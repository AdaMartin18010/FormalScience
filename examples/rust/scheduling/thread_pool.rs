/// 线程池实现
/// 
/// 线程池是一种任务调度技术，通过维护一组工作线程来执行提交的任务，
/// 避免了频繁创建和销毁线程的开销。

use std::sync::{mpsc, Arc, Mutex};
use std::thread;
use std::time::Duration;

/// 任务类型：Box<dyn FnOnce() + Send + 'static>
/// 表示一个可以在线程间安全传递的一次性闭包
type Job = Box<dyn FnOnce() + Send + 'static>;

/// 线程池消息枚举
enum Message {
    /// 执行新任务
    NewJob(Job),
    /// 终止工作线程
    Terminate,
}

/// 工作线程结构
struct Worker {
    /// 线程ID
    id: usize,
    /// 线程句柄（Option 用于 take 所有权）
    thread: Option<thread::JoinHandle<()>>,
}

impl Worker {
    /// 创建新工作线程
    fn new(id: usize, receiver: Arc<Mutex<mpsc::Receiver<Message>>>) -> Self {
        let thread = thread::spawn(move || {
            println!("工作线程 {} 启动", id);
            
            loop {
                // 获取锁并接收消息
                let message = receiver.lock().unwrap().recv();
                
                match message {
                    Ok(Message::NewJob(job)) => {
                        println!("工作线程 {} 执行任务", id);
                        job();
                    }
                    Ok(Message::Terminate) => {
                        println!("工作线程 {} 收到终止信号", id);
                        break;
                    }
                    Err(_) => {
                        println!("工作线程 {}: 发送端已关闭", id);
                        break;
                    }
                }
            }
            
            println!("工作线程 {} 退出", id);
        });

        Self {
            id,
            thread: Some(thread),
        }
    }
}

/// 线程池结构
pub struct ThreadPool {
    /// 工作线程集合
    workers: Vec<Worker>,
    /// 任务发送通道
    sender: mpsc::Sender<Message>,
    /// 线程池大小
    size: usize,
}

impl ThreadPool {
    /// 创建指定大小的线程池
    /// 
    /// # Arguments
    /// * `size` - 线程池中的工作线程数量
    /// 
    /// # Panics
    /// 当 size 为 0 时 panic
    pub fn new(size: usize) -> Self {
        assert!(size > 0, "线程池大小必须大于 0");

        // 创建任务通道
        let (sender, receiver) = mpsc::channel();
        
        // 使用 Arc<Mutex<>> 在线程间共享接收端
        let receiver = Arc::new(Mutex::new(receiver));
        
        // 创建工作线程
        let mut workers = Vec::with_capacity(size);
        for id in 0..size {
            workers.push(Worker::new(id, Arc::clone(&receiver)));
        }

        Self {
            workers,
            sender,
            size,
        }
    }

    /// 创建根据CPU核心数自动调整大小的线程池
    pub fn with_default_size() -> Self {
        let size = thread::available_parallelism()
            .map(|p| p.get())
            .unwrap_or(4);
        Self::new(size)
    }

    /// 提交任务到线程池
    /// 
    /// # Arguments
    /// * `f` - 要执行的任务闭包
    pub fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        let job = Box::new(f);
        self.sender.send(Message::NewJob(job)).unwrap();
    }

    /// 获取线程池大小
    pub fn size(&self) -> usize {
        self.size
    }
}

impl Drop for ThreadPool {
    fn drop(&mut self) {
        println!("\n正在关闭线程池...");
        
        // 向所有工作线程发送终止信号
        for _ in &self.workers {
            self.sender.send(Message::Terminate).unwrap();
        }
        
        // 等待所有工作线程完成
        for worker in &mut self.workers {
            if let Some(thread) = worker.thread.take() {
                thread.join().unwrap();
            }
        }
        
        println!("线程池已关闭");
    }
}

/// 带任务统计的增强型线程池
pub struct InstrumentedThreadPool {
    inner: ThreadPool,
    task_count: Arc<Mutex<usize>>,
}

impl InstrumentedThreadPool {
    pub fn new(size: usize) -> Self {
        Self {
            inner: ThreadPool::new(size),
            task_count: Arc::new(Mutex::new(0)),
        }
    }

    pub fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        let counter = Arc::clone(&self.task_count);
        
        self.inner.execute(move || {
            f();
            let mut count = counter.lock().unwrap();
            *count += 1;
        });
    }

    pub fn completed_tasks(&self) -> usize {
        *self.task_count.lock().unwrap()
    }
}

/// 工作窃取线程池（简化实现）
/// 
/// 每个工作线程有自己的任务队列，可以从其他线程窃取任务
pub mod work_stealing {
    use std::collections::VecDeque;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::{Arc, Mutex};
    use std::thread;

    type Task = Box<dyn FnOnce() + Send + 'static>;

    /// 任务队列
    pub struct TaskQueue {
        queue: Mutex<VecDeque<Task>>,
    }

    impl TaskQueue {
        pub fn new() -> Self {
            Self {
                queue: Mutex::new(VecDeque::new()),
            }
        }

        /// 添加任务到队列尾部
        pub fn push(&self, task: Task) {
            self.queue.lock().unwrap().push_back(task);
        }

        /// 从队列头部获取任务（本地线程）
        pub fn pop(&self) -> Option<Task> {
            self.queue.lock().unwrap().pop_front()
        }

        /// 从队列尾部窃取任务（其他线程）
        pub fn steal(&self) -> Option<Task> {
            self.queue.lock().unwrap().pop_back()
        }

        /// 检查队列是否为空
        pub fn is_empty(&self) -> bool {
            self.queue.lock().unwrap().is_empty()
        }
    }

    /// 工作窃取线程池
    pub struct WorkStealingPool {
        /// 每个线程的任务队列
        queues: Vec<Arc<TaskQueue>>,
        /// 线程句柄
        threads: Vec<thread::JoinHandle<()>>,
        /// 全局任务计数
        task_count: Arc<AtomicUsize>,
    }

    impl WorkStealingPool {
        pub fn new(size: usize) -> Self {
            let mut queues: Vec<Arc<TaskQueue>> = Vec::with_capacity(size);
            for _ in 0..size {
                queues.push(Arc::new(TaskQueue::new()));
            }

            let task_count = Arc::new(AtomicUsize::new(0));
            let mut threads = Vec::with_capacity(size);

            for id in 0..size {
                let local_queue = Arc::clone(&queues[id]);
                let all_queues = queues.clone();
                let counter = Arc::clone(&task_count);

                let thread = thread::spawn(move || {
                    println!("工作窃取线程 {} 启动", id);

                    loop {
                        // 先尝试从本地队列获取任务
                        let task = local_queue.pop()
                            // 如果本地队列为空，尝试从其他队列窃取
                            .or_else(|| Self::steal_from_others(&all_queues, id));

                        if let Some(task) = task {
                            task();
                            counter.fetch_add(1, Ordering::Relaxed);
                        } else {
                            // 没有任务，短暂休眠
                            thread::sleep(std::time::Duration::from_millis(1));
                        }
                    }
                });

                threads.push(thread);
            }

            Self {
                queues,
                threads,
                task_count,
            }
        }

        /// 从其他队列窃取任务
        fn steal_from_others(queues: &[Arc<TaskQueue>], my_id: usize) -> Option<Task> {
            for (i, queue) in queues.iter().enumerate() {
                if i != my_id {
                    if let Some(task) = queue.steal() {
                        println!("线程 {} 从线程 {} 窃取任务", my_id, i);
                        return Some(task);
                    }
                }
            }
            None
        }

        /// 提交任务（轮询选择队列）
        pub fn submit<F>(&self, f: F)
        where
            F: FnOnce() + Send + 'static,
        {
            static COUNTER: AtomicUsize = AtomicUsize::new(0);
            let idx = COUNTER.fetch_add(1, Ordering::Relaxed) % self.queues.len();
            self.queues[idx].push(Box::new(f));
        }

        pub fn task_count(&self) -> usize {
            self.task_count.load(Ordering::Relaxed)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_thread_pool_basic() {
        let pool = ThreadPool::new(4);
        
        let counter = Arc::new(Mutex::new(0));
        for _ in 0..10 {
            let counter = Arc::clone(&counter);
            pool.execute(move || {
                let mut num = counter.lock().unwrap();
                *num += 1;
            });
        }

        // 等待任务完成
        thread::sleep(Duration::from_millis(100));
        
        assert_eq!(*counter.lock().unwrap(), 10);
    }

    #[test]
    fn test_thread_pool_size() {
        let pool = ThreadPool::new(8);
        assert_eq!(pool.size(), 8);
    }

    #[test]
    fn test_instrumented_pool() {
        let pool = InstrumentedThreadPool::new(2);
        
        for i in 0..5 {
            pool.execute(move || {
                println!("执行任务 {}", i);
            });
        }

        thread::sleep(Duration::from_millis(100));
        assert!(pool.completed_tasks() > 0);
    }
}

fn main() {
    println!("=== 基础线程池示例 ===");
    {
        let pool = ThreadPool::new(4);
        
        for i in 0..8 {
            pool.execute(move || {
                println!("任务 {} 开始执行", i);
                thread::sleep(Duration::from_millis(100));
                println!("任务 {} 完成", i);
            });
        }

        // 等待任务完成
        thread::sleep(Duration::from_millis(500));
    }

    println!("\n=== 带统计的线程池示例 ===");
    {
        let pool = InstrumentedThreadPool::new(2);
        
        for i in 0..10 {
            pool.execute(move || {
                thread::sleep(Duration::from_millis(50));
            });
        }

        thread::sleep(Duration::from_millis(500));
        println!("完成任务数: {}", pool.completed_tasks());
    }

    println!("\n=== 工作窃取线程池示例 ===");
    {
        use work_stealing::WorkStealingPool;
        
        let pool = WorkStealingPool::new(4);
        
        for i in 0..20 {
            pool.submit(move || {
                println!("窃取池任务 {} 执行", i);
                thread::sleep(Duration::from_millis(50));
            });
        }

        thread::sleep(Duration::from_millis(500));
        println!("窃取池任务数: {}", pool.task_count());
    }
}
