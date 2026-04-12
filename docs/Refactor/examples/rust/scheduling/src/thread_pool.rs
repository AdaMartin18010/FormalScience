//! # 线程池实现
//! 
//! 一个功能完整的线程池，支持各种调度策略

use std::sync::{mpsc, Arc, Mutex};
use std::thread;

/// 任务类型
pub type Task = Box<dyn FnOnce() + Send + 'static>;

/// 线程池消息
enum Message {
    NewTask(Task),
    Terminate,
}

/// 线程池
pub struct ThreadPool {
    workers: Vec<Worker>,
    sender: Option<mpsc::Sender<Message>>,
}

impl ThreadPool {
    /// 创建一个新的线程池
    /// 
    /// # Panics
    /// 
    /// 当 size 为 0 时 panic
    pub fn new(size: usize) -> Self {
        assert!(size > 0);
        
        let (sender, receiver) = mpsc::channel();
        let receiver = Arc::new(Mutex::new(receiver));
        
        let mut workers = Vec::with_capacity(size);
        
        for id in 0..size {
            workers.push(Worker::new(id, Arc::clone(&receiver)));
        }
        
        ThreadPool {
            workers,
            sender: Some(sender),
        }
    }
    
    /// 创建具有特定配置的线程池
    pub fn builder() -> ThreadPoolBuilder {
        ThreadPoolBuilder::new()
    }
    
    /// 执行任务
    pub fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        let task = Box::new(f);
        if let Some(sender) = &self.sender {
            sender.send(Message::NewTask(task)).unwrap();
        }
    }
    
    /// 获取线程数
    pub fn num_threads(&self) -> usize {
        self.workers.len()
    }
}

impl Drop for ThreadPool {
    fn drop(&mut self) {
        // 发送终止消息
        drop(self.sender.take());
        
        // 等待所有工作线程完成
        for worker in &mut self.workers {
            if let Some(thread) = worker.thread.take() {
                thread.join().unwrap();
            }
        }
    }
}

/// 线程池构建器
pub struct ThreadPoolBuilder {
    size: Option<usize>,
    stack_size: Option<usize>,
    name_prefix: Option<String>,
}

impl ThreadPoolBuilder {
    fn new() -> Self {
        Self {
            size: None,
            stack_size: None,
            name_prefix: None,
        }
    }
    
    /// 设置线程数
    pub fn size(mut self, size: usize) -> Self {
        self.size = Some(size);
        self
    }
    
    /// 设置栈大小
    pub fn stack_size(mut self, size: usize) -> Self {
        self.stack_size = Some(size);
        self
    }
    
    /// 设置线程名前缀
    pub fn name_prefix(mut self, prefix: impl Into<String>) -> Self {
        self.name_prefix = Some(prefix.into());
        self
    }
    
    /// 构建线程池
    pub fn build(self) -> ThreadPool {
        let size = self.size.unwrap_or_else(num_cpus::get);
        
        let (sender, receiver) = mpsc::channel();
        let receiver = Arc::new(Mutex::new(receiver));
        
        let mut workers = Vec::with_capacity(size);
        
        for id in 0..size {
            let name = self.name_prefix.as_ref()
                .map(|p| format!("{}-{}", p, id));
            
            workers.push(Worker::new_with_config(
                id,
                Arc::clone(&receiver),
                name,
                self.stack_size,
            ));
        }
        
        ThreadPool {
            workers,
            sender: Some(sender),
        }
    }
}

/// 工作线程
struct Worker {
    id: usize,
    thread: Option<thread::JoinHandle<()>>,
}

impl Worker {
    fn new(id: usize, receiver: Arc<Mutex<mpsc::Receiver<Message>>>) -> Self {
        Self::new_with_config(id, receiver, None, None)
    }
    
    fn new_with_config(
        id: usize,
        receiver: Arc<Mutex<mpsc::Receiver<Message>>>,
        name: Option<String>,
        stack_size: Option<usize>,
    ) -> Self {
        let thread = thread::Builder::new()
            .name(name.unwrap_or_else(|| format!("worker-{}", id)))
            .stack_size(stack_size.unwrap_or(2 * 1024 * 1024))
            .spawn(move || loop {
                let message = receiver.lock().unwrap().recv();
                
                match message {
                    Ok(Message::NewTask(task)) => {
                        task();
                    }
                    Ok(Message::Terminate) | Err(_) => {
                        break;
                    }
                }
            })
            .unwrap();
        
        Worker {
            id,
            thread: Some(thread),
        }
    }
}

/// 作用域线程池
pub struct ScopedThreadPool<'scope> {
    scope: &'scope thread::Scope<'scope, 'scope>,
    num_threads: usize,
}

impl<'scope> ScopedThreadPool<'scope> {
    pub fn new(num_threads: usize, scope: &'scope thread::Scope<'scope, 'scope>) -> Self {
        Self { scope, num_threads }
    }
    
    pub fn spawn<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'scope,
    {
        // 简化的实现，实际应该使用工作窃取队列
        self.scope.spawn(f);
    }
}

/// 异步任务线程池
pub struct AsyncThreadPool {
    pool: ThreadPool,
}

impl AsyncThreadPool {
    pub fn new(size: usize) -> Self {
        Self {
            pool: ThreadPool::new(size),
        }
    }
    
    /// 提交异步任务
    pub fn spawn<F, T>(&self, f: F) -> TaskHandle<T>
    where
        F: FnOnce() -> T + Send + 'static,
        T: Send + 'static,
    {
        let (sender, receiver) = mpsc::channel();
        
        self.pool.execute(move || {
            let result = f();
            let _ = sender.send(result);
        });
        
        TaskHandle { receiver }
    }
}

/// 任务句柄
pub struct TaskHandle<T> {
    receiver: mpsc::Receiver<T>,
}

impl<T> TaskHandle<T> {
    pub fn join(self) -> Result<T, mpsc::RecvError> {
        self.receiver.recv()
    }
    
    pub fn try_join(&self) -> Result<T, mpsc::TryRecvError> {
        self.receiver.try_recv()
    }
    
    pub fn join_timeout(&self, timeout: std::time::Duration) -> Result<T, mpsc::RecvTimeoutError> {
        self.receiver.recv_timeout(timeout)
    }
}

/// CPU 核心数
mod num_cpus {
    pub fn get() -> usize {
        std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1)
    }
}

/// 并行映射
pub fn parallel_map<T, R, F>(input: Vec<T>, f: F, num_threads: usize) -> Vec<R>
where
    T: Send + 'static,
    R: Send + 'static,
    F: Fn(T) -> R + Send + Sync + 'static,
{
    let pool = ThreadPool::new(num_threads);
    let f = Arc::new(f);
    
    let mut handles = Vec::with_capacity(input.len());
    
    for item in input {
        let f = Arc::clone(&f);
        let (sender, receiver) = mpsc::channel();
        
        pool.execute(move || {
            let result = f(item);
            let _ = sender.send(result);
        });
        
        handles.push(receiver);
    }
    
    drop(pool);
    
    handles.into_iter().map(|r| r.recv().unwrap()).collect()
}

/// 并行 for 循环
pub fn parallel_for<F>(range: std::ops::Range<usize>, f: F, num_threads: usize)
where
    F: Fn(usize) + Send + Sync + 'static,
{
    let pool = ThreadPool::new(num_threads);
    let f = Arc::new(f);
    
    for i in range {
        let f = Arc::clone(&f);
        pool.execute(move || f(i));
    }
    
    drop(pool);
}

/// 带结果收集的并行 for
pub fn parallel_for_collect<F, R>(range: std::ops::Range<usize>, f: F, num_threads: usize) -> Vec<R>
where
    F: Fn(usize) -> R + Send + Sync + 'static,
    R: Send + 'static,
{
    let pool = ThreadPool::new(num_threads);
    let f = Arc::new(f);
    
    let mut handles = Vec::with_capacity(range.len());
    
    for i in range {
        let f = Arc::clone(&f);
        let (sender, receiver) = mpsc::channel();
        
        pool.execute(move || {
            let result = f(i);
            let _ = sender.send(result);
        });
        
        handles.push(receiver);
    }
    
    drop(pool);
    
    handles.into_iter().map(|r| r.recv().unwrap()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::time::Duration;
    
    #[test]
    fn test_thread_pool() {
        let pool = ThreadPool::new(4);
        let counter = Arc::new(AtomicUsize::new(0));
        
        for _ in 0..10 {
            let c = Arc::clone(&counter);
            pool.execute(move || {
                c.fetch_add(1, Ordering::SeqCst);
            });
        }
        
        // 等待任务完成
        std::thread::sleep(Duration::from_millis(100));
        
        assert!(counter.load(Ordering::SeqCst) >= 10);
    }
    
    #[test]
    fn test_thread_pool_builder() {
        let pool = ThreadPool::builder()
            .size(2)
            .name_prefix("worker")
            .build();
        
        assert_eq!(pool.num_threads(), 2);
        
        pool.execute(|| {
            println!("Hello from worker!");
        });
    }
    
    #[test]
    fn test_async_thread_pool() {
        let pool = AsyncThreadPool::new(2);
        
        let handle = pool.spawn(|| {
            42
        });
        
        let result = handle.join().unwrap();
        assert_eq!(result, 42);
    }
    
    #[test]
    fn test_parallel_map() {
        let input: Vec<i32> = (0..100).collect();
        let output: Vec<i32> = parallel_map(input, |x| x * x, 4);
        
        assert_eq!(output.len(), 100);
        assert_eq!(output[10], 100);
        assert_eq!(output[99], 9801);
    }
    
    #[test]
    fn test_parallel_for() {
        let counter = Arc::new(AtomicUsize::new(0));
        
        parallel_for(0..100, {
            let c = Arc::clone(&counter);
            move |_| {
                c.fetch_add(1, Ordering::SeqCst);
            }
        }, 4);
        
        // parallel_for 会等待所有任务完成
        assert_eq!(counter.load(Ordering::SeqCst), 100);
    }
    
    #[test]
    fn test_parallel_for_collect() {
        let results: Vec<usize> = parallel_for_collect(0..10, |i| i * i, 4);
        
        assert_eq!(results.len(), 10);
        assert_eq!(results[5], 25);
    }
}
