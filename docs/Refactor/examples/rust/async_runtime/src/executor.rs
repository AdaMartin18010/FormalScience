//! # 执行器实现
//! 
//! 实现一个简单的异步任务执行器

use std::future::Future;
use std::pin::Pin;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{channel, Sender};
use std::sync::{Arc, Mutex};
use std::task::{Context, Poll};

use crate::task::{Task, TaskId, TaskQueue, TaskWaker};

/// 任务执行器
pub struct Executor {
    queue: Arc<Mutex<TaskQueue>>,
    sender: Sender<TaskId>,
    shutdown: AtomicBool,
}

impl Executor {
    pub fn new() -> Self {
        let (sender, _receiver) = channel::<TaskId>();
        Self {
            queue: Arc::new(Mutex::new(TaskQueue::new())),
            sender,
            shutdown: AtomicBool::new(false),
        }
    }
    
    /// 提交一个新任务
    pub fn spawn<F>(&self, future: F) -> TaskId
    where
        F: Future<Output = ()> + Send + 'static,
    {
        let task = Task::new(future);
        let id = task.id();
        
        let mut queue = self.queue.lock().unwrap();
        queue.push(task);
        
        id
    }
    
    /// 运行执行器直到所有任务完成
    pub fn run(&self) {
        while !self.shutdown.load(Ordering::SeqCst) {
            if let Some(mut task) = {
                let mut queue = self.queue.lock().unwrap();
                queue.pop()
            } {
                // 创建 waker
                let waker = TaskWaker::new(task.id()).into();
                let mut context = Context::from_waker(&waker);
                
                // 轮询任务
                match task.poll(&mut context) {
                    Poll::Ready(()) => {
                        // 任务完成
                    }
                    Poll::Pending => {
                        // 任务阻塞，放回队列
                        let mut queue = self.queue.lock().unwrap();
                        queue.push(task);
                    }
                }
            } else {
                // 没有就绪的任务
                let queue = self.queue.lock().unwrap();
                if queue.is_empty() {
                    break;
                }
                // 等待一段时间再检查
                std::thread::yield_now();
            }
            
            // 清理已完成的任务
            let mut queue = self.queue.lock().unwrap();
            queue.cleanup_completed();
        }
    }
    
    /// 运行一次轮询循环
    pub fn run_once(&self) -> bool {
        let mut progress = false;
        
        while let Some(mut task) = {
            let mut queue = self.queue.lock().unwrap();
            queue.pop()
        } {
            progress = true;
            
            let waker = TaskWaker::new(task.id()).into();
            let mut context = Context::from_waker(&waker);
            
            match task.poll(&mut context) {
                Poll::Ready(()) => {}
                Poll::Pending => {
                    let mut queue = self.queue.lock().unwrap();
                    queue.push(task);
                }
            }
        }
        
        progress
    }
    
    /// 请求关闭
    pub fn shutdown(&self) {
        self.shutdown.store(true, Ordering::SeqCst);
    }
    
    /// 唤醒任务
    pub fn wake(&self, task_id: TaskId) {
        let mut queue = self.queue.lock().unwrap();
        queue.mark_ready(task_id);
        let _ = self.sender.send(task_id);
    }
}

impl Default for Executor {
    fn default() -> Self {
        Self::new()
    }
}

/// 块级执行器
pub fn block_on<F>(future: F) -> F::Output
where
    F: Future,
{
    use std::sync::Arc;
    use std::task::Wake;

    struct DummyWaker;
    
    impl Wake for DummyWaker {
        fn wake(self: Arc<Self>) {}
        fn wake_by_ref(self: &Arc<Self>) {}
    }
    
    let waker = Arc::new(DummyWaker).into();
    let mut context = Context::from_waker(&waker);
    
    let mut future = std::pin::pin!(future);
    
    loop {
        match future.as_mut().poll(&mut context) {
            Poll::Ready(result) => return result,
            Poll::Pending => {
                std::thread::yield_now();
            }
        }
    }
}

/// 本地执行器（单线程）
pub struct LocalExecutor {
    tasks: Vec<LocalTask>,
}

struct LocalTask {
    id: TaskId,
    future: Pin<Box<dyn Future<Output = ()>>>,
}

impl LocalExecutor {
    pub fn new() -> Self {
        Self { tasks: Vec::new() }
    }
    
    pub fn spawn_local<F>(&mut self, future: F) -> TaskId
    where
        F: Future<Output = ()> + 'static,
    {
        let id = TaskId::new();
        self.tasks.push(LocalTask {
            id,
            future: Box::pin(future),
        });
        id
    }
    
    pub fn run(&mut self) {
        use std::task::Wake;
        
        struct LocalWaker;
        
        impl Wake for LocalWaker {
            fn wake(self: Arc<Self>) {}
            fn wake_by_ref(self: &Arc<Self>) {}
        }
        
        let waker = Arc::new(LocalWaker).into();
        let mut context = Context::from_waker(&waker);
        
        let mut completed = Vec::new();
        
        loop {
            let mut progress = false;
            
            for (i, task) in self.tasks.iter_mut().enumerate() {
                if completed.contains(&i) {
                    continue;
                }
                
                match task.future.as_mut().poll(&mut context) {
                    Poll::Ready(()) => {
                        completed.push(i);
                        progress = true;
                    }
                    Poll::Pending => {}
                }
            }
            
            if !progress {
                break;
            }
        }
        
        // 移除已完成的任务
        for i in completed.into_iter().rev() {
            self.tasks.remove(i);
        }
    }
}

impl Default for LocalExecutor {
    fn default() -> Self {
        Self::new()
    }
}

/// 多线程执行器
pub struct ThreadPoolExecutor {
    workers: Vec<std::thread::JoinHandle<()>>,
    sender: Sender<TaskId>,
    queue: Arc<Mutex<TaskQueue>>,
}

impl ThreadPoolExecutor {
    pub fn new(num_threads: usize) -> Self {
        let (sender, receiver) = channel::<TaskId>();
        let receiver = Arc::new(Mutex::new(receiver));
        let queue = Arc::new(Mutex::new(TaskQueue::new()));
        
        let mut workers = Vec::with_capacity(num_threads);
        
        for _ in 0..num_threads {
            let queue = Arc::clone(&queue);
            let receiver = Arc::clone(&receiver);
            
            let handle = std::thread::spawn(move || {
                loop {
                    // 等待任务通知
                    let _ = receiver.lock().unwrap().recv();
                    
                    // 执行任务
                    if let Some(mut task) = {
                        let mut q = queue.lock().unwrap();
                        q.pop()
                    } {
                        let waker = TaskWaker::new(task.id()).into();
                        let mut context = Context::from_waker(&waker);
                        
                        if task.poll(&mut context).is_pending() {
                            let mut q = queue.lock().unwrap();
                            q.push(task);
                        }
                    }
                }
            });
            
            workers.push(handle);
        }
        
        Self {
            workers,
            sender,
            queue,
        }
    }
    
    pub fn spawn<F>(&self, future: F) -> TaskId
    where
        F: Future<Output = ()> + Send + 'static,
    {
        let task = Task::new(future);
        let id = task.id();
        
        let mut queue = self.queue.lock().unwrap();
        queue.push(task);
        
        // 通知工作线程
        let _ = self.sender.send(id);
        
        id
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_executor_spawn() {
        let executor = Executor::new();
        
        let task_id = executor.spawn(async {
            println!("Hello from async task!");
        });
        
        assert_ne!(task_id, TaskId::default());
    }
    
    #[test]
    fn test_block_on() {
        let result = block_on(async {
            let x = 10;
            let y = 20;
            x + y
        });
        
        assert_eq!(result, 30);
    }
    
    #[test]
    fn test_local_executor() {
        let mut executor = LocalExecutor::new();
        
        executor.spawn_local(async {
            println!("Local task 1");
        });
        
        executor.spawn_local(async {
            println!("Local task 2");
        });
        
        executor.run();
    }
}
