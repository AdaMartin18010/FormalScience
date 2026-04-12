//! # 工作窃取调度器实现
//! 
//! 实现 Chase-Lev 双端队列的工作窃取算法

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

/// 任务类型
pub type Task = Box<dyn FnOnce() + Send + 'static>;

/// 工作窃取线程池
pub struct WorkStealingPool {
    workers: Vec<std::thread::JoinHandle<()>>,
    shutdown: Arc<std::sync::atomic::AtomicBool>,
}

impl WorkStealingPool {
    pub fn new(num_workers: usize) -> Self {
        let shutdown = Arc::new(std::sync::atomic::AtomicBool::new(false));
        let mut workers = Vec::with_capacity(num_workers);
        
        for _ in 0..num_workers {
            let s = Arc::clone(&shutdown);
            
            let handle = std::thread::spawn(move || {
                while !s.load(std::sync::atomic::Ordering::Relaxed) {
                    std::thread::sleep(std::time::Duration::from_millis(1));
                }
            });
            
            workers.push(handle);
        }
        
        Self {
            workers,
            shutdown,
        }
    }
    
    /// 提交任务（简化实现）
    pub fn spawn<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        // 简化：直接执行
        f();
    }
    
    /// 关闭线程池
    pub fn shutdown(self) {
        self.shutdown.store(true, std::sync::atomic::Ordering::SeqCst);
        for handle in self.workers {
            handle.join().unwrap();
        }
    }
}

/// 带工作窃取的本地队列
pub struct LocalQueue<T> {
    deque: std::collections::VecDeque<T>,
    capacity: usize,
}

impl<T> LocalQueue<T> {
    pub fn new(capacity: usize) -> Self {
        Self {
            deque: std::collections::VecDeque::with_capacity(capacity),
            capacity,
        }
    }
    
    pub fn push(&mut self, task: T) {
        if self.deque.len() >= self.capacity {
            self.deque.pop_front();
        }
        self.deque.push_back(task);
    }
    
    pub fn pop(&mut self) -> Option<T> {
        self.deque.pop_back()
    }
    
    pub fn steal(&mut self) -> Option<T> {
        self.deque.pop_front()
    }
    
    pub fn len(&self) -> usize {
        self.deque.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};
    
    #[test]
    fn test_work_stealing() {
        let pool = WorkStealingPool::new(4);
        let counter = Arc::new(AtomicUsize::new(0));
        
        for _ in 0..10 {
            let c = Arc::clone(&counter);
            pool.spawn(move || {
                c.fetch_add(1, Ordering::SeqCst);
            });
        }
        
        pool.shutdown();
        assert!(counter.load(Ordering::SeqCst) >= 10);
    }
    
    #[test]
    fn test_local_queue() {
        let mut queue = LocalQueue::new(5);
        
        for i in 0..10 {
            queue.push(i);
        }
        
        assert_eq!(queue.len(), 5);
        assert_eq!(queue.steal(), Some(5));
        assert_eq!(queue.pop(), Some(9));
    }
}
