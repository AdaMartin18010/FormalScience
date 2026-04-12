//! # 多级反馈队列 (MLFQ) 调度器
//! 
//! 实现多级反馈队列调度算法

use std::collections::VecDeque;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

/// 队列数量
pub const DEFAULT_NUM_QUEUES: usize = 4;

/// 基础时间片
pub const DEFAULT_BASE_TIME_SLICE: Duration = Duration::from_millis(10);

/// 任务 ID
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TaskId(pub u64);

impl TaskId {
    pub fn new() -> Self {
        use std::sync::atomic::{AtomicU64, Ordering};
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        TaskId(COUNTER.fetch_add(1, Ordering::SeqCst))
    }
}

impl Default for TaskId {
    fn default() -> Self {
        Self::new()
    }
}

/// MLFQ 调度器
pub struct MlfqScheduler {
    queues: Arc<Mutex<Vec<VecDeque<Task>>>>,
    num_queues: usize,
    threads: Vec<thread::JoinHandle<()>>,
    shutdown: Arc<std::sync::atomic::AtomicBool>,
}

type Task = Box<dyn FnOnce() + Send + 'static>;

impl MlfqScheduler {
    pub fn new(num_threads: usize, num_queues: usize) -> Self {
        let mut queues_vec: Vec<VecDeque<Task>> = Vec::with_capacity(num_queues);
        for _ in 0..num_queues {
            queues_vec.push(VecDeque::new());
        }
        
        let queues = Arc::new(Mutex::new(queues_vec));
        let shutdown = Arc::new(std::sync::atomic::AtomicBool::new(false));
        
        let mut threads = Vec::with_capacity(num_threads);
        
        for _ in 0..num_threads {
            let q = Arc::clone(&queues);
            let s = Arc::clone(&shutdown);
            
            let handle = thread::spawn(move || {
                loop {
                    if s.load(std::sync::atomic::Ordering::Relaxed) {
                        let qs = q.lock().unwrap();
                        if qs.iter().all(|queue| queue.is_empty()) {
                            break;
                        }
                    }
                    
                    let task = {
                        let mut qs = q.lock().unwrap();
                        let mut found_task = None;
                        
                        for queue in qs.iter_mut() {
                            if let Some(task) = queue.pop_front() {
                                found_task = Some(task);
                                break;
                            }
                        }
                        found_task
                    };
                    
                    if let Some(task) = task {
                        task();
                    } else {
                        thread::sleep(Duration::from_millis(1));
                    }
                }
            });
            
            threads.push(handle);
        }
        
        Self {
            queues,
            num_queues,
            threads,
            shutdown,
        }
    }
    
    /// 提交任务
    pub fn spawn<F>(&self, task: F) -> TaskId
    where
        F: FnOnce() + Send + 'static,
    {
        let id = TaskId::new();
        
        let mut qs = self.queues.lock().unwrap();
        qs[0].push_back(Box::new(task));
        drop(qs);
        
        id
    }
    
    /// 提交批处理任务（低优先级）
    pub fn spawn_batch<F>(&self, task: F) -> TaskId
    where
        F: FnOnce() + Send + 'static,
    {
        let id = TaskId::new();
        let level = self.num_queues - 1;
        
        let mut qs = self.queues.lock().unwrap();
        qs[level].push_back(Box::new(task));
        drop(qs);
        
        id
    }
    
    /// 获取队列长度信息
    pub fn queue_lengths(&self) -> Vec<usize> {
        let qs = self.queues.lock().unwrap();
        qs.iter().map(|q| q.len()).collect()
    }
    
    /// 关闭调度器
    pub fn shutdown(self) {
        self.shutdown.store(true, std::sync::atomic::Ordering::SeqCst);
        for handle in self.threads {
            handle.join().unwrap();
        }
    }
}

/// 简化的 MLFQ（单线程版本）
pub struct SimpleMlfq {
    queues: Vec<VecDeque<Box<dyn FnOnce()>>>,
}

impl SimpleMlfq {
    pub fn new(num_queues: usize) -> Self {
        let mut queues = Vec::with_capacity(num_queues);
        for _ in 0..num_queues {
            queues.push(VecDeque::new());
        }
        
        Self {
            queues,
        }
    }
    
    pub fn push<F>(&mut self, task: F)
    where
        F: FnOnce() + 'static,
    {
        self.queues[0].push_back(Box::new(task));
    }
    
    pub fn run(&mut self) {
        loop {
            let mut task_executed = false;
            
            for queue in &mut self.queues {
                if let Some(task) = queue.pop_front() {
                    task();
                    task_executed = true;
                    break;
                }
            }
            
            if !task_executed {
                break;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};
    
    #[test]
    fn test_mlfq_scheduler() {
        let scheduler = MlfqScheduler::new(2, 4);
        let counter = Arc::new(AtomicUsize::new(0));
        
        for _ in 0..10 {
            let c = Arc::clone(&counter);
            scheduler.spawn(move || {
                c.fetch_add(1, Ordering::SeqCst);
            });
        }
        
        std::thread::sleep(Duration::from_millis(100));
        
        scheduler.shutdown();
        
        assert!(counter.load(Ordering::SeqCst) >= 10);
    }
    
    #[test]
    fn test_simple_mlfq() {
        let mut scheduler = SimpleMlfq::new(3);
        
        scheduler.push(|| {
            println!("Task 1");
        });
        
        scheduler.push(|| {
            println!("Task 2");
        });
        
        scheduler.run();
    }
}
