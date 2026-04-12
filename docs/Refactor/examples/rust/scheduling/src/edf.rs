//! # EDF (Earliest Deadline First) 调度器
//! 
//! 实现实时调度算法 EDF

use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::sync::{Arc, Condvar, Mutex};
use std::thread;
use std::time::{Duration, Instant};

/// 截止时间
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Deadline(pub Instant);

impl Deadline {
    pub fn from_now(duration: Duration) -> Self {
        Deadline(Instant::now() + duration)
    }
    
    pub fn is_expired(&self) -> bool {
        Instant::now() >= self.0
    }
}

impl Ord for Deadline {
    fn cmp(&self, other: &Self) -> Ordering {
        other.0.cmp(&self.0)
    }
}

impl PartialOrd for Deadline {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

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

/// 实时任务
pub struct RealtimeTask {
    pub id: TaskId,
    pub deadline: Deadline,
    pub task: Box<dyn FnOnce() + Send>,
    pub is_hard: bool,
}

impl RealtimeTask {
    pub fn new<F>(deadline: Deadline, task: F, is_hard: bool) -> Self
    where
        F: FnOnce() + Send + 'static,
    {
        Self {
            id: TaskId::new(),
            deadline,
            task: Box::new(task),
            is_hard,
        }
    }
    
    pub fn execute(self) {
        (self.task)();
    }
}

impl Ord for RealtimeTask {
    fn cmp(&self, other: &Self) -> Ordering {
        self.deadline.cmp(&other.deadline)
            .then_with(|| self.id.0.cmp(&other.id.0))
    }
}

impl PartialOrd for RealtimeTask {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for RealtimeTask {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for RealtimeTask {}

/// EDF 调度器
pub struct EdfScheduler {
    queue: Arc<(Mutex<BinaryHeap<RealtimeTask>>, Condvar)>,
    threads: Vec<thread::JoinHandle<()>>,
    shutdown: Arc<std::sync::atomic::AtomicBool>,
}

impl EdfScheduler {
    pub fn new(num_threads: usize) -> Self {
        let queue = Arc::new((Mutex::new(BinaryHeap::new()), Condvar::new()));
        let shutdown = Arc::new(std::sync::atomic::AtomicBool::new(false));
        
        let mut threads = Vec::with_capacity(num_threads);
        
        for _ in 0..num_threads {
            let q = Arc::clone(&queue);
            let s = Arc::clone(&shutdown);
            
            let handle = thread::spawn(move || {
                Self::worker_loop(q, s);
            });
            
            threads.push(handle);
        }
        
        Self {
            queue,
            threads,
            shutdown,
        }
    }
    
    fn worker_loop(
        queue: Arc<(Mutex<BinaryHeap<RealtimeTask>>, Condvar)>,
        shutdown: Arc<std::sync::atomic::AtomicBool>,
    ) {
        let (lock, cvar) = &*queue;
        
        loop {
            let task = {
                let mut heap = lock.lock().unwrap();
                
                loop {
                    if shutdown.load(std::sync::atomic::Ordering::Relaxed) && heap.is_empty() {
                        return;
                    }
                    
                    if let Some(task) = heap.peek() {
                        if task.deadline.is_expired() {
                            let _expired = heap.pop().unwrap();
                            continue;
                        }
                        break heap.pop();
                    } else {
                        heap = cvar.wait(heap).unwrap();
                    }
                }
            };
            
            if let Some(task) = task {
                if !task.deadline.is_expired() {
                    task.execute();
                }
            }
        }
    }
    
    /// 提交软实时任务
    pub fn spawn_soft<F>(&self, deadline: Deadline, task: F) -> TaskId
    where
        F: FnOnce() + Send + 'static,
    {
        self.spawn(deadline, task, false)
    }
    
    /// 提交硬实时任务
    pub fn spawn_hard<F>(&self, deadline: Deadline, task: F) -> TaskId
    where
        F: FnOnce() + Send + 'static,
    {
        self.spawn(deadline, task, true)
    }
    
    fn spawn<F>(&self, deadline: Deadline, task: F, is_hard: bool) -> TaskId
    where
        F: FnOnce() + Send + 'static,
    {
        let task = RealtimeTask::new(deadline, task, is_hard);
        let id = task.id;
        
        let (lock, cvar) = &*self.queue;
        let mut heap = lock.lock().unwrap();
        heap.push(task);
        drop(heap);
        cvar.notify_one();
        
        id
    }
    
    /// 检查调度可行性
    pub fn is_schedulable(utilization: f64, num_processors: usize) -> bool {
        utilization <= num_processors as f64
    }
    
    /// 关闭调度器
    pub fn shutdown(self) {
        self.shutdown.store(true, std::sync::atomic::Ordering::SeqCst);
        self.queue.1.notify_all();
        
        for handle in self.threads {
            handle.join().unwrap();
        }
    }
}

/// 周期性任务
pub struct PeriodicTask {
    pub period: Duration,
    pub deadline: Duration,
    pub execution_time: Duration,
}

impl PeriodicTask {
    pub fn utilization(&self) -> f64 {
        self.execution_time.as_secs_f64() / self.period.as_secs_f64()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};
    
    #[test]
    fn test_deadline_ordering() {
        let now = Instant::now();
        let d1 = Deadline(now + Duration::from_secs(1));
        let d2 = Deadline(now + Duration::from_secs(2));
        
        assert!(d1 > d2);
        assert!(!d1.is_expired());
    }
    
    #[test]
    fn test_edf_scheduler() {
        let scheduler = EdfScheduler::new(2);
        let counter = Arc::new(AtomicUsize::new(0));
        
        let c = Arc::clone(&counter);
        scheduler.spawn_soft(
            Deadline::from_now(Duration::from_millis(100)),
            move || {
                c.fetch_add(1, Ordering::SeqCst);
            },
        );
        
        std::thread::sleep(Duration::from_millis(50));
        
        scheduler.shutdown();
        
        assert!(counter.load(Ordering::SeqCst) >= 1);
    }
    
    #[test]
    fn test_edf_schedulability() {
        assert!(EdfScheduler::is_schedulable(0.8, 1));
        assert!(!EdfScheduler::is_schedulable(1.2, 1));
        assert!(EdfScheduler::is_schedulable(1.5, 2));
    }
    
    #[test]
    fn test_periodic_task_utilization() {
        let task = PeriodicTask {
            period: Duration::from_millis(100),
            deadline: Duration::from_millis(100),
            execution_time: Duration::from_millis(50),
        };
        
        assert_eq!(task.utilization(), 0.5);
    }
}
