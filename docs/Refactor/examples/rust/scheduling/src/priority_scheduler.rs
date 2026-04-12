//! # 优先级调度器
//! 
//! 实现基于优先级的任务调度

use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::sync::{Arc, Condvar, Mutex};
use std::thread;
use std::time::Instant;

/// 任务优先级
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Priority(pub u32);

impl Priority {
    pub const MAX: Priority = Priority(u32::MAX);
    pub const HIGH: Priority = Priority(100);
    pub const NORMAL: Priority = Priority(50);
    pub const LOW: Priority = Priority(10);
    pub const MIN: Priority = Priority(0);
}

/// 优先级任务
pub struct PriorityTask {
    pub priority: Priority,
    pub id: TaskId,
    pub created_at: Instant,
    pub task: Box<dyn FnOnce() + Send>,
}

impl PriorityTask {
    pub fn new(priority: Priority, task: impl FnOnce() + Send + 'static) -> Self {
        Self {
            priority,
            id: TaskId::new(),
            created_at: Instant::now(),
            task: Box::new(task),
        }
    }
    
    pub fn execute(self) {
        (self.task)();
    }
}

impl Ord for PriorityTask {
    fn cmp(&self, other: &Self) -> Ordering {
        // 高优先级在前
        self.priority.cmp(&other.priority)
            .then_with(|| other.created_at.cmp(&self.created_at)) // 先创建的先执行
    }
}

impl PartialOrd for PriorityTask {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for PriorityTask {
    fn eq(&self, other: &Self) -> bool {
        self.priority == other.priority && self.id == other.id
    }
}

impl Eq for PriorityTask {}

/// 任务 ID
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TaskId(u64);

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

/// 优先级队列
pub struct PriorityQueue {
    heap: BinaryHeap<PriorityTask>,
}

impl PriorityQueue {
    pub fn new() -> Self {
        Self {
            heap: BinaryHeap::new(),
        }
    }
    
    pub fn push(&mut self, task: PriorityTask) {
        self.heap.push(task);
    }
    
    pub fn pop(&mut self) -> Option<PriorityTask> {
        self.heap.pop()
    }
    
    pub fn peek(&self) -> Option<&PriorityTask> {
        self.heap.peek()
    }
    
    pub fn len(&self) -> usize {
        self.heap.len()
    }
    
    pub fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }
}

impl Default for PriorityQueue {
    fn default() -> Self {
        Self::new()
    }
}

/// 优先级调度器
pub struct PriorityScheduler {
    queue: Arc<(Mutex<PriorityQueue>, Condvar)>,
    threads: Vec<thread::JoinHandle<()>>,
    shutdown: Arc<std::sync::atomic::AtomicBool>,
}

impl PriorityScheduler {
    pub fn new(num_threads: usize) -> Self {
        let queue = Arc::new((Mutex::new(PriorityQueue::new()), Condvar::new()));
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
        queue: Arc<(Mutex<PriorityQueue>, Condvar)>,
        shutdown: Arc<std::sync::atomic::AtomicBool>,
    ) {
        let (lock, cvar) = &*queue;
        
        loop {
            let mut queue = lock.lock().unwrap();
            
            // 等待任务或关闭信号
            queue = cvar
                .wait_while(queue, |q| {
                    q.is_empty() && !shutdown.load(std::sync::atomic::Ordering::Relaxed)
                })
                .unwrap();
            
            if shutdown.load(std::sync::atomic::Ordering::Relaxed) && queue.is_empty() {
                break;
            }
            
            if let Some(task) = queue.pop() {
                drop(queue); // 释放锁
                task.execute();
            }
        }
    }
    
    /// 提交高优先级任务
    pub fn spawn_high<F>(&self, f: F) -> TaskId
    where
        F: FnOnce() + Send + 'static,
    {
        self.spawn_with_priority(Priority::HIGH, f)
    }
    
    /// 提交普通优先级任务
    pub fn spawn<F>(&self, f: F) -> TaskId
    where
        F: FnOnce() + Send + 'static,
    {
        self.spawn_with_priority(Priority::NORMAL, f)
    }
    
    /// 提交低优先级任务
    pub fn spawn_low<F>(&self, f: F) -> TaskId
    where
        F: FnOnce() + Send + 'static,
    {
        self.spawn_with_priority(Priority::LOW, f)
    }
    
    /// 提交指定优先级任务
    pub fn spawn_with_priority<F>(&self, priority: Priority, f: F) -> TaskId
    where
        F: FnOnce() + Send + 'static,
    {
        let task = PriorityTask::new(priority, f);
        let id = task.id;
        
        let (lock, cvar) = &*self.queue;
        let mut queue = lock.lock().unwrap();
        queue.push(task);
        drop(queue);
        cvar.notify_one();
        
        id
    }
    
    /// 关闭调度器
    pub fn shutdown(self) {
        self.shutdown.store(true, std::sync::atomic::Ordering::SeqCst);
        self.queue.1.notify_all();
        
        for handle in self.threads {
            handle.join().unwrap();
        }
    }
    
    /// 获取队列长度
    pub fn queue_len(&self) -> usize {
        self.queue.0.lock().unwrap().len()
    }
}

/// 抢占式优先级调度器
pub struct PreemptivePriorityScheduler {
    // 简化的实现：使用线程池
    scheduler: PriorityScheduler,
    max_concurrent: usize,
}

impl PreemptivePriorityScheduler {
    pub fn new(num_threads: usize, max_concurrent: usize) -> Self {
        Self {
            scheduler: PriorityScheduler::new(num_threads),
            max_concurrent,
        }
    }
    
    pub fn spawn<F>(&self, priority: Priority, f: F) -> TaskId
    where
        F: FnOnce() + Send + 'static,
    {
        self.scheduler.spawn_with_priority(priority, f)
    }
    
    pub fn shutdown(self) {
        self.scheduler.shutdown();
    }
}

/// 速率限制调度器
pub struct RateLimitedScheduler {
    scheduler: PriorityScheduler,
    tokens: Arc<Mutex<f64>>,
    max_tokens: f64,
    refill_rate: f64, // tokens per second
    last_refill: Arc<Mutex<Instant>>,
}

impl RateLimitedScheduler {
    pub fn new(
        num_threads: usize,
        max_tokens: f64,
        refill_rate: f64,
    ) -> Self {
        Self {
            scheduler: PriorityScheduler::new(num_threads),
            tokens: Arc::new(Mutex::new(max_tokens)),
            max_tokens,
            refill_rate,
            last_refill: Arc::new(Mutex::new(Instant::now())),
        }
    }
    
    fn refill(&self) {
        let mut last = self.last_refill.lock().unwrap();
        let now = Instant::now();
        let elapsed = now.duration_since(*last).as_secs_f64();
        *last = now;
        
        let mut tokens = self.tokens.lock().unwrap();
        *tokens = (*tokens + elapsed * self.refill_rate).min(self.max_tokens);
    }
    
    pub fn spawn<F>(&self, cost: f64, f: F) -> Option<TaskId>
    where
        F: FnOnce() + Send + 'static,
    {
        self.refill();
        
        let mut tokens = self.tokens.lock().unwrap();
        if *tokens >= cost {
            *tokens -= cost;
            
            let tokens_clone = Arc::clone(&self.tokens);
            let id = self.scheduler.spawn(move || {
                f();
            });
            
            Some(id)
        } else {
            None // 速率限制
        }
    }
    
    pub fn shutdown(self) {
        self.scheduler.shutdown();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};
    
    #[test]
    fn test_priority_ordering() {
        let mut queue = PriorityQueue::new();
        
        queue.push(PriorityTask::new(Priority::LOW, || {}));
        queue.push(PriorityTask::new(Priority::HIGH, || {}));
        queue.push(PriorityTask::new(Priority::NORMAL, || {}));
        
        // 高优先级应该先出队
        let first = queue.pop().unwrap();
        assert_eq!(first.priority, Priority::HIGH);
        
        let second = queue.pop().unwrap();
        assert_eq!(second.priority, Priority::NORMAL);
        
        let third = queue.pop().unwrap();
        assert_eq!(third.priority, Priority::LOW);
    }
    
    #[test]
    fn test_priority_scheduler() {
        let scheduler = PriorityScheduler::new(2);
        let counter = Arc::new(AtomicUsize::new(0));
        
        let c1 = Arc::clone(&counter);
        scheduler.spawn_high(move || {
            c1.fetch_add(1, Ordering::SeqCst);
        });
        
        let c2 = Arc::clone(&counter);
        scheduler.spawn_low(move || {
            c2.fetch_add(1, Ordering::SeqCst);
        });
        
        std::thread::sleep(std::time::Duration::from_millis(50));
        
        scheduler.shutdown();
        
        // 验证任务被执行
        assert!(counter.load(Ordering::SeqCst) >= 2);
    }
    
    #[test]
    fn test_rate_limited_scheduler() {
        let scheduler = RateLimitedScheduler::new(1, 10.0, 1.0);
        
        let mut spawned = 0;
        for _ in 0..20 {
            if scheduler.spawn(1.0, || {}).is_some() {
                spawned += 1;
            }
        }
        
        // 应该只启动了约 10 个任务（初始令牌数）
        assert!(spawned <= 10);
        
        scheduler.shutdown();
    }
}
