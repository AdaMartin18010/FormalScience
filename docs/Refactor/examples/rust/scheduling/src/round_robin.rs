//! # 时间片轮转调度器
//! 
//! 实现经典的 RR (Round Robin) 调度算法

use std::collections::VecDeque;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

/// 时间片大小（毫秒）
pub const DEFAULT_TIME_SLICE_MS: u64 = 100;

/// 可运行的任务
pub trait Runnable: Send + 'static {
    fn run(&mut self, time_slice: Duration) -> RunResult;
}

/// 运行结果
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RunResult {
    /// 任务完成
    Completed,
    /// 需要更多时间
    NeedsMoreTime,
    /// 阻塞等待 I/O
    Blocked,
    /// 产生执行权
    Yield,
}

/// 时间片任务
pub struct TimeSliceTask {
    pub id: TaskId,
    pub task: Box<dyn Runnable>,
    pub priority: u32,
    pub accumulated_time: Duration,
    pub last_run: Option<Instant>,
}

impl TimeSliceTask {
    pub fn new(id: TaskId, task: impl Runnable, priority: u32) -> Self {
        Self {
            id,
            task: Box::new(task),
            priority,
            accumulated_time: Duration::ZERO,
            last_run: None,
        }
    }
    
    pub fn run(&mut self, time_slice: Duration) -> RunResult {
        self.last_run = Some(Instant::now());
        let start = Instant::now();
        
        let result = self.task.run(time_slice);
        
        let elapsed = start.elapsed();
        self.accumulated_time += elapsed;
        
        result
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

/// 时间片轮转调度器
pub struct RoundRobinScheduler {
    queue: Arc<Mutex<VecDeque<TimeSliceTask>>>,
    time_slice: Duration,
    threads: Vec<thread::JoinHandle<()>>,
    shutdown: Arc<std::sync::atomic::AtomicBool>,
}

impl RoundRobinScheduler {
    pub fn new(num_threads: usize, time_slice_ms: u64) -> Self {
        let queue = Arc::new(Mutex::new(VecDeque::new()));
        let time_slice = Duration::from_millis(time_slice_ms);
        let shutdown = Arc::new(std::sync::atomic::AtomicBool::new(false));
        
        let mut threads = Vec::with_capacity(num_threads);
        
        for _ in 0..num_threads {
            let q = Arc::clone(&queue);
            let s = Arc::clone(&shutdown);
            let ts = time_slice;
            
            let handle = thread::spawn(move || {
                Self::worker_loop(q, ts, s);
            });
            
            threads.push(handle);
        }
        
        Self {
            queue,
            time_slice,
            threads,
            shutdown,
        }
    }
    
    pub fn with_default_time_slice(num_threads: usize) -> Self {
        Self::new(num_threads, DEFAULT_TIME_SLICE_MS)
    }
    
    fn worker_loop(
        queue: Arc<Mutex<VecDeque<TimeSliceTask>>>,
        time_slice: Duration,
        shutdown: Arc<std::sync::atomic::AtomicBool>,
    ) {
        loop {
            if shutdown.load(std::sync::atomic::Ordering::Relaxed) {
                break;
            }
            
            let mut task = {
                let mut q = queue.lock().unwrap();
                q.pop_front()
            };
            
            if let Some(mut t) = task {
                match t.run(time_slice) {
                    RunResult::Completed => {
                        // 任务完成，不重新加入队列
                    }
                    RunResult::NeedsMoreTime => {
                        // 需要更多时间，重新加入队列
                        let mut q = queue.lock().unwrap();
                        q.push_back(t);
                    }
                    RunResult::Blocked => {
                        // 阻塞，稍后处理
                        std::thread::sleep(Duration::from_millis(10));
                        let mut q = queue.lock().unwrap();
                        q.push_back(t);
                    }
                    RunResult::Yield => {
                        // 主动产生执行权
                        let mut q = queue.lock().unwrap();
                        q.push_back(t);
                    }
                }
            } else {
                // 队列为空，短暂休眠
                thread::sleep(Duration::from_millis(1));
            }
        }
    }
    
    /// 提交任务
    pub fn spawn(&self, task: impl Runnable, priority: u32) -> TaskId {
        let id = TaskId::new();
        let task = TimeSliceTask::new(id, task, priority);
        
        let mut queue = self.queue.lock().unwrap();
        queue.push_back(task);
        
        id
    }
    
    /// 获取队列长度
    pub fn queue_len(&self) -> usize {
        self.queue.lock().unwrap().len()
    }
    
    /// 关闭调度器
    pub fn shutdown(self) {
        self.shutdown.store(true, std::sync::atomic::Ordering::SeqCst);
        for handle in self.threads {
            handle.join().unwrap();
        }
    }
}

/// 支持优先级的 RR 调度器（带权重的 RR）
pub struct WeightedRoundRobinScheduler {
    queue: Arc<Mutex<VecDeque<TimeSliceTask>>>,
    base_time_slice: Duration,
    threads: Vec<thread::JoinHandle<()>>,
    shutdown: Arc<std::sync::atomic::AtomicBool>,
}

impl WeightedRoundRobinScheduler {
    pub fn new(num_threads: usize, base_time_slice_ms: u64) -> Self {
        let queue = Arc::new(Mutex::new(VecDeque::new()));
        let base_time_slice = Duration::from_millis(base_time_slice_ms);
        let shutdown = Arc::new(std::sync::atomic::AtomicBool::new(false));
        
        let mut threads = Vec::with_capacity(num_threads);
        
        for _ in 0..num_threads {
            let q = Arc::clone(&queue);
            let s = Arc::clone(&shutdown);
            let ts = base_time_slice;
            
            let handle = thread::spawn(move || {
                Self::worker_loop(q, ts, s);
            });
            
            threads.push(handle);
        }
        
        Self {
            queue,
            base_time_slice,
            threads,
            shutdown,
        }
    }
    
    fn worker_loop(
        queue: Arc<Mutex<VecDeque<TimeSliceTask>>>,
        base_time_slice: Duration,
        shutdown: Arc<std::sync::atomic::AtomicBool>,
    ) {
        loop {
            if shutdown.load(std::sync::atomic::Ordering::Relaxed) {
                break;
            }
            
            let mut task = {
                let mut q = queue.lock().unwrap();
                q.pop_front()
            };
            
            if let Some(mut t) = task {
                // 根据优先级调整时间片
                let time_slice = base_time_slice * t.priority.max(1);
                
                match t.run(time_slice) {
                    RunResult::Completed => {}
                    RunResult::NeedsMoreTime | RunResult::Blocked | RunResult::Yield => {
                        let mut q = queue.lock().unwrap();
                        q.push_back(t);
                    }
                }
            } else {
                thread::sleep(Duration::from_millis(1));
            }
        }
    }
    
    pub fn spawn(&self, task: impl Runnable, priority: u32) -> TaskId {
        let id = TaskId::new();
        let task = TimeSliceTask::new(id, task, priority);
        
        let mut queue = self.queue.lock().unwrap();
        queue.push_back(task);
        
        id
    }
    
    pub fn shutdown(self) {
        self.shutdown.store(true, std::sync::atomic::Ordering::SeqCst);
        for handle in self.threads {
            handle.join().unwrap();
        }
    }
}

/// 一个简单的可运行任务实现
pub struct SimpleTask {
    work_units: usize,
    work_done: usize,
}

impl SimpleTask {
    pub fn new(work_units: usize) -> Self {
        Self {
            work_units,
            work_done: 0,
        }
    }
}

impl Runnable for SimpleTask {
    fn run(&mut self, _time_slice: Duration) -> RunResult {
        const WORK_PER_SLICE: usize = 10;
        
        let to_do = WORK_PER_SLICE.min(self.work_units - self.work_done);
        
        // 模拟工作
        for _ in 0..to_do {
            std::hint::black_box(self.work_done += 1);
        }
        
        if self.work_done >= self.work_units {
            RunResult::Completed
        } else {
            RunResult::NeedsMoreTime
        }
    }
}

/// 统计信息
#[derive(Debug, Default)]
pub struct RoundRobinStats {
    pub tasks_submitted: u64,
    pub tasks_completed: u64,
    pub context_switches: u64,
    pub total_wait_time: Duration,
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_simple_task() {
        let mut task = SimpleTask::new(100);
        
        while task.run(Duration::from_millis(10)) != RunResult::Completed {
            // 继续运行
        }
        
        assert_eq!(task.work_done, 100);
    }
    
    #[test]
    fn test_round_robin_scheduler() {
        let scheduler = RoundRobinScheduler::with_default_time_slice(2);
        
        let task1 = SimpleTask::new(50);
        let task2 = SimpleTask::new(50);
        
        scheduler.spawn(task1, 1);
        scheduler.spawn(task2, 1);
        
        // 等待任务完成
        std::thread::sleep(Duration::from_millis(500));
        
        scheduler.shutdown();
    }
    
    #[test]
    fn test_weighted_round_robin() {
        let scheduler = WeightedRoundRobinScheduler::new(2, 10);
        
        // 高优先级任务
        scheduler.spawn(SimpleTask::new(100), 10);
        
        // 低优先级任务
        scheduler.spawn(SimpleTask::new(100), 1);
        
        std::thread::sleep(Duration::from_millis(500));
        
        scheduler.shutdown();
    }
}
