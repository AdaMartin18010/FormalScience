/// 优先级调度算法实现
/// 
/// 优先级调度根据进程的优先级来决定执行顺序。
/// 分为抢占式和非抢占式两种策略。

use std::cmp::Ordering;
use std::collections::BinaryHeap;

/// 进程状态
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProcessState {
    Ready,      // 就绪
    Running,    // 运行中
    Blocked,    // 阻塞
    Completed,  // 完成
}

/// 优先级进程
#[derive(Debug, Clone)]
pub struct PriorityProcess {
    /// 进程ID
    pub id: u32,
    /// 进程名称
    pub name: String,
    /// 优先级（数值越小优先级越高）
    pub priority: u8,
    /// 到达时间
    pub arrival_time: u32,
    /// 执行所需总时间
    pub burst_time: u32,
    /// 剩余执行时间
    pub remaining_time: u32,
    /// 进程状态
    pub state: ProcessState,
    /// 等待时间
    pub waiting_time: u32,
    /// 完成时间
    pub completion_time: Option<u32>,
    /// 静态优先级（用于 aging 算法）
    pub base_priority: u8,
}

impl PriorityProcess {
    /// 创建新进程
    pub fn new(id: u32, name: &str, priority: u8, arrival_time: u32, burst_time: u32) -> Self {
        Self {
            id,
            name: name.to_string(),
            priority,
            arrival_time,
            burst_time,
            remaining_time: burst_time,
            state: ProcessState::Ready,
            waiting_time: 0,
            completion_time: None,
            base_priority: priority,
        }
    }

    /// 获取周转时间
    pub fn turnaround_time(&self) -> Option<u32> {
        self.completion_time.map(|ct| ct - self.arrival_time)
    }
}

// 为优先级队列实现 Ord trait
impl Ord for PriorityProcess {
    fn cmp(&self, other: &Self) -> Ordering {
        // 优先级高的在前（数值小）
        other.priority.cmp(&self.priority)
            .then_with(|| other.arrival_time.cmp(&self.arrival_time))
    }
}

impl PartialOrd for PriorityProcess {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for PriorityProcess {
    fn eq(&self, other: &Self) -> bool {
        self.priority == other.priority && self.arrival_time == other.arrival_time
    }
}

impl Eq for PriorityProcess {}

/// 非抢占式优先级调度器
pub struct NonPreemptivePriorityScheduler {
    /// 就绪队列
    ready_queue: BinaryHeap<PriorityProcess>,
    /// 当前时间
    current_time: u32,
    /// 完成的进程
    completed_processes: Vec<PriorityProcess>,
    /// 平均等待时间
    avg_waiting_time: f64,
    /// 平均周转时间
    avg_turnaround_time: f64,
}

impl NonPreemptivePriorityScheduler {
    pub fn new() -> Self {
        Self {
            ready_queue: BinaryHeap::new(),
            current_time: 0,
            completed_processes: Vec::new(),
            avg_waiting_time: 0.0,
            avg_turnaround_time: 0.0,
        }
    }

    /// 添加进程
    pub fn add_process(&mut self, process: PriorityProcess) {
        self.ready_queue.push(process);
    }

    /// 运行调度
    pub fn run(&mut self) -> Vec<PriorityProcess> {
        println!("\n=== 非抢占式优先级调度 ===");
        
        let mut total_waiting_time = 0u32;
        let mut total_turnaround_time = 0u32;
        let mut process_count = 0u32;

        while let Some(mut process) = self.ready_queue.pop() {
            // 如果当前时间小于到达时间，快进时间
            if self.current_time < process.arrival_time {
                self.current_time = process.arrival_time;
            }

            // 计算等待时间
            process.waiting_time = self.current_time - process.arrival_time;
            total_waiting_time += process.waiting_time;

            // 执行进程
            println!(
                "时间 {}: 执行进程 {} ({}), 优先级={}, 执行时间={}ms",
                self.current_time,
                process.id,
                process.name,
                process.priority,
                process.burst_time
            );

            process.state = ProcessState::Running;
            self.current_time += process.burst_time;
            process.remaining_time = 0;
            process.completion_time = Some(self.current_time);
            process.state = ProcessState::Completed;

            // 计算周转时间
            let turnaround = process.turnaround_time().unwrap();
            total_turnaround_time += turnaround;
            process_count += 1;

            println!(
                "  -> 完成时间: {}, 等待时间: {}, 周转时间: {}",
                self.current_time,
                process.waiting_time,
                turnaround
            );

            self.completed_processes.push(process);
        }

        if process_count > 0 {
            self.avg_waiting_time = total_waiting_time as f64 / process_count as f64;
            self.avg_turnaround_time = total_turnaround_time as f64 / process_count as f64;
        }

        println!("\n=== 调度完成 ===");
        println!("总耗时: {}ms", self.current_time);
        println!("平均等待时间: {:.2}ms", self.avg_waiting_time);
        println!("平均周转时间: {:.2}ms", self.avg_turnaround_time);

        self.completed_processes.clone()
    }
}

/// 抢占式优先级调度器（支持 Aging）
pub struct PreemptivePriorityScheduler {
    /// 就绪队列
    ready_queue: BinaryHeap<PriorityProcess>,
    /// 当前时间
    current_time: u32,
    /// 完成的进程
    completed_processes: Vec<PriorityProcess>,
    /// 当前运行的进程
    current_process: Option<PriorityProcess>,
    /// Aging 时间间隔
    aging_interval: u32,
    /// Aging 增量
    aging_boost: u8,
}

impl PreemptivePriorityScheduler {
    pub fn new(aging_interval: u32, aging_boost: u8) -> Self {
        Self {
            ready_queue: BinaryHeap::new(),
            current_time: 0,
            completed_processes: Vec::new(),
            current_process: None,
            aging_interval,
            aging_boost,
        }
    }

    /// 添加进程
    pub fn add_process(&mut self, process: PriorityProcess) {
        self.ready_queue.push(process);
    }

    /// 应用 Aging 算法，防止饥饿
    fn apply_aging(&mut self) {
        let mut temp_queue: Vec<PriorityProcess> = Vec::new();
        
        while let Some(mut process) = self.ready_queue.pop() {
            // 增加等待时间
            let wait_time = self.current_time - process.arrival_time;
            
            // 如果等待时间超过 aging_interval，提升优先级
            if wait_time > 0 && wait_time % self.aging_interval == 0 {
                let new_priority = process.priority.saturating_sub(self.aging_boost);
                if new_priority != process.priority {
                    println!(
                        "  -> Aging: 进程 {} 优先级 {} -> {}",
                        process.id,
                        process.priority,
                        new_priority
                    );
                    process.priority = new_priority;
                }
            }
            
            temp_queue.push(process);
        }
        
        // 重新放入队列
        for process in temp_queue {
            self.ready_queue.push(process);
        }
    }

    /// 执行一个时间单位
    pub fn tick(&mut self) -> bool {
        self.apply_aging();

        // 检查是否有更高优先级的进程到达
        if let Some(ref current) = self.current_process {
            if let Some(next) = self.ready_queue.peek() {
                if next.priority < current.priority {
                    // 抢占当前进程
                    println!(
                        "时间 {}: 进程 {} 被进程 {} 抢占",
                        self.current_time,
                        current.id,
                        next.id
                    );
                    let preempted = self.current_process.take().unwrap();
                    self.ready_queue.push(preempted);
                }
            }
        }

        // 如果没有正在运行的进程，从队列中取一个
        if self.current_process.is_none() {
            if let Some(process) = self.ready_queue.pop() {
                self.current_process = Some(process);
            } else {
                self.current_time += 1;
                return false;
            }
        }

        // 执行当前进程
        if let Some(ref mut process) = self.current_process {
            process.remaining_time -= 1;
            
            if process.remaining_time == 0 {
                // 进程完成
                let mut completed = self.current_process.take().unwrap();
                completed.completion_time = Some(self.current_time + 1);
                completed.state = ProcessState::Completed;
                
                println!(
                    "时间 {}: 进程 {} ({}) 完成",
                    self.current_time + 1,
                    completed.id,
                    completed.name
                );
                
                self.completed_processes.push(completed);
            }
        }

        self.current_time += 1;
        true
    }

    /// 运行调度直到所有进程完成
    pub fn run(&mut self) -> Vec<PriorityProcess> {
        println!("\n=== 抢占式优先级调度（带Aging） ===");

        while !self.ready_queue.is_empty() || self.current_process.is_some() {
            self.tick();
        }

        println!("\n=== 调度完成 ===");
        println!("总耗时: {}ms", self.current_time);

        self.completed_processes.clone()
    }
}

/// 速率单调调度（Rate Monotonic Scheduling）
/// 用于实时系统，周期越短优先级越高
#[derive(Debug, Clone)]
pub struct RealTimeTask {
    /// 任务ID
    pub id: u32,
    /// 任务名称
    pub name: String,
    /// 周期（ms）
    pub period: u32,
    /// 执行时间
    pub execution_time: u32,
    /// 截止时间
    pub deadline: u32,
    /// 下一次释放时间
    pub next_release: u32,
    /// 剩余执行时间
    pub remaining: u32,
}

impl RealTimeTask {
    pub fn new(id: u32, name: &str, period: u32, execution_time: u32) -> Self {
        Self {
            id,
            name: name.to_string(),
            period,
            execution_time,
            deadline: period,
            next_release: 0,
            remaining: 0,
        }
    }

    /// 检查是否可调度（利用率测试）
    pub fn is_schedulable(tasks: &[RealTimeTask]) -> bool {
        let n = tasks.len() as f64;
        let utilization: f64 = tasks.iter()
            .map(|t| t.execution_time as f64 / t.period as f64)
            .sum();
        
        // Rate Monotonic 利用率界限
        let bound = n * (2.0f64.powf(1.0 / n) - 1.0);
        
        println!("总利用率: {:.4}, 界限: {:.4}", utilization, bound);
        utilization <= bound
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_non_preemptive_priority() {
        let mut scheduler = NonPreemptivePriorityScheduler::new();
        
        // 优先级数值越小优先级越高
        scheduler.add_process(PriorityProcess::new(1, "高优先级", 1, 0, 10));
        scheduler.add_process(PriorityProcess::new(2, "中优先级", 2, 0, 5));
        scheduler.add_process(PriorityProcess::new(3, "低优先级", 3, 0, 8));
        
        let completed = scheduler.run();
        assert_eq!(completed.len(), 3);
        // 应该按 1, 2, 3 的顺序完成
        assert_eq!(completed[0].id, 1);
    }

    #[test]
    fn test_rate_monotonic_schedulability() {
        let tasks = vec![
            RealTimeTask::new(1, "任务1", 20, 5),
            RealTimeTask::new(2, "任务2", 50, 10),
            RealTimeTask::new(3, "任务3", 100, 20),
        ];
        
        assert!(RealTimeTask::is_schedulable(&tasks));
    }
}

fn main() {
    // 非抢占式优先级调度示例
    let mut non_preemptive = NonPreemptivePriorityScheduler::new();
    non_preemptive.add_process(PriorityProcess::new(1, "系统进程", 1, 0, 20));
    non_preemptive.add_process(PriorityProcess::new(2, "用户进程", 3, 5, 15));
    non_preemptive.add_process(PriorityProcess::new(3, "后台任务", 5, 0, 10));
    non_preemptive.run();

    // 抢占式优先级调度示例
    let mut preemptive = PreemptivePriorityScheduler::new(50, 1);
    preemptive.add_process(PriorityProcess::new(4, "关键任务", 1, 0, 30));
    preemptive.add_process(PriorityProcess::new(5, "普通任务", 2, 10, 20));
    preemptive.add_process(PriorityProcess::new(6, "低优先级", 3, 5, 25));
    preemptive.run();

    // 实时任务可调度性测试
    println!("\n=== 实时任务可调度性分析 ===");
    let rt_tasks = vec![
        RealTimeTask::new(1, "传感器读取", 20, 5),
        RealTimeTask::new(2, "控制算法", 50, 10),
        RealTimeTask::new(3, "数据记录", 100, 15),
    ];
    
    let schedulable = RealTimeTask::is_schedulable(&rt_tasks);
    println!("任务集可调度: {}", schedulable);
}
