//! 调度器模块
//! 
//! 提供多种 CPU 调度算法的实现。

use crate::metrics::{GanttChart, Metrics, ScheduleResult};
use crate::tasks::{Task, TaskState, TimeUnit};

pub mod fcfs;
pub mod sjf;
pub mod round_robin;
pub mod priority;
pub mod mlfq;

pub use fcfs::FcfsScheduler;
pub use sjf::SjfScheduler;
pub use round_robin::RoundRobinScheduler;
pub use priority::PriorityScheduler;
pub use mlfq::MlfqScheduler;

/// 调度器 trait
/// 
/// 所有调度算法都需要实现这个 trait
pub trait Scheduler {
    /// 运行调度算法
    /// 
    /// # 参数
    /// - `tasks`: 需要调度的任务列表
    /// 
    /// # 返回
    /// 包含甘特图和性能指标的调度结果
    fn schedule(&self, tasks: &[Task]) -> ScheduleResult;

    /// 获取调度器名称
    fn name(&self) -> &str;
}

/// 调度器运行时的共享状态
#[derive(Debug)]
pub struct SchedulerContext {
    /// 当前时间
    pub current_time: TimeUnit,
    /// 已完成的任务数量
    pub completed_count: usize,
    /// 甘特图
    pub gantt_chart: GanttChart,
}

impl SchedulerContext {
    /// 创建新的调度上下文
    pub fn new() -> Self {
        SchedulerContext {
            current_time: 0,
            completed_count: 0,
            gantt_chart: GanttChart::new(),
        }
    }

    /// 重置上下文
    pub fn reset(&mut self) {
        self.current_time = 0;
        self.completed_count = 0;
        self.gantt_chart = GanttChart::new();
    }

    /// 前进时间
    pub fn advance_time(&mut self, delta: TimeUnit) {
        self.current_time += delta;
    }

    /// 记录任务执行
    pub fn record_execution(&mut self, task_id: u32, duration: TimeUnit) {
        let start = self.current_time;
        let end = start + duration;
        self.gantt_chart.add_task(task_id, start, end);
        self.current_time = end;
    }

    /// 记录空闲时间
    pub fn record_idle(&mut self, duration: TimeUnit) {
        let start = self.current_time;
        let end = start + duration;
        self.gantt_chart.add_idle(start, end);
        self.current_time = end;
    }

    /// 标记任务完成
    pub fn mark_completed(&mut self) {
        self.completed_count += 1;
    }
}

impl Default for SchedulerContext {
    fn default() -> Self {
        Self::new()
    }
}

/// 辅助函数：获取已到达且未完成的任务
pub fn get_available_tasks(tasks: &[Task], current_time: TimeUnit) -> Vec<usize> {
    tasks
        .iter()
        .enumerate()
        .filter(|(_, t)| t.has_arrived(current_time) && !t.is_completed())
        .map(|(i, _)| i)
        .collect()
}

/// 辅助函数：检查是否所有任务都已完成
pub fn all_tasks_completed(tasks: &[Task]) -> bool {
    tasks.iter().all(|t| t.is_completed())
}

/// 辅助函数：找到下一个任务到达时间
pub fn next_arrival_time(tasks: &[Task], current_time: TimeUnit) -> Option<TimeUnit> {
    tasks
        .iter()
        .filter(|t| !t.is_completed() && t.arrival_time > current_time)
        .map(|t| t.arrival_time)
        .min()
}

/// 辅助函数：克隆并重置任务列表
pub fn clone_and_reset_tasks(tasks: &[Task]) -> Vec<Task> {
    let mut cloned: Vec<Task> = tasks.to_vec();
    for task in &mut cloned {
        task.reset();
    }
    cloned
}

/// 调度结果构建器
pub struct ScheduleResultBuilder {
    tasks: Vec<Task>,
    context: SchedulerContext,
}

impl ScheduleResultBuilder {
    /// 创建新的构建器
    pub fn new(tasks: Vec<Task>, context: SchedulerContext) -> Self {
        ScheduleResultBuilder { tasks, context }
    }

    /// 构建最终的结果
    pub fn build(self) -> ScheduleResult {
        let total_time = self.context.gantt_chart.total_span();
        let busy_time = self.context.gantt_chart.busy_time();
        let metrics = Metrics::calculate(&self.tasks, total_time, busy_time);

        ScheduleResult {
            tasks: self.tasks,
            gantt_chart: self.context.gantt_chart,
            metrics,
        }
    }
}

/// 调度器枚举（用于统一处理不同类型的调度器）
#[derive(Debug, Clone)]
pub enum SchedulerType {
    FCFS,
    SJF(bool), // true = preemptive (SRTF)
    RoundRobin(TimeUnit), // time quantum
    Priority(bool), // true = preemptive
    MLFQ(Vec<TimeUnit>), // time quanta for each queue
}

impl SchedulerType {
    /// 创建对应的调度器实例
    pub fn create(&self) -> Box<dyn Scheduler> {
        match self {
            SchedulerType::FCFS => Box::new(FcfsScheduler::new()),
            SchedulerType::SJF(preemptive) => Box::new(SjfScheduler::new(*preemptive)),
            SchedulerType::RoundRobin(quantum) => Box::new(RoundRobinScheduler::new(*quantum)),
            SchedulerType::Priority(preemptive) => Box::new(PriorityScheduler::new(*preemptive)),
            SchedulerType::MLFQ(quanta) => Box::new(MlfqScheduler::new(quanta.clone())),
        }
    }

    /// 获取调度器名称
    pub fn name(&self) -> String {
        match self {
            SchedulerType::FCFS => "FCFS".to_string(),
            SchedulerType::SJF(false) => "SJF (Non-preemptive)".to_string(),
            SchedulerType::SJF(true) => "SRTF (Preemptive)".to_string(),
            SchedulerType::RoundRobin(q) => format!("Round Robin (q={})", q),
            SchedulerType::Priority(false) => "Priority (Non-preemptive)".to_string(),
            SchedulerType::Priority(true) => "Priority (Preemptive)".to_string(),
            SchedulerType::MLFQ(_) => "MLFQ".to_string(),
        }
    }
}

/// 运行所有调度算法并比较结果
pub fn compare_all_schedulers(tasks: &[Task]) -> Vec<(String, ScheduleResult)> {
    let schedulers = vec![
        ("FCFS".to_string(), SchedulerType::FCFS.create()),
        ("SJF".to_string(), SchedulerType::SJF(false).create()),
        ("SRTF".to_string(), SchedulerType::SJF(true).create()),
        ("Round Robin (q=2)".to_string(), 
         SchedulerType::RoundRobin(2).create()),
        ("Priority".to_string(), SchedulerType::Priority(false).create()),
    ];

    schedulers
        .into_iter()
        .map(|(name, scheduler)| {
            let result = scheduler.schedule(tasks);
            (name, result)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tasks::utils::create_sample_tasks;

    #[test]
    fn test_scheduler_context() {
        let mut ctx = SchedulerContext::new();
        assert_eq!(ctx.current_time, 0);
        
        ctx.record_execution(1, 5);
        assert_eq!(ctx.current_time, 5);
        assert_eq!(ctx.gantt_chart.entries.len(), 1);
        
        ctx.record_idle(3);
        assert_eq!(ctx.current_time, 8);
        assert_eq!(ctx.gantt_chart.entries.len(), 2);
    }

    #[test]
    fn test_all_tasks_completed() {
        let mut tasks = create_sample_tasks();
        assert!(!all_tasks_completed(&tasks));
        
        for task in &mut tasks {
            task.state = TaskState::Completed;
            task.remaining_time = 0;
        }
        assert!(all_tasks_completed(&tasks));
    }
}
