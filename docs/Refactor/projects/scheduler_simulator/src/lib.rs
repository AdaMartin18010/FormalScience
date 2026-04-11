//! Scheduler Simulator Library
//! 
//! 一个 CPU 调度算法模拟器库，支持多种经典调度算法。

pub mod metrics;
pub mod scheduler;
pub mod tasks;

// 重新导出常用类型
pub use metrics::{GanttChart, GanttEntry, Metrics, ScheduleResult};
pub use scheduler::{
    clone_and_reset_tasks, all_tasks_completed, next_arrival_time,
    Scheduler, SchedulerContext, SchedulerType, ScheduleResultBuilder,
    compare_all_schedulers,
    FcfsScheduler, SjfScheduler, RoundRobinScheduler, 
    PriorityScheduler, MlfqScheduler,
};
pub use tasks::{Task, TaskId, TaskState, TimeUnit, Priority, utils as task_utils};
