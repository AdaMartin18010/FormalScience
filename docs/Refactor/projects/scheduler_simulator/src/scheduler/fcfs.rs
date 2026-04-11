//! FCFS (First-Come-First-Served) 调度器
//! 
//! 先来先服务调度算法：按照任务到达的顺序执行。
//! 特点：
//! - 非抢占式
//! - 实现简单
//! - 可能导致 convoy effect（护航效应）
//! - 平均等待时间可能较长

use crate::metrics::ScheduleResult;
use crate::scheduler::{clone_and_reset_tasks, all_tasks_completed, next_arrival_time, Scheduler, SchedulerContext, ScheduleResultBuilder};
use crate::tasks::{Task, TaskState, TimeUnit};

/// FCFS 调度器
#[derive(Debug, Clone)]
pub struct FcfsScheduler;

impl FcfsScheduler {
    /// 创建新的 FCFS 调度器
    pub fn new() -> Self {
        FcfsScheduler
    }

    /// 选择下一个要执行的任务
    /// 
    /// 策略：选择到达时间最早且未完成的任务
    fn select_next_task(&self, tasks: &[Task], current_time: TimeUnit) -> Option<usize> {
        tasks
            .iter()
            .enumerate()
            .filter(|(_, t)| !t.is_completed() && t.arrival_time <= current_time)
            .min_by_key(|(_, t)| t.arrival_time)
            .map(|(idx, _)| idx)
    }
}

impl Default for FcfsScheduler {
    fn default() -> Self {
        Self::new()
    }
}

impl Scheduler for FcfsScheduler {
    fn schedule(&self, tasks: &[Task]) -> ScheduleResult {
        // 克隆并重置任务状态
        let mut tasks = clone_and_reset_tasks(tasks);
        let mut context = SchedulerContext::new();

        // 主调度循环
        while !all_tasks_completed(&tasks) {
            // 尝试选择下一个任务
            match self.select_next_task(&tasks, context.current_time) {
                Some(idx) => {
                    // 找到了可执行的任务
                    let task = &mut tasks[idx];
                    
                    // 更新任务状态
                    task.update_waiting_time(context.current_time);
                    task.mark_running();
                    
                    // 记录任务开始执行（如果需要）
                    if task.first_run_time.is_none() {
                        task.first_run_time = Some(context.current_time);
                    }
                    
                    // 执行任务直到完成（非抢占式）
                    let burst = task.remaining_time;
                    for _ in 0..burst {
                        task.execute(context.current_time);
                        context.advance_time(1);
                    }
                    
                    // 记录到甘特图
                    context.record_execution(task.id, burst);
                    context.mark_completed();
                }
                None => {
                    // 没有可执行的任务，CPU 空闲
                    if let Some(next_arrival) = next_arrival_time(&tasks, context.current_time) {
                        let idle_duration = next_arrival - context.current_time;
                        context.record_idle(idle_duration);
                    } else {
                        // 没有更多任务了，退出
                        break;
                    }
                }
            }
        }

        ScheduleResultBuilder::new(tasks, context).build()
    }

    fn name(&self) -> &str {
        "FCFS (First-Come-First-Served)"
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn create_test_tasks() -> Vec<Task> {
        vec![
            Task::new(1, 0, 8, None),
            Task::new(2, 1, 4, None),
            Task::new(3, 2, 9, None),
        ]
    }

    #[test]
    fn test_fcfs_basic() {
        let scheduler = FcfsScheduler::new();
        let tasks = create_test_tasks();
        let result = scheduler.schedule(&tasks);

        // 验证所有任务都已完成
        assert_eq!(result.tasks.len(), 3);
        assert!(result.tasks.iter().all(|t| t.is_completed()));

        // FCFS 执行顺序应该是 1, 2, 3
        // 任务1: 0-8, 任务2: 8-12, 任务3: 12-21
        assert_eq!(result.tasks[0].completion_time, Some(8));
        assert_eq!(result.tasks[1].completion_time, Some(12));
        assert_eq!(result.tasks[2].completion_time, Some(21));
    }

    #[test]
    fn test_fcfs_with_idle() {
        let scheduler = FcfsScheduler::new();
        let tasks = vec![
            Task::new(1, 0, 3, None),
            Task::new(2, 5, 2, None), // 任务2在任务1完成后才到达
        ];
        
        let result = scheduler.schedule(&tasks);
        
        // 应该有一个空闲时间段 3-5
        let idle_time = result.gantt_chart.idle_time();
        assert_eq!(idle_time, 2);
        
        // 总时间应该是 7 (0-3 任务1, 3-5 空闲, 5-7 任务2)
        assert_eq!(result.gantt_chart.total_span(), 7);
    }

    #[test]
    fn test_fcfs_waiting_time() {
        let scheduler = FcfsScheduler::new();
        // 测试护航效应
        let tasks = vec![
            Task::new(1, 0, 10, None),  // 长任务先到达
            Task::new(2, 1, 1, None),   // 短任务后到达，但需要等待长任务
        ];
        
        let result = scheduler.schedule(&tasks);
        
        // 任务2需要等待任务1完成，等待时间应该是 10 - 1 = 9
        // 但实际上由于任务2在时刻1到达，任务1执行了10个单位，
        // 所以任务2的等待时间 = 10 - 1 = 9
        let task2 = &result.tasks[1];
        assert_eq!(task2.waiting_time, 9);
    }
}
