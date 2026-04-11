//! Priority Scheduling 调度器
//! 
//! 优先级调度算法：根据任务的优先级进行调度，
//! 优先级数值越小表示优先级越高。
//! 
//! 两种模式：
//! - 非抢占式：一旦开始执行就运行到完成
//! - 抢占式：新任务到达时，如果优先级更高，则抢占 CPU
//! 
//! 特点：
//! - 可以满足重要任务的及时响应
//! - 可能导致低优先级任务饥饿
//! - 通常需要 aging 机制防止饥饿

use crate::metrics::ScheduleResult;
use crate::scheduler::{clone_and_reset_tasks, all_tasks_completed, next_arrival_time, Scheduler, SchedulerContext, ScheduleResultBuilder};
use crate::tasks::{Task, TaskState, TimeUnit, Priority};

/// 优先级调度器
#[derive(Debug, Clone)]
pub struct PriorityScheduler {
    /// 是否使用抢占式调度
    preemptive: bool,
}

impl PriorityScheduler {
    /// 创建新的优先级调度器
    /// 
    /// # 参数
    /// - `preemptive`: true 表示抢占式，false 表示非抢占式
    pub fn new(preemptive: bool) -> Self {
        PriorityScheduler { preemptive }
    }

    /// 选择下一个要执行的任务（优先级最高的）
    fn select_next_task(&self, tasks: &[Task], current_time: TimeUnit) -> Option<usize> {
        tasks
            .iter()
            .enumerate()
            .filter(|(_, t)| !t.is_completed() && t.arrival_time <= current_time)
            .min_by_key(|(_, t)| t.priority) // 优先级数值越小优先级越高
            .map(|(idx, _)| idx)
    }

    /// 检查是否有更高优先级的任务到达（用于抢占式调度）
    fn check_higher_priority_arrival(
        &self,
        tasks: &[Task],
        current_priority: Priority,
        current_time: TimeUnit,
    ) -> Option<TimeUnit> {
        if !self.preemptive {
            return None;
        }

        tasks
            .iter()
            .filter(|t| {
                !t.is_completed()
                    && t.arrival_time > current_time
                    && t.priority < current_priority // 优先级数值更小 = 更高优先级
            })
            .map(|t| t.arrival_time)
            .min()
    }
}

impl Scheduler for PriorityScheduler {
    fn schedule(&self, tasks: &[Task]) -> ScheduleResult {
        let mut tasks = clone_and_reset_tasks(tasks);
        let mut context = SchedulerContext::new();
        let mut current_task_idx: Option<usize> = None;

        while !all_tasks_completed(&tasks) {
            // 尝试选择最高优先级的任务
            let selected_idx = self.select_next_task(&tasks, context.current_time);

            // 抢占式调度检查
            if self.preemptive {
                if let Some(new_idx) = selected_idx {
                    if let Some(current_idx) = current_task_idx {
                        // 如果有新任务的优先级高于当前任务，抢占
                        if tasks[new_idx].priority < tasks[current_idx].priority {
                            // 保存当前任务状态
                            tasks[current_idx].mark_ready(context.current_time);
                            current_task_idx = None;
                        }
                    }
                }
            }

            // 如果没有当前任务，切换到选中的任务
            if current_task_idx.is_none() {
                current_task_idx = selected_idx;
                if let Some(idx) = current_task_idx {
                    let task = &mut tasks[idx];
                    task.update_waiting_time(context.current_time);
                    task.mark_running();
                    
                    if task.first_run_time.is_none() {
                        task.first_run_time = Some(context.current_time);
                    }
                }
            }

            match current_task_idx {
                Some(idx) => {
                    let current_priority = tasks[idx].priority;
                    
                    // 检查是否有更高优先级的任务会到达
                    if let Some(preempt_time) = self.check_higher_priority_arrival(
                        &tasks, current_priority, context.current_time) {
                        // 在当前任务执行到被抢占的时间点
                        let run_duration = preempt_time - context.current_time;
                        let task = &mut tasks[idx];
                        
                        for _ in 0..run_duration {
                            if task.execute(context.current_time) {
                                break;
                            }
                            context.advance_time(1);
                        }
                        
                        context.record_execution(task.id, run_duration);
                        
                        if task.is_completed() {
                            context.mark_completed();
                            current_task_idx = None;
                        } else {
                            task.mark_ready(context.current_time);
                            current_task_idx = None; // 被抢占
                        }
                    } else {
                        // 执行到完成
                        let task = &mut tasks[idx];
                        let remaining = task.remaining_time;
                        
                        for _ in 0..remaining {
                            task.execute(context.current_time);
                            context.advance_time(1);
                        }
                        
                        context.record_execution(task.id, remaining);
                        context.mark_completed();
                        current_task_idx = None;
                    }
                }
                None => {
                    // CPU 空闲
                    if let Some(next_arrival) = next_arrival_time(&tasks, context.current_time) {
                        let idle_duration = next_arrival - context.current_time;
                        context.record_idle(idle_duration);
                    } else {
                        break;
                    }
                }
            }
        }

        ScheduleResultBuilder::new(tasks, context).build()
    }

    fn name(&self) -> &str {
        if self.preemptive {
            "Priority Scheduling (Preemptive)"
        } else {
            "Priority Scheduling (Non-preemptive)"
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_priority_non_preemptive() {
        let scheduler = PriorityScheduler::new(false);
        let tasks = vec![
            Task::new(1, 0, 10, Some(3)), // 优先级3（较低）
            Task::new(2, 0, 1, Some(1)),  // 优先级1（最高）
            Task::new(3, 0, 2, Some(4)),  // 优先级4（最低）
            Task::new(4, 0, 1, Some(5)),  // 优先级5（最低）
            Task::new(5, 0, 5, Some(2)),  // 优先级2（较高）
        ];

        let result = scheduler.schedule(&tasks);

        // 非抢占式：按优先级排序执行
        // 执行顺序应该是: 任务2(p=1), 任务5(p=2), 任务1(p=3), 任务3(p=4), 任务4(p=5)
        
        // 验证所有任务完成
        assert!(result.tasks.iter().all(|t| t.is_completed()));
        
        // 任务2应该最先完成（优先级最高，执行时间最短）
        assert_eq!(result.tasks[1].completion_time, Some(1));
    }

    #[test]
    fn test_priority_preemptive() {
        let scheduler = PriorityScheduler::new(true);
        let tasks = vec![
            Task::new(1, 0, 10, Some(3)),
            Task::new(2, 1, 1, Some(1)),  // t=1到达，更高优先级，应该抢占
        ];

        let result = scheduler.schedule(&tasks);

        // 任务2优先级更高，应该先完成
        assert!(result.tasks[1].completion_time < result.tasks[0].completion_time);
    }

    #[test]
    fn test_priority_starvation() {
        // 测试饥饿：持续有高优先级任务到达
        let scheduler = PriorityScheduler::new(true);
        let tasks = vec![
            Task::new(1, 0, 100, Some(5)), // 低优先级任务
            Task::new(2, 1, 1, Some(1)),   // 高优先级任务
            Task::new(3, 2, 1, Some(1)),   // 高优先级任务
            Task::new(4, 3, 1, Some(1)),   // 高优先级任务
        ];

        let result = scheduler.schedule(&tasks);

        // 所有任务最终都应该完成
        assert!(result.tasks.iter().all(|t| t.is_completed()));
        
        // 但低优先级任务的等待时间应该很长
        let low_priority_task = &result.tasks[0];
        assert!(low_priority_task.waiting_time >= 3);
    }

    #[test]
    fn test_priority_same_priority() {
        // 相同优先级的任务应该按到达顺序执行（FCFS）
        let scheduler = PriorityScheduler::new(false);
        let tasks = vec![
            Task::new(1, 0, 5, Some(1)),
            Task::new(2, 1, 3, Some(1)),
            Task::new(3, 2, 1, Some(1)),
        ];

        let result = scheduler.schedule(&tasks);

        // 相同优先级，按到达顺序：1, 2, 3
        assert!(result.tasks[0].completion_time <= result.tasks[1].completion_time);
        assert!(result.tasks[1].completion_time <= result.tasks[2].completion_time);
    }
}
