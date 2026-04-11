//! SJF (Shortest Job First) 调度器
//! 
//! 短作业优先调度算法：选择预计执行时间最短的任务。
//! 
//! 两种模式：
//! - 非抢占式 (Non-preemptive)：一旦开始执行就一直运行到完成
//! - 抢占式 (SRTF - Shortest Remaining Time First)：新任务到达时，
//!   如果其执行时间比当前任务的剩余时间更短，则抢占 CPU
//! 
//! 特点：
//! - 理论上可以获得最小的平均等待时间
//! - 可能导致长作业饥饿（starvation）
//! - 需要预先知道或估计作业的执行时间

use crate::metrics::ScheduleResult;
use crate::scheduler::{clone_and_reset_tasks, all_tasks_completed, next_arrival_time, Scheduler, SchedulerContext, ScheduleResultBuilder};
use crate::tasks::{Task, TaskState, TimeUnit};

/// SJF 调度器
#[derive(Debug, Clone)]
pub struct SjfScheduler {
    /// 是否使用抢占式调度 (SRTF)
    preemptive: bool,
}

impl SjfScheduler {
    /// 创建新的 SJF 调度器
    /// 
    /// # 参数
    /// - `preemptive`: true 表示使用 SRTF（抢占式），false 表示非抢占式
    pub fn new(preemptive: bool) -> Self {
        SjfScheduler { preemptive }
    }

    /// 选择下一个要执行的任务
    /// 
    /// 策略：选择执行时间最短且已到达的未完成任务
    fn select_next_task(&self, tasks: &[Task], current_time: TimeUnit) -> Option<usize> {
        tasks
            .iter()
            .enumerate()
            .filter(|(_, t)| !t.is_completed() && t.arrival_time <= current_time)
            .min_by_key(|(_, t)| {
                if self.preemptive {
                    t.remaining_time // SRTF: 选择剩余时间最短的
                } else {
                    t.burst_time // SJF: 选择总执行时间最短的
                }
            })
            .map(|(idx, _)| idx)
    }

    /// 检查是否有新任务会抢占当前任务
    /// 
    /// 返回下一个可能抢占的时间点和对应的任务索引
    fn check_preemption(
        &self,
        tasks: &[Task],
        current_task_idx: usize,
        current_time: TimeUnit,
    ) -> Option<(TimeUnit, usize)> {
        if !self.preemptive {
            return None;
        }

        let current_remaining = tasks[current_task_idx].remaining_time;

        // 查找所有可能在当前任务完成前到达的任务
        tasks
            .iter()
            .enumerate()
            .filter(|(idx, t)| {
                *idx != current_task_idx
                    && !t.is_completed()
                    && t.arrival_time > current_time
                    && t.arrival_time < current_time + current_remaining
                    && t.burst_time < current_remaining
            })
            .min_by_key(|(_, t)| (t.arrival_time, t.burst_time))
            .map(|(idx, t)| (t.arrival_time, idx))
    }
}

impl Scheduler for SjfScheduler {
    fn schedule(&self, tasks: &[Task]) -> ScheduleResult {
        let mut tasks = clone_and_reset_tasks(tasks);
        let mut context = SchedulerContext::new();
        let mut current_task_idx: Option<usize> = None;

        while !all_tasks_completed(&tasks) {
            // 如果当前没有运行任务，或者使用抢占式调度，尝试选择新任务
            if current_task_idx.is_none() || self.preemptive {
                if let Some(new_idx) = self.select_next_task(&tasks, context.current_time) {
                    // 如果是新任务或抢占发生
                    if current_task_idx != Some(new_idx) {
                        // 如果有正在运行的任务，将其标记为就绪
                        if let Some(idx) = current_task_idx {
                            tasks[idx].mark_ready(context.current_time);
                        }

                        // 切换到新任务
                        current_task_idx = Some(new_idx);
                    }
                }
            }

            match current_task_idx {
                Some(idx) => {
                    // 先检查抢占
                    if self.preemptive {
                        if let Some((preempt_time, _)) = 
                            self.check_preemption(&tasks, idx, context.current_time) {
                            // 在当前时刻到抢占时刻之间执行任务
                            let run_duration = preempt_time - context.current_time;
                            let task = &mut tasks[idx];
                            
                            task.update_waiting_time(context.current_time);
                            task.mark_running();
                            
                            if task.first_run_time.is_none() {
                                task.first_run_time = Some(context.current_time);
                            }
                            
                            for _ in 0..run_duration {
                                task.execute(context.current_time);
                                context.advance_time(1);
                            }
                            context.record_execution(task.id, run_duration);
                            current_task_idx = None; // 强制重新选择任务
                            continue;
                        }
                    }

                    // 执行任务直到完成
                    let task = &mut tasks[idx];
                    
                    task.update_waiting_time(context.current_time);
                    task.mark_running();
                    
                    if task.first_run_time.is_none() {
                        task.first_run_time = Some(context.current_time);
                    }
                    
                    let remaining = task.remaining_time;
                    for _ in 0..remaining {
                        task.execute(context.current_time);
                        context.advance_time(1);
                    }
                    context.record_execution(task.id, remaining);
                    context.mark_completed();
                    current_task_idx = None;
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
            "SRTF (Shortest Remaining Time First)"
        } else {
            "SJF (Shortest Job First)"
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sjf_non_preemptive() {
        let scheduler = SjfScheduler::new(false);
        let tasks = vec![
            Task::new(1, 0, 7, None),
            Task::new(2, 2, 4, None),
            Task::new(3, 4, 1, None),
            Task::new(4, 5, 4, None),
        ];

        let result = scheduler.schedule(&tasks);

        // 非抢占式 SJF 执行顺序:
        // t=0: 只有任务1到达，执行它 (burst=7)
        // t=7: 任务2,3,4都到达，选择burst最短的: 任务3 (burst=1), 然后任务2和4都是4，按到达顺序
        // 执行顺序: 1, 3, 2, 4
        
        assert!(result.tasks[0].completion_time == Some(7)); // 任务1
        assert!(result.tasks[2].completion_time == Some(8)); // 任务3
    }

    #[test]
    fn test_srtf_preemptive() {
        let scheduler = SjfScheduler::new(true);
        let tasks = vec![
            Task::new(1, 0, 7, None),
            Task::new(2, 2, 4, None),
            Task::new(3, 4, 1, None),
            Task::new(4, 5, 4, None),
        ];

        let result = scheduler.schedule(&tasks);

        // 抢占式 SJF (SRTF) 执行顺序:
        // t=0: 任务1开始 (remaining=7)
        // t=2: 任务2到达 (burst=4 < 5=remaining of task1)，抢占！
        // t=4: 任务3到达 (burst=1 < 2=remaining of task2)，抢占！
        // 任务3执行完成，然后继续任务2，最后任务4和任务1
        
        // 任务3应该先完成
        assert!(result.tasks[2].completion_time <= Some(5)); // 任务3在t=5前完成
    }

    #[test]
    fn test_sjf_vs_srtf_efficiency() {
        // SRTF 应该比 SJF 有更好的平均等待时间
        let tasks = vec![
            Task::new(1, 0, 8, None),
            Task::new(2, 1, 4, None),
            Task::new(3, 2, 2, None),
        ];

        let sjf = SjfScheduler::new(false).schedule(&tasks);
        let srtf = SjfScheduler::new(true).schedule(&tasks);

        // SRTF 的平均等待时间应该小于等于 SJF
        assert!(
            srtf.metrics.avg_waiting_time <= sjf.metrics.avg_waiting_time,
            "SRTF should have better or equal avg waiting time than SJF"
        );
    }

    #[test]
    fn test_sjf_starvation() {
        // 测试饥饿情况：持续有短任务到达，长任务可能一直等待
        let scheduler = SjfScheduler::new(true);
        let tasks = vec![
            Task::new(1, 0, 100, None), // 长任务
            Task::new(2, 1, 1, None),   // 短任务
            Task::new(3, 2, 1, None),   // 短任务
            Task::new(4, 3, 1, None),   // 短任务
        ];

        let result = scheduler.schedule(&tasks);
        
        // 所有任务最终都应该完成
        assert!(result.tasks.iter().all(|t| t.is_completed()));
        
        // 但长任务的等待时间应该很长
        let long_task = &result.tasks[0];
        assert!(long_task.waiting_time >= 3); // 至少等待了3个短任务
    }
}
