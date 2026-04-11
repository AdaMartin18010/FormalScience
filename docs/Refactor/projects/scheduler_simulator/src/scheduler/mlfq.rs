//! MLFQ (Multi-Level Feedback Queue) 调度器
//! 
//! 多级反馈队列调度算法：使用多个不同优先级的队列，
//! 任务根据行为在不同队列间移动。
//! 
//! 算法规则：
//! 1. 如果任务A的优先级 > 任务B的优先级，运行A（不运行B）
//! 2. 如果任务A的优先级 = 任务B的优先级，轮转运行A和B
//! 3. 任务进入系统时，放在最高优先级队列
//! 4. 任务用完时间片后，降低其优先级
//! 5. 经过一段时间等待后，提升任务的优先级（防止饥饿）
//! 
//! 特点：
//! - 结合了优先级调度和轮转调度的优点
//! - 自适应：I/O密集型任务保持高优先级，CPU密集型任务降低优先级
//! - 无需预先知道任务的执行时间
//! - 复杂的参数调优

use crate::metrics::ScheduleResult;
use crate::scheduler::{clone_and_reset_tasks, all_tasks_completed, next_arrival_time, Scheduler, SchedulerContext, ScheduleResultBuilder};
use crate::tasks::{Task, TaskState, TimeUnit};
use std::collections::VecDeque;

/// MLFQ 调度器
#[derive(Debug, Clone)]
pub struct MlfqScheduler {
    /// 每个队列的时间片大小（从最高优先级到最低优先级）
    quanta: Vec<TimeUnit>,
    /// 优先级提升时间（防止饥饿）
    boost_interval: Option<TimeUnit>,
}

impl MlfqScheduler {
    /// 创建新的 MLFQ 调度器
    /// 
    /// # 参数
    /// - `quanta`: 每个优先级队列的时间片大小，向量长度决定队列数量
    /// 
    /// # 示例
    /// ```
    /// // 3级队列，时间片分别为 2, 4, 8
    /// let scheduler = MlfqScheduler::new(vec![2, 4, 8]);
    /// ```
    pub fn new(quanta: Vec<TimeUnit>) -> Self {
        MlfqScheduler {
            quanta,
            boost_interval: None, // 可以设置优先级提升间隔
        }
    }

    /// 创建带优先级提升的 MLFQ 调度器
    pub fn with_boost(quanta: Vec<TimeUnit>, boost_interval: TimeUnit) -> Self {
        MlfqScheduler {
            quanta,
            boost_interval: Some(boost_interval),
        }
    }

    /// 获取队列数量
    pub fn num_queues(&self) -> usize {
        self.quanta.len()
    }

    /// 获取指定优先级队列的时间片
    fn get_quantum(&self, priority: usize) -> TimeUnit {
        if priority < self.quanta.len() {
            self.quanta[priority]
        } else {
            *self.quanta.last().unwrap_or(&1)
        }
    }
}

impl Default for MlfqScheduler {
    fn default() -> Self {
        // 默认3级反馈队列，时间片递增
        Self::new(vec![2, 4, 8])
    }
}

impl Scheduler for MlfqScheduler {
    fn schedule(&self, tasks: &[Task]) -> ScheduleResult {
        let mut tasks = clone_and_reset_tasks(tasks);
        let mut context = SchedulerContext::new();
        
        // 多级队列：每个队列存储任务索引
        let num_queues = self.num_queues();
        let mut queues: Vec<VecDeque<usize>> = (0..num_queues)
            .map(|_| VecDeque::new())
            .collect();
        
        // 记录每个任务当前的队列级别
        let mut task_levels: Vec<usize> = vec![0; tasks.len()];
        
        // 上次优先级提升时间
        let mut last_boost_time: TimeUnit = 0;
        
        // 上次检查到达时间
        let mut last_arrival_check: TimeUnit = 0;

        while !all_tasks_completed(&tasks) {
            // 检查并添加新到达的任务到最高优先级队列
            for (idx, task) in tasks.iter().enumerate() {
                if task.arrival_time <= context.current_time 
                    && task.arrival_time > last_arrival_check
                    && !task.is_completed() {
                    task_levels[idx] = 0; // 新任务进入最高优先级队列
                    if !queues[0].contains(&idx) {
                        queues[0].push_back(idx);
                    }
                }
            }
            last_arrival_check = context.current_time;

            // 检查优先级提升（防止饥饿）
            if let Some(boost_interval) = self.boost_interval {
                if context.current_time - last_boost_time >= boost_interval {
                    // 将所有未完成的任务提升到最高优先级队列
                    for (idx, task) in tasks.iter().enumerate() {
                        if !task.is_completed() && task_levels[idx] > 0 {
                            task_levels[idx] = 0;
                            if !queues[0].contains(&idx) {
                                queues[0].push_back(idx);
                            }
                        }
                    }
                    // 清空其他队列
                    for i in 1..queues.len() {
                        queues[i].clear();
                    }
                    last_boost_time = context.current_time;
                }
            }

            // 从最高优先级队列开始查找可执行的任务
            let mut found_task = None;
            for level in 0..num_queues {
                if let Some(&idx) = queues[level].front() {
                    found_task = Some((idx, level));
                    break;
                }
            }

            match found_task {
                Some((idx, level)) => {
                    queues[level].pop_front();
                    
                    // 获取当前队列的时间片
                    let quantum = self.get_quantum(level);
                    let execute_time = std::cmp::min(quantum, tasks[idx].remaining_time);

                    // 执行任务
                    for t in 0..execute_time {
                        tasks[idx].execute(context.current_time + t);
                        
                        // 执行过程中检查新到达的任务
                        for (idx2, task2) in tasks.iter().enumerate() {
                            if task2.arrival_time <= context.current_time + t + 1
                                && task2.arrival_time > last_arrival_check
                                && !task2.is_completed() {
                                task_levels[idx2] = 0;
                                if !queues[0].contains(&idx2) {
                                    queues[0].push_back(idx2);
                                }
                            }
                        }
                        last_arrival_check = context.current_time + t + 1;
                    }
                    
                    // 更新任务状态
                    tasks[idx].update_waiting_time(context.current_time);
                    tasks[idx].mark_running();
                    
                    if tasks[idx].first_run_time.is_none() {
                        tasks[idx].first_run_time = Some(context.current_time);
                    }
                    
                    context.advance_time(execute_time);
                    context.record_execution(tasks[idx].id, execute_time);

                    if tasks[idx].is_completed() {
                        context.mark_completed();
                    } else {
                        // 时间片用完，降低优先级
                        tasks[idx].mark_ready(context.current_time);
                        let new_level = (level + 1).min(num_queues - 1);
                        task_levels[idx] = new_level;
                        queues[new_level].push_back(idx);
                    }
                }
                None => {
                    // 所有队列为空，CPU 空闲
                    if let Some(next_arrival) = next_arrival_time(&tasks, context.current_time) {
                        let idle_duration = next_arrival - context.current_time;
                        context.record_idle(idle_duration);
                        last_arrival_check = context.current_time;
                    } else {
                        break;
                    }
                }
            }
        }

        ScheduleResultBuilder::new(tasks, context).build()
    }

    fn name(&self) -> &str {
        "MLFQ (Multi-Level Feedback Queue)"
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mlfq_basic() {
        let scheduler = MlfqScheduler::new(vec![2, 4, 8]);
        let tasks = vec![
            Task::new(1, 0, 10, None), // CPU密集型，会逐渐降低优先级
            Task::new(2, 0, 2, None),  // 短任务，在高优先级完成
        ];

        let result = scheduler.schedule(&tasks);

        // 所有任务完成
        assert!(result.tasks.iter().all(|t| t.is_completed()));
        
        // 短任务应该在高优先级完成
        assert!(result.tasks[1].completion_time <= Some(4));
    }

    #[test]
    fn test_mlfq_priority_demotion() {
        // 测试优先级降低机制
        let scheduler = MlfqScheduler::new(vec![2, 4]); // 2级队列，时间片为2和4
        let tasks = vec![
            Task::new(1, 0, 6, None), // 执行时间超过第一级队列的时间片
        ];

        let result = scheduler.schedule(&tasks);

        assert!(result.tasks[0].is_completed());
        // 总时间应该是6（不考虑其他任务）
        assert_eq!(result.gantt_chart.total_span(), 6);
    }

    #[test]
    fn test_mlfq_boost() {
        // 测试优先级提升机制
        let scheduler = MlfqScheduler::with_boost(vec![2, 4], 10);
        let tasks = vec![
            Task::new(1, 0, 20, None),
            Task::new(2, 1, 1, None),
            Task::new(3, 2, 1, None),
        ];

        let result = scheduler.schedule(&tasks);

        // 所有任务应该都能完成（没有饿死）
        assert!(result.tasks.iter().all(|t| t.is_completed()));
    }

    #[test]
    fn test_mlfq_io_bound_vs_cpu_bound() {
        // 模拟 I/O 密集型 vs CPU 密集型任务
        // I/O 密集型任务会频繁放弃 CPU，保持高优先级
        // CPU 密集型任务会一直执行直到时间片用完，降低优先级
        
        let scheduler = MlfqScheduler::new(vec![2, 4, 8]);
        let tasks = vec![
            Task::new(1, 0, 20, None), // CPU密集型
            Task::new(2, 0, 2, None),  // 短任务（类似I/O密集型）
            Task::new(3, 1, 2, None),  // 短任务
        ];

        let result = scheduler.schedule(&tasks);

        // 短任务应该先完成
        let short_completion = result.tasks[1].completion_time.max(result.tasks[2].completion_time);
        let long_completion = result.tasks[0].completion_time;
        
        assert!(short_completion < long_completion);
    }
}
