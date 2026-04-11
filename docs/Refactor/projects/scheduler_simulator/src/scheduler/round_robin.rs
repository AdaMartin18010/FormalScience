//! Round Robin (RR) 调度器
//! 
//! 时间片轮转调度算法：每个任务分配一个固定的时间片（quantum），
//! 轮流执行，时间片用完就放到队列末尾。
//! 
//! 特点：
//! - 抢占式（基于时间片）
//! - 公平性好，响应时间可预测
//! - 时间片大小很重要：太大变成 FCFS，太小上下文切换开销大
//! - 常用于分时系统

use crate::metrics::ScheduleResult;
use crate::scheduler::{clone_and_reset_tasks, all_tasks_completed, next_arrival_time, Scheduler, SchedulerContext, ScheduleResultBuilder};
use crate::tasks::{Task, TaskState, TimeUnit};
use std::collections::VecDeque;

/// Round Robin 调度器
#[derive(Debug, Clone)]
pub struct RoundRobinScheduler {
    /// 时间片大小
    quantum: TimeUnit,
}

impl RoundRobinScheduler {
    /// 创建新的 Round Robin 调度器
    /// 
    /// # 参数
    /// - `quantum`: 时间片大小，决定每个任务每次能执行多长时间
    /// 
    /// # 建议
    /// - 时间片通常设置为 10-100ms
    /// - 应大于典型的上下文切换时间（通常 < 10μs）
    pub fn new(quantum: TimeUnit) -> Self {
        RoundRobinScheduler { quantum }
    }

    /// 获取时间片大小
    pub fn quantum(&self) -> TimeUnit {
        self.quantum
    }

    /// 设置时间片大小
    pub fn set_quantum(&mut self, quantum: TimeUnit) {
        self.quantum = quantum;
    }
}

impl Default for RoundRobinScheduler {
    fn default() -> Self {
        Self::new(2) // 默认时间片为2
    }
}

impl Scheduler for RoundRobinScheduler {
    fn schedule(&self, tasks: &[Task]) -> ScheduleResult {
        let mut tasks = clone_and_reset_tasks(tasks);
        let mut context = SchedulerContext::new();
        let mut ready_queue: VecDeque<usize> = VecDeque::new();
        let mut last_arrival_check: TimeUnit = 0;

        while !all_tasks_completed(&tasks) {
            // 添加新到达的任务到就绪队列
            for (idx, task) in tasks.iter().enumerate() {
                if task.arrival_time <= context.current_time 
                    && task.arrival_time > last_arrival_check
                    && !task.is_completed()
                    && !ready_queue.contains(&idx) {
                    ready_queue.push_back(idx);
                }
            }
            last_arrival_check = context.current_time;

            match ready_queue.pop_front() {
                Some(idx) => {
                    let task = &mut tasks[idx];
                    
                    // 更新等待时间
                    task.update_waiting_time(context.current_time);
                    task.mark_running();
                    
                    if task.first_run_time.is_none() {
                        task.first_run_time = Some(context.current_time);
                    }

                    // 确定本次执行的时间（取时间片和剩余时间的最小值）
                    let execute_time = std::cmp::min(self.quantum, task.remaining_time);

                    // 执行任务
                    for _t in 0..execute_time {
                        task.execute(context.current_time);
                        context.advance_time(1);
                        last_arrival_check = context.current_time;
                    }

                    context.record_execution(task.id, execute_time);

                    if task.is_completed() {
                        context.mark_completed();
                    } else {
                        // 时间片用完，任务未完成，放回队列末尾
                        task.mark_ready(context.current_time);
                        ready_queue.push_back(idx);
                    }
                }
                None => {
                    // 就绪队列为空，CPU 空闲
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
        "Round Robin"
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_round_robin_basic() {
        let scheduler = RoundRobinScheduler::new(2);
        let tasks = vec![
            Task::new(1, 0, 5, None),
            Task::new(2, 1, 3, None),
            Task::new(3, 2, 1, None),
        ];

        let result = scheduler.schedule(&tasks);

        // Round Robin (q=2) 执行顺序:
        // t=0: 任务1执行2单位 (remaining: 3)
        // t=2: 任务2执行2单位 (remaining: 1)
        // t=4: 任务3执行1单位完成
        // t=5: 任务1执行2单位 (remaining: 1)
        // t=7: 任务2执行1单位完成
        // t=8: 任务1执行1单位完成

        assert!(result.tasks.iter().all(|t| t.is_completed()));
        
        // 任务3应该最先完成（它最短）
        assert_eq!(result.tasks[2].completion_time, Some(5));
    }

    #[test]
    fn test_round_robin_context_switching() {
        // 测试频繁的上下文切换
        let scheduler = RoundRobinScheduler::new(1); // 时间片为1，频繁切换
        let tasks = vec![
            Task::new(1, 0, 3, None),
            Task::new(2, 0, 3, None),
            Task::new(3, 0, 3, None),
        ];

        let result = scheduler.schedule(&tasks);

        // 严格轮转，每个任务每次执行1单位
        // 所有任务应该都完成
        assert!(result.tasks.iter().all(|t| t.is_completed()));
        
        // 总甘特图条目数应该很多（每次执行都记录）
        assert!(result.gantt_chart.entries.len() >= 9); // 至少9次执行
    }

    #[test]
    fn test_round_robin_fairness() {
        // 测试公平性：同时到达的任务应该获得相等的 CPU 时间
        let scheduler = RoundRobinScheduler::new(2);
        let tasks = vec![
            Task::new(1, 0, 6, None),
            Task::new(2, 0, 6, None),
        ];

        let result = scheduler.schedule(&tasks);

        // 两个任务同时到达，相同执行时间，应该同时完成
        assert_eq!(
            result.tasks[0].completion_time,
            result.tasks[1].completion_time
        );
    }

    #[test]
    fn test_round_robin_quantum_too_large() {
        // 如果时间片非常大，行为类似于 FCFS
        let scheduler = RoundRobinScheduler::new(100);
        let tasks = vec![
            Task::new(1, 0, 5, None),
            Task::new(2, 1, 3, None),
        ];

        let result = scheduler.schedule(&tasks);

        // 每个任务都能在时间片内完成，所以执行顺序是 1, 2
        assert_eq!(result.tasks[0].completion_time, Some(5));
        assert_eq!(result.tasks[1].completion_time, Some(8));
    }

    #[test]
    fn test_round_robin_response_time() {
        // Round Robin 应该有较好的响应时间
        let scheduler = RoundRobinScheduler::new(2);
        let tasks = vec![
            Task::new(1, 0, 10, None),
            Task::new(2, 1, 1, None),
        ];

        let result = scheduler.schedule(&tasks);

        // 任务2在 t=1 到达，在 t=2 开始执行（下一个时间片）
        // 所以响应时间应该是 1
        let task2_response = result.tasks[1].response_time();
        assert_eq!(task2_response, Some(1));
    }
}
