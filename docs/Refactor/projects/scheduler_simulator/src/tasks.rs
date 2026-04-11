//! 任务定义模块
//! 
//! 定义了 CPU 调度中的基本任务结构，包括任务属性、状态和统计信息。

use std::fmt;

/// 任务的唯一标识符类型
pub type TaskId = u32;

/// 任务优先级类型（数值越小优先级越高）
pub type Priority = u32;

/// 时间单位类型
pub type TimeUnit = u32;

/// 任务状态枚举
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TaskState {
    /// 新创建，等待调度
    New,
    /// 在就绪队列中等待
    Ready,
    /// 正在运行
    Running,
    /// 等待 I/O 或其他事件
    Waiting,
    /// 已完成
    Completed,
}

impl fmt::Display for TaskState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TaskState::New => write!(f, "NEW"),
            TaskState::Ready => write!(f, "READY"),
            TaskState::Running => write!(f, "RUNNING"),
            TaskState::Waiting => write!(f, "WAITING"),
            TaskState::Completed => write!(f, "COMPLETED"),
        }
    }
}

/// CPU 任务结构体
/// 
/// 表示一个需要在 CPU 上执行的任务，包含任务的基本属性和运行时状态。
#[derive(Debug, Clone)]
pub struct Task {
    /// 任务唯一标识符
    pub id: TaskId,
    /// 任务到达时间（系统启动后的时间单位）
    pub arrival_time: TimeUnit,
    /// 任务需要的 CPU 时间总量
    pub burst_time: TimeUnit,
    /// 任务优先级（数值越小优先级越高，0 为最高优先级）
    pub priority: Priority,
    /// 当前任务状态
    pub state: TaskState,
    
    // 运行时状态（由调度器维护）
    /// 剩余需要执行的 CPU 时间
    pub remaining_time: TimeUnit,
    /// 任务首次获得 CPU 的时间
    pub first_run_time: Option<TimeUnit>,
    /// 任务完成时间
    pub completion_time: Option<TimeUnit>,
    /// 任务在就绪队列中累计等待的时间
    pub waiting_time: TimeUnit,
    /// 任务最后一次被调度的时间（用于计算等待时间）
    pub last_ready_time: TimeUnit,
}

impl Task {
    /// 创建一个新任务
    /// 
    /// # 参数
    /// - `id`: 任务唯一标识符
    /// - `arrival_time`: 到达时间
    /// - `burst_time`: 需要的 CPU 时间
    /// - `priority`: 优先级（可选，默认为 0）
    /// 
    /// # 示例
    /// ```
    /// let task = Task::new(1, 0, 10, Some(1));
    /// ```
    pub fn new(
        id: TaskId,
        arrival_time: TimeUnit,
        burst_time: TimeUnit,
        priority: Option<Priority>,
    ) -> Self {
        Task {
            id,
            arrival_time,
            burst_time,
            priority: priority.unwrap_or(0),
            state: TaskState::New,
            remaining_time: burst_time,
            first_run_time: None,
            completion_time: None,
            waiting_time: 0,
            last_ready_time: arrival_time,
        }
    }

    /// 检查任务是否已完成
    pub fn is_completed(&self) -> bool {
        self.state == TaskState::Completed || self.remaining_time == 0
    }

    /// 检查任务是否已到达（给定当前时间）
    pub fn has_arrived(&self, current_time: TimeUnit) -> bool {
        self.arrival_time <= current_time
    }

    /// 任务执行一个时间单位
    /// 
    /// # 参数
    /// - `current_time`: 当前系统时间
    /// 
    /// # 返回
    /// - `true`: 任务在本次执行后完成
    /// - `false`: 任务仍需继续执行
    pub fn execute(&mut self, current_time: TimeUnit) -> bool {
        // 如果是首次运行，记录响应时间
        if self.first_run_time.is_none() {
            self.first_run_time = Some(current_time);
            self.state = TaskState::Running;
        }

        // 执行一个时间单位
        if self.remaining_time > 0 {
            self.remaining_time -= 1;
        }

        // 检查是否完成
        if self.remaining_time == 0 {
            self.state = TaskState::Completed;
            self.completion_time = Some(current_time + 1);
            true
        } else {
            false
        }
    }

    /// 将任务标记为就绪状态
    /// 
    /// # 参数
    /// - `current_time`: 当前系统时间，用于计算后续等待时间
    pub fn mark_ready(&mut self, current_time: TimeUnit) {
        if self.state != TaskState::Ready {
            self.state = TaskState::Ready;
            self.last_ready_time = current_time;
        }
    }

    /// 将任务标记为运行状态
    pub fn mark_running(&mut self) {
        self.state = TaskState::Running;
    }

    /// 将任务标记为等待状态
    pub fn mark_waiting(&mut self) {
        self.state = TaskState::Waiting;
    }

    /// 更新等待时间（当任务从就绪队列被调度时调用）
    /// 
    /// # 参数
    /// - `current_time`: 当前系统时间
    pub fn update_waiting_time(&mut self, current_time: TimeUnit) {
        if self.state == TaskState::Ready {
            let waited = current_time.saturating_sub(self.last_ready_time);
            self.waiting_time += waited;
        }
    }

    /// 计算周转时间（任务完成时间 - 到达时间）
    /// 
    /// # 返回
    /// - `Some(turnaround_time)`: 如果任务已完成
    /// - `None`: 如果任务尚未完成
    pub fn turnaround_time(&self) -> Option<TimeUnit> {
        self.completion_time.map(|ct| ct.saturating_sub(self.arrival_time))
    }

    /// 计算响应时间（首次运行时间 - 到达时间）
    /// 
    /// # 返回
    /// - `Some(response_time)`: 如果任务已开始执行
    /// - `None`: 如果任务尚未开始执行
    pub fn response_time(&self) -> Option<TimeUnit> {
        self.first_run_time.map(|frt| frt.saturating_sub(self.arrival_time))
    }

    /// 重置任务状态（用于重新运行模拟）
    pub fn reset(&mut self) {
        self.state = TaskState::New;
        self.remaining_time = self.burst_time;
        self.first_run_time = None;
        self.completion_time = None;
        self.waiting_time = 0;
        self.last_ready_time = self.arrival_time;
    }
}

impl fmt::Display for Task {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Task {}: arrival={}, burst={}, priority={}, state={}",
            self.id, self.arrival_time, self.burst_time, self.priority, self.state
        )
    }
}

/// 任务列表辅助函数
pub mod utils {
    use super::*;

    /// 创建一组测试任务
    pub fn create_sample_tasks() -> Vec<Task> {
        vec![
            Task::new(1, 0, 8, Some(3)),
            Task::new(2, 1, 4, Some(1)),
            Task::new(3, 2, 9, Some(2)),
            Task::new(4, 3, 5, Some(4)),
            Task::new(5, 4, 2, Some(5)),
        ]
    }

    /// 创建另一组测试任务（用于 SJF 演示）
    pub fn create_sjf_tasks() -> Vec<Task> {
        vec![
            Task::new(1, 0, 7, None),
            Task::new(2, 2, 4, None),
            Task::new(3, 4, 1, None),
            Task::new(4, 5, 4, None),
        ]
    }

    /// 创建优先级调度测试任务
    pub fn create_priority_tasks() -> Vec<Task> {
        vec![
            Task::new(1, 0, 10, Some(3)),
            Task::new(2, 0, 1, Some(1)),
            Task::new(3, 0, 2, Some(4)),
            Task::new(4, 0, 1, Some(5)),
            Task::new(5, 0, 5, Some(2)),
        ]
    }

    /// 打印任务列表
    pub fn print_tasks(tasks: &[Task]) {
        println!("任务列表:");
        println!("{:-<50}", "");
        println!("{:<5} {:<10} {:<10} {:<10} {:<10}", 
                 "ID", "Arrival", "Burst", "Priority", "State");
        println!("{:-<50}", "");
        for task in tasks {
            println!("{:<5} {:<10} {:<10} {:<10} {:<10}",
                task.id, task.arrival_time, task.burst_time, 
                task.priority, task.state);
        }
        println!("{:-<50}", "");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_task_creation() {
        let task = Task::new(1, 0, 10, Some(1));
        assert_eq!(task.id, 1);
        assert_eq!(task.arrival_time, 0);
        assert_eq!(task.burst_time, 10);
        assert_eq!(task.priority, 1);
        assert_eq!(task.remaining_time, 10);
        assert!(!task.is_completed());
    }

    #[test]
    fn test_task_execution() {
        let mut task = Task::new(1, 0, 3, None);
        
        // 第一次执行
        assert!(!task.execute(0));
        assert_eq!(task.remaining_time, 2);
        assert_eq!(task.first_run_time, Some(0));
        
        // 第二次执行
        assert!(!task.execute(1));
        assert_eq!(task.remaining_time, 1);
        
        // 第三次执行 - 完成
        assert!(task.execute(2));
        assert_eq!(task.remaining_time, 0);
        assert!(task.is_completed());
        assert_eq!(task.completion_time, Some(3));
    }

    #[test]
    fn test_turnaround_time() {
        let mut task = Task::new(1, 2, 5, None);
        // 模拟任务执行
        task.first_run_time = Some(2);
        task.completion_time = Some(10);
        
        assert_eq!(task.turnaround_time(), Some(8)); // 10 - 2 = 8
    }

    #[test]
    fn test_response_time() {
        let mut task = Task::new(1, 2, 5, None);
        task.first_run_time = Some(4);
        
        assert_eq!(task.response_time(), Some(2)); // 4 - 2 = 2
    }

    #[test]
    fn test_task_reset() {
        let mut task = Task::new(1, 0, 5, None);
        task.execute(0);
        task.execute(1);
        task.reset();
        
        assert_eq!(task.remaining_time, 5);
        assert_eq!(task.state, TaskState::New);
        assert!(task.first_run_time.is_none());
        assert!(task.completion_time.is_none());
    }
}
