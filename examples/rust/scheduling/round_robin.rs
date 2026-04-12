/// 轮转调度算法（Round Robin Scheduling）实现
/// 
/// 轮转调度是一种基于时间片的进程调度算法，每个进程获得相等的时间片来执行。
/// 当时间片用完时，进程被放到队列末尾等待下一次调度。

use std::collections::VecDeque;
use std::fmt::Debug;

/// 表示一个进程
#[derive(Debug, Clone)]
pub struct Process {
    /// 进程ID
    pub id: u32,
    /// 进程名称
    pub name: String,
    /// 剩余执行时间
    pub remaining_time: u32,
    /// 进程优先级（可选，用于优先级轮转）
    pub priority: u8,
}

impl Process {
    /// 创建新进程
    pub fn new(id: u32, name: &str, total_time: u32) -> Self {
        Self {
            id,
            name: name.to_string(),
            remaining_time: total_time,
            priority: 0,
        }
    }

    /// 创建带优先级的进程
    pub fn with_priority(id: u32, name: &str, total_time: u32, priority: u8) -> Self {
        Self {
            id,
            name: name.to_string(),
            remaining_time: total_time,
            priority,
        }
    }
}

/// 轮转调度器
pub struct RoundRobinScheduler {
    /// 就绪队列
    ready_queue: VecDeque<Process>,
    /// 时间片大小（毫秒）
    time_quantum: u32,
    /// 当前时间
    current_time: u32,
    /// 完成的进程列表
    completed_processes: Vec<Process>,
}

impl RoundRobinScheduler {
    /// 创建新的轮转调度器
    pub fn new(time_quantum: u32) -> Self {
        Self {
            ready_queue: VecDeque::new(),
            time_quantum,
            current_time: 0,
            completed_processes: Vec::new(),
        }
    }

    /// 添加进程到就绪队列
    pub fn add_process(&mut self, process: Process) {
        self.ready_queue.push_back(process);
    }

    /// 执行一轮调度
    pub fn tick(&mut self) -> Option<Process> {
        if let Some(mut process) = self.ready_queue.pop_front() {
            // 计算实际执行时间
            let exec_time = std::cmp::min(self.time_quantum, process.remaining_time);
            
            // 更新进程状态
            process.remaining_time -= exec_time;
            self.current_time += exec_time;
            
            println!(
                "时间 [{}-{}]: 执行进程 {} ({})，执行 {}ms，剩余 {}ms",
                self.current_time - exec_time,
                self.current_time,
                process.id,
                process.name,
                exec_time,
                process.remaining_time
            );
            
            // 如果进程未完成，放回队列末尾
            if process.remaining_time > 0 {
                self.ready_queue.push_back(process);
                None
            } else {
                println!("  -> 进程 {} 完成！", process.id);
                self.completed_processes.push(process.clone());
                Some(process)
            }
        } else {
            None
        }
    }

    /// 运行调度直到所有进程完成
    pub fn run(&mut self) -> Vec<Process> {
        println!("\n=== 开始轮转调度（时间片={}ms）===", self.time_quantum);
        
        while !self.ready_queue.is_empty() {
            self.tick();
        }
        
        println!("\n=== 所有进程执行完成 ===");
        println!("总耗时: {}ms", self.current_time);
        
        self.completed_processes.clone()
    }

    /// 获取就绪队列长度
    pub fn queue_len(&self) -> usize {
        self.ready_queue.len()
    }

    /// 检查是否还有进程待执行
    pub fn has_processes(&self) -> bool {
        !self.ready_queue.is_empty()
    }
}

/// 多级反馈队列调度器
pub struct MultilevelFeedbackQueue {
    /// 多个优先级队列
    queues: Vec<VecDeque<Process>>,
    /// 每个队列的时间片（逐级递增）
    time_quantums: Vec<u32>,
    /// 当前时间
    current_time: u32,
}

impl MultilevelFeedbackQueue {
    /// 创建多级反馈队列
    pub fn new(levels: usize) -> Self {
        let mut queues = Vec::with_capacity(levels);
        let mut time_quantums = Vec::with_capacity(levels);
        
        for i in 0..levels {
            queues.push(VecDeque::new());
            // 时间片逐级翻倍
            time_quantums.push(10 * (1 << i) as u32);
        }
        
        Self {
            queues,
            time_quantums,
            current_time: 0,
        }
    }

    /// 添加进程到最高优先级队列
    pub fn add_process(&mut self, process: Process) {
        if !self.queues.is_empty() {
            self.queues[0].push_back(process);
        }
    }

    /// 执行一轮调度
    pub fn tick(&mut self) -> Option<Process> {
        // 从最高优先级队列开始查找
        for level in 0..self.queues.len() {
            if let Some(mut process) = self.queues[level].pop_front() {
                let time_quantum = self.time_quantums[level];
                let exec_time = std::cmp::min(time_quantum, process.remaining_time);
                
                process.remaining_time -= exec_time;
                self.current_time += exec_time;
                
                println!(
                    "时间 [{}-{}]: 队列{} 执行进程 {}，执行 {}ms，剩余 {}ms",
                    self.current_time - exec_time,
                    self.current_time,
                    level,
                    process.id,
                    exec_time,
                    process.remaining_time
                );
                
                if process.remaining_time > 0 {
                    // 未完成，降低优先级
                    let next_level = std::cmp::min(level + 1, self.queues.len() - 1);
                    self.queues[next_level].push_back(process);
                } else {
                    println!("  -> 进程 {} 完成！", process.id);
                    return Some(process);
                }
                
                return None;
            }
        }
        
        None
    }

    /// 运行调度
    pub fn run(&mut self) -> u32 {
        println!("\n=== 开始多级反馈队列调度 ===");
        
        while self.has_processes() {
            self.tick();
        }
        
        println!("\n=== 所有进程执行完成 ===");
        println!("总耗时: {}ms", self.current_time);
        
        self.current_time
    }

    /// 检查是否还有进程
    fn has_processes(&self) -> bool {
        self.queues.iter().any(|q| !q.is_empty())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_round_robin() {
        let mut scheduler = RoundRobinScheduler::new(20);
        
        scheduler.add_process(Process::new(1, "进程A", 50));
        scheduler.add_process(Process::new(2, "进程B", 30));
        scheduler.add_process(Process::new(3, "进程C", 40));
        
        let completed = scheduler.run();
        assert_eq!(completed.len(), 3);
    }

    #[test]
    fn test_multilevel_feedback_queue() {
        let mut scheduler = MultilevelFeedbackQueue::new(3);
        
        scheduler.add_process(Process::new(1, "进程A", 100));
        scheduler.add_process(Process::new(2, "进程B", 50));
        scheduler.add_process(Process::new(3, "进程C", 30));
        
        let total_time = scheduler.run();
        assert!(total_time > 0);
    }
}

/// 主函数示例
fn main() {
    // 轮转调度示例
    let mut rr_scheduler = RoundRobinScheduler::new(20);
    rr_scheduler.add_process(Process::new(1, "浏览器", 50));
    rr_scheduler.add_process(Process::new(2, "编辑器", 30));
    rr_scheduler.add_process(Process::new(3, "音乐播放器", 40));
    rr_scheduler.run();

    // 多级反馈队列示例
    let mut mlfq = MultilevelFeedbackQueue::new(3);
    mlfq.add_process(Process::new(4, "交互式应用", 25));
    mlfq.add_process(Process::new(5, "批处理任务", 80));
    mlfq.add_process(Process::new(6, "后台服务", 60));
    mlfq.run();
}
