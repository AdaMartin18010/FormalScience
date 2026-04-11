//! 性能指标模块
//! 
//! 提供 CPU 调度算法的性能评估指标计算和统计功能。

use crate::tasks::{Task, TimeUnit};
use std::fmt;

/// 调度性能指标结构体
/// 
/// 包含评估调度算法性能的各项指标
#[derive(Debug, Clone, Copy, Default)]
pub struct Metrics {
    /// 平均周转时间
    pub avg_turnaround_time: f64,
    /// 平均等待时间
    pub avg_waiting_time: f64,
    /// 平均响应时间
    pub avg_response_time: f64,
    /// 吞吐量（单位时间内完成的任务数）
    pub throughput: f64,
    /// CPU 利用率（百分比）
    pub cpu_utilization: f64,
    /// 总模拟时间
    pub total_time: TimeUnit,
    /// 完成的任务数量
    pub completed_tasks: usize,
}

impl Metrics {
    /// 从任务列表计算所有指标
    /// 
    /// # 参数
    /// - `tasks`: 已完成调度的任务列表
    /// - `total_time`: 模拟运行的总时间
    /// - `cpu_busy_time`: CPU 实际工作的时间
    /// 
    /// # 返回
    /// 计算好的 Metrics 实例
    pub fn calculate(
        tasks: &[Task],
        total_time: TimeUnit,
        cpu_busy_time: TimeUnit,
    ) -> Self {
        let n = tasks.len() as f64;
        if n == 0.0 {
            return Metrics::default();
        }

        // 计算各项时间的总和
        let total_turnaround: TimeUnit = tasks
            .iter()
            .filter_map(|t| t.turnaround_time())
            .sum();
        
        let total_waiting: TimeUnit = tasks
            .iter()
            .map(|t| t.waiting_time)
            .sum();
        
        let total_response: TimeUnit = tasks
            .iter()
            .filter_map(|t| t.response_time())
            .sum();

        // 计算平均值
        let avg_turnaround = total_turnaround as f64 / n;
        let avg_waiting = total_waiting as f64 / n;
        let avg_response = total_response as f64 / n;

        // 计算吞吐量和 CPU 利用率
        let throughput = if total_time > 0 {
            tasks.len() as f64 / total_time as f64
        } else {
            0.0
        };

        let cpu_utilization = if total_time > 0 {
            (cpu_busy_time as f64 / total_time as f64) * 100.0
        } else {
            0.0
        };

        Metrics {
            avg_turnaround_time: avg_turnaround,
            avg_waiting_time: avg_waiting,
            avg_response_time: avg_response,
            throughput,
            cpu_utilization,
            total_time,
            completed_tasks: tasks.len(),
        }
    }

    /// 快速计算指标（假设 CPU 一直在工作）
    pub fn calculate_simple(tasks: &[Task], total_time: TimeUnit) -> Self {
        Self::calculate(tasks, total_time, total_time)
    }

    /// 以表格形式打印指标
    pub fn print_table(&self) {
        println!("\n{:=^50}", " 性能指标 ");
        println!("{:<25} {:>20}", "指标", "数值");
        println!("{:-<50}", "");
        println!("{:<25} {:>20.2}", "平均周转时间", self.avg_turnaround_time);
        println!("{:<25} {:>20.2}", "平均等待时间", self.avg_waiting_time);
        println!("{:<25} {:>20.2}", "平均响应时间", self.avg_response_time);
        println!("{:<25} {:>20.4}", "吞吐量 (任务/时间)", self.throughput);
        println!("{:<25} {:>19.2}%", "CPU 利用率", self.cpu_utilization);
        println!("{:<25} {:>20}", "总模拟时间", self.total_time);
        println!("{:<25} {:>20}", "完成任务数", self.completed_tasks);
        println!("{:=<50}\n", "");
    }
}

impl fmt::Display for Metrics {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Metrics {{ avg_turnaround: {:.2}, avg_waiting: {:.2}, avg_response: {:.2}, throughput: {:.4}, cpu_util: {:.2}% }}",
            self.avg_turnaround_time,
            self.avg_waiting_time,
            self.avg_response_time,
            self.throughput,
            self.cpu_utilization
        )
    }
}

/// 甘特图条目
#[derive(Debug, Clone)]
pub struct GanttEntry {
    /// 任务 ID（None 表示 CPU 空闲）
    pub task_id: Option<u32>,
    /// 开始时间
    pub start_time: TimeUnit,
    /// 结束时间
    pub end_time: TimeUnit,
}

impl GanttEntry {
    /// 创建一个新的甘特图条目
    pub fn new(task_id: Option<u32>, start_time: TimeUnit, end_time: TimeUnit) -> Self {
        GanttEntry {
            task_id,
            start_time,
            end_time,
        }
    }

    /// 获取持续时间
    pub fn duration(&self) -> TimeUnit {
        self.end_time.saturating_sub(self.start_time)
    }
}

/// 甘特图结构体
/// 
/// 用于可视化展示调度过程
#[derive(Debug, Clone, Default)]
pub struct GanttChart {
    /// 调度条目列表
    pub entries: Vec<GanttEntry>,
}

impl GanttChart {
    /// 创建一个新的空甘特图
    pub fn new() -> Self {
        GanttChart { entries: Vec::new() }
    }

    /// 添加一个条目
    pub fn add_entry(&mut self, entry: GanttEntry) {
        self.entries.push(entry);
    }

    /// 添加一个任务执行记录
    pub fn add_task(&mut self, task_id: u32, start_time: TimeUnit, end_time: TimeUnit) {
        self.add_entry(GanttEntry::new(Some(task_id), start_time, end_time));
    }

    /// 添加一个空闲时间段
    pub fn add_idle(&mut self, start_time: TimeUnit, end_time: TimeUnit) {
        self.add_entry(GanttEntry::new(None, start_time, end_time));
    }

    /// 计算总时间跨度
    pub fn total_span(&self) -> TimeUnit {
        if let Some(last) = self.entries.last() {
            last.end_time
        } else {
            0
        }
    }

    /// 计算 CPU 空闲时间
    pub fn idle_time(&self) -> TimeUnit {
        self.entries
            .iter()
            .filter(|e| e.task_id.is_none())
            .map(|e| e.duration())
            .sum()
    }

    /// 计算 CPU 工作时间
    pub fn busy_time(&self) -> TimeUnit {
        self.entries
            .iter()
            .filter(|e| e.task_id.is_some())
            .map(|e| e.duration())
            .sum()
    }

    /// 以 ASCII 艺术形式打印甘特图
    pub fn print(&self) {
        if self.entries.is_empty() {
            println!("(空甘特图)");
            return;
        }

        println!("\n甘特图:");
        println!("{}", "=".repeat(60));

        // 打印时间轴
        print!("Time:    ");
        for entry in &self.entries {
            print!("{:4}", entry.start_time);
        }
        println!();

        // 打印任务条
        print!("Task:    ");
        for entry in &self.entries {
            let symbol = match entry.task_id {
                Some(id) => format!("[T{}]", id),
                None => "[IDLE]".to_string(),
            };
            print!("{:<4}", symbol);
        }
        println!();

        // 打印分隔线
        print!("         ");
        for _ in &self.entries {
            print!("|   ");
        }
        println!();

        // 打印可视化条
        print!("         ");
        for entry in &self.entries {
            let ch = match entry.task_id {
                Some(id) => char::from_digit(id % 10, 10).unwrap_or('#'),
                None => '.',
            };
            let bar: String = std::iter::repeat(ch)
                .take(entry.duration() as usize * 2)
                .collect();
            print!("{:<4}", bar);
        }
        println!();

        // 打印结束时间
        if let Some(last) = self.entries.last() {
            println!("End:     {}", last.end_time);
        }

        println!("{}", "=".repeat(60));

        // 打印图例
        println!("图例: [T#] = 任务执行, [IDLE] = CPU 空闲, . = 空闲时间段");
    }

    /// 以紧凑形式打印甘特图
    pub fn print_compact(&self) {
        if self.entries.is_empty() {
            return;
        }

        print!("调度序列: ");
        for entry in &self.entries {
            match entry.task_id {
                Some(id) => print!("T{}({}-{}) ", id, entry.start_time, entry.end_time),
                None => print!("IDLE({}-{}) ", entry.start_time, entry.end_time),
            }
        }
        println!();
    }
}

/// 调度结果结构体
/// 
/// 包含调度后的完整结果
#[derive(Debug, Clone)]
pub struct ScheduleResult {
    /// 完成的任务列表
    pub tasks: Vec<Task>,
    /// 甘特图
    pub gantt_chart: GanttChart,
    /// 性能指标
    pub metrics: Metrics,
}

impl ScheduleResult {
    /// 打印完整的调度结果
    pub fn print(&self) {
        self.gantt_chart.print();
        self.metrics.print_table();
        
        // 打印每个任务的详细统计
        println!("\n任务详细统计:");
        println!("{:-<60}", "");
        println!(
            "{:<5} {:<10} {:<10} {:<10} {:<10} {:<10}",
            "ID", "到达", "执行", "完成", "周转", "等待"
        );
        println!("{:-<60}", "");
        
        for task in &self.tasks {
            let turnaround = task.turnaround_time().unwrap_or(0);
            println!(
                "{:<5} {:<10} {:<10} {:<10} {:<10} {:<10}",
                task.id,
                task.arrival_time,
                task.burst_time,
                task.completion_time.unwrap_or(0),
                turnaround,
                task.waiting_time
            );
        }
        println!("{:-<60}", "");
    }
}

/// 比较不同调度算法的指标
pub fn compare_metrics(results: &[(String, Metrics)]) {
    println!("\n{:=^80}", " 调度算法性能比较 ");
    println!(
        "{:<20} {:>12} {:>12} {:>12} {:>12} {:>12}",
        "算法", "周转时间", "等待时间", "响应时间", "吞吐量", "CPU利用率"
    );
    println!("{:-<80}", "");
    
    for (name, metrics) in results {
        println!(
            "{:<20} {:>12.2} {:>12.2} {:>12.2} {:>12.4} {:>11.1}%",
            name,
            metrics.avg_turnaround_time,
            metrics.avg_waiting_time,
            metrics.avg_response_time,
            metrics.throughput,
            metrics.cpu_utilization
        );
    }
    println!("{:=<80}\n", "");
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tasks::Task;

    #[test]
    fn test_metrics_calculation() {
        let tasks = vec![
            Task {
                id: 1,
                arrival_time: 0,
                burst_time: 5,
                priority: 0,
                state: crate::tasks::TaskState::Completed,
                remaining_time: 0,
                first_run_time: Some(0),
                completion_time: Some(5),
                waiting_time: 0,
                last_ready_time: 0,
            },
            Task {
                id: 2,
                arrival_time: 1,
                burst_time: 3,
                priority: 0,
                state: crate::tasks::TaskState::Completed,
                remaining_time: 0,
                first_run_time: Some(5),
                completion_time: Some(8),
                waiting_time: 1,
                last_ready_time: 0,
            },
        ];

        let metrics = Metrics::calculate_simple(&tasks, 8);
        
        // 任务1: turnaround = 5, waiting = 0, response = 0
        // 任务2: turnaround = 7, waiting = 1, response = 4
        // 平均: turnaround = 6, waiting = 0.5, response = 2
        assert_eq!(metrics.avg_turnaround_time, 6.0);
        assert_eq!(metrics.avg_waiting_time, 0.5);
        assert_eq!(metrics.avg_response_time, 2.0);
    }

    #[test]
    fn test_gantt_chart() {
        let mut chart = GanttChart::new();
        chart.add_task(1, 0, 5);
        chart.add_idle(5, 7);
        chart.add_task(2, 7, 10);

        assert_eq!(chart.total_span(), 10);
        assert_eq!(chart.idle_time(), 2);
        assert_eq!(chart.busy_time(), 8);
    }
}
