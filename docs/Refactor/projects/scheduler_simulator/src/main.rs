//! CPU Scheduler Simulator
//! 
//! 一个完整的 CPU 调度算法模拟器，支持多种经典调度算法：
//! - FCFS (First-Come-First-Served)
//! - SJF (Shortest Job First) / SRTF (Shortest Remaining Time First)
//! - Round Robin
//! - Priority Scheduling
//! - MLFQ (Multi-Level Feedback Queue)

mod scheduler;
mod tasks;
mod metrics;

use scheduler::*;
use tasks::{utils::*, Task};
use metrics::compare_metrics;

fn main() {
    print_banner();
    
    // 创建示例任务集
    let tasks = create_sample_tasks();
    print_task_set(&tasks);

    // 运行并比较所有调度算法
    println!("\n{:=^70}", " 运行调度算法 ");
    
    // 1. FCFS
    run_scheduler(&FcfsScheduler::new(), &tasks);
    
    // 2. SJF (Non-preemptive)
    run_scheduler(&SjfScheduler::new(false), &tasks);
    
    // 3. SRTF (Preemptive SJF)
    run_scheduler(&SjfScheduler::new(true), &tasks);
    
    // 4. Round Robin (q=2)
    run_scheduler(&RoundRobinScheduler::new(2), &tasks);
    
    // 5. Round Robin (q=4)
    run_scheduler(&RoundRobinScheduler::new(4), &tasks);
    
    // 6. Priority (Non-preemptive)
    let priority_tasks = create_priority_tasks();
    println!("\n>>> 使用优先级任务集测试优先级调度 <<<");
    print_task_set(&priority_tasks);
    run_scheduler(&PriorityScheduler::new(false), &priority_tasks);
    
    // 7. MLFQ
    run_scheduler(&MlfqScheduler::new(vec![2, 4, 8]), &tasks);

    // 最终比较
    println!("\n{:=^70}", " 算法性能综合比较 ");
    let all_results = vec![
        ("FCFS".to_string(), FcfsScheduler::new().schedule(&tasks)),
        ("SJF".to_string(), SjfScheduler::new(false).schedule(&tasks)),
        ("SRTF".to_string(), SjfScheduler::new(true).schedule(&tasks)),
        ("RR(q=2)".to_string(), RoundRobinScheduler::new(2).schedule(&tasks)),
        ("RR(q=4)".to_string(), RoundRobinScheduler::new(4).schedule(&tasks)),
        ("MLFQ".to_string(), MlfqScheduler::new(vec![2, 4, 8]).schedule(&tasks)),
    ];
    
    let metrics_to_compare: Vec<(String, _)> = all_results
        .iter()
        .map(|(name, result)| (name.clone(), result.metrics))
        .collect();
    compare_metrics(&metrics_to_compare);

    println!("\n{:=^70}", " 演示完成 ");
    println!("使用 'cargo run --example demo' 查看更多示例");
}

/// 打印程序标题
fn print_banner() {
    println!("\n{:=^70}", "");
    println!("{:^70}", "CPU Scheduler Simulator");
    println!("{:^70}", "CPU 调度算法模拟器");
    println!("{:=^70}\n", "");
}

/// 打印任务集信息
fn print_task_set(tasks: &[Task]) {
    println!("任务集配置:");
    println!("{:-<60}", "");
    println!("{:<5} {:<12} {:<12} {:<12} {:<12}", 
             "ID", "到达时间", "执行时间", "优先级", "状态");
    println!("{:-<60}", "");
    
    for task in tasks {
        println!("{:<5} {:<12} {:<12} {:<12} {:<12}",
            task.id,
            task.arrival_time,
            task.burst_time,
            task.priority,
            "待调度"
        );
    }
    println!("{:-<60}\n", "");
}

/// 运行单个调度器并显示结果
fn run_scheduler<S: Scheduler>(scheduler: &S, tasks: &[Task]) {
    println!("\n{:-<70}", "");
    println!("调度算法: {}", scheduler.name());
    println!("{:-<70}", "");
    
    let result = scheduler.schedule(tasks);
    result.print();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_all_schedulers_run() {
        let tasks = create_sample_tasks();
        
        // 测试所有调度器都能正常运行
        let schedulers: Vec<Box<dyn Scheduler>> = vec![
            Box::new(FcfsScheduler::new()),
            Box::new(SjfScheduler::new(false)),
            Box::new(SjfScheduler::new(true)),
            Box::new(RoundRobinScheduler::new(2)),
            Box::new(PriorityScheduler::new(false)),
            Box::new(MlfqScheduler::default()),
        ];

        for scheduler in schedulers {
            let result = scheduler.schedule(&tasks);
            assert!(result.tasks.iter().all(|t| t.is_completed()),
                "{} 未能完成所有任务", scheduler.name());
        }
    }
}
