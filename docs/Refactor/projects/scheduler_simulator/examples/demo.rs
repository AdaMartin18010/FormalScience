//! Scheduler Simulator Demo
//! 
//! 演示调度器模拟器的各种使用场景和高级特性

use scheduler_simulator::scheduler::*;
use scheduler_simulator::tasks::Task;
use scheduler_simulator::metrics::compare_metrics;

fn main() {
    println!("\n{:=^80}", "");
    println!("{:^80}", "调度器模拟器 - 高级演示");
    println!("{:=^80}\n", "");

    // 演示 1: 护航效应 (Convoy Effect)
    demo_convoy_effect();

    // 演示 2: 上下文切换开销
    demo_context_switch_overhead();

    // 演示 3: 饥饿问题
    demo_starvation();

    // 演示 4: 响应时间比较
    demo_response_time_comparison();

    // 演示 5: 自定义任务集
    demo_custom_workload();

    println!("\n{:=^80}", "");
    println!("{:^80}", "所有演示完成！");
    println!("{:=^80}\n", "");
}

/// 演示 1: 护航效应 (Convoy Effect)
/// 
/// FCFS 调度中，如果有一个长任务先到达，后续短任务需要等待很长时间
fn demo_convoy_effect() {
    println!("\n{:=^80}", " 演示 1: 护航效应 (Convoy Effect) ");
    
    let tasks = vec![
        Task::new(1, 0, 100, None), // 长任务先到达
        Task::new(2, 1, 1, None),   // 短任务后到达
        Task::new(3, 2, 1, None),
        Task::new(4, 3, 1, None),
    ];

    println!("\n任务集：一个长任务(100)和多个短任务(1)");
    println!("预期：FCFS 中短任务等待时间长，SJF 效果更好\n");

    let fcfs_result = FcfsScheduler::new().schedule(&tasks);
    let sjf_result = SjfScheduler::new(false).schedule(&tasks);

    println!("FCFS 平均等待时间: {:.2}", fcfs_result.metrics.avg_waiting_time);
    println!("SJF 平均等待时间:  {:.2}", sjf_result.metrics.avg_waiting_time);
    println!("\n结论: SJF 比 FCFS 减少 {:.1}% 的等待时间",
        (fcfs_result.metrics.avg_waiting_time - sjf_result.metrics.avg_waiting_time) 
        / fcfs_result.metrics.avg_waiting_time * 100.0
    );
}

/// 演示 2: 上下文切换开销
/// 
/// Round Robin 的时间片大小对性能的影响
fn demo_context_switch_overhead() {
    println!("\n{:=^80}", " 演示 2: 时间片大小对 Round Robin 的影响 ");
    
    let tasks = vec![
        Task::new(1, 0, 10, None),
        Task::new(2, 0, 10, None),
        Task::new(3, 0, 10, None),
    ];

    println!("\n任务集：3个执行时间为10的任务同时到达\n");

    let mut results = Vec::new();
    
    for quantum in [1, 2, 5, 10, 20] {
        let result = RoundRobinScheduler::new(quantum).schedule(&tasks);
        results.push((quantum, result));
    }

    println!("时间片大小 | 甘特图条目数 | 平均等待时间 | 平均周转时间");
    println!("{:-<60}", "");
    
    for (quantum, result) in &results {
        println!("{:>10} | {:>12} | {:>12.2} | {:>14.2}",
            quantum,
            result.gantt_chart.entries.len(),
            result.metrics.avg_waiting_time,
            result.metrics.avg_turnaround_time
        );
    }

    println!("\n结论:");
    println!("- 时间片太小：频繁的上下文切换，甘特图条目多");
    println!("- 时间片太大：变成 FCFS，响应时间变差");
    println!("- 最优时间片：需要在响应时间和开销之间平衡");
}

/// 演示 3: 饥饿问题
/// 
/// 优先级调度和 SJF 可能导致长任务/低优先级任务饥饿
fn demo_starvation() {
    println!("\n{:=^80}", " 演示 3: 饥饿问题 ");
    
    let tasks = vec![
        Task::new(1, 0, 50, Some(5)), // 低优先级长任务
        Task::new(2, 1, 2, Some(1)),  // 高优先级短任务
        Task::new(3, 3, 2, Some(1)),
        Task::new(4, 5, 2, Some(1)),
        Task::new(5, 7, 2, Some(1)),
    ];

    println!("\n任务集：1个低优先级长任务 + 多个高优先级短任务\n");

    let priority_result = PriorityScheduler::new(true).schedule(&tasks);
    let rr_result = RoundRobinScheduler::new(2).schedule(&tasks);

    println!("优先级调度 (抢占式):");
    println!("  - 任务1 (长任务) 完成时间: {}", 
        priority_result.tasks[0].completion_time.unwrap_or(0));
    println!("  - 任务1 等待时间: {}", priority_result.tasks[0].waiting_time);
    
    println!("\nRound Robin (时间片=2):");
    println!("  - 任务1 (长任务) 完成时间: {}", 
        rr_result.tasks[0].completion_time.unwrap_or(0));
    println!("  - 任务1 等待时间: {}", rr_result.tasks[0].waiting_time);

    println!("\n结论: Round Robin 更公平，避免了低优先级任务的饥饿");
}

/// 演示 4: 响应时间比较
/// 
/// 比较不同调度算法的响应时间，对交互式系统很重要
fn demo_response_time_comparison() {
    println!("\n{:=^80}", " 演示 4: 响应时间比较 ");
    
    let tasks = vec![
        Task::new(1, 0, 20, None), // 后台任务
        Task::new(2, 1, 1, None),  // 交互式任务
        Task::new(3, 2, 1, None),  // 交互式任务
    ];

    println!("\n任务集：1个后台任务 + 2个交互式任务\n");

    let schedulers: Vec<(&str, Box<dyn Scheduler>)> = vec![
        ("FCFS", Box::new(FcfsScheduler::new())),
        ("SJF", Box::new(SjfScheduler::new(false))),
        ("SRTF", Box::new(SjfScheduler::new(true))),
        ("RR(q=1)", Box::new(RoundRobinScheduler::new(1))),
        ("RR(q=2)", Box::new(RoundRobinScheduler::new(2))),
    ];

    println!("算法        | 任务2响应时间 | 任务3响应时间 | 平均响应时间");
    println!("{:-<65}", "");

    for (name, scheduler) in &schedulers {
        let result = scheduler.schedule(&tasks);
        let resp_2 = result.tasks[1].response_time().unwrap_or(0);
        let resp_3 = result.tasks[2].response_time().unwrap_or(0);
        let avg = result.metrics.avg_response_time;
        
        println!("{:<11} | {:>13} | {:>13} | {:>14.2}",
            name, resp_2, resp_3, avg);
    }

    println!("\n结论: Round Robin 提供最好的响应时间，适合交互式系统");
}

/// 演示 5: 自定义工作负载
/// 
/// 用户可以定义自己的工作负载进行测试
fn demo_custom_workload() {
    println!("\n{:=^80}", " 演示 5: 自定义工作负载分析 ");
    
    // 模拟一个混合工作负载：
    // - 批处理作业（长执行时间，低优先级）
    // - 交互式作业（短执行时间，高优先级）
    // - I/O 密集型作业（中等执行时间）
    
    let workload = vec![
        // 批处理作业
        Task::new(1, 0, 50, Some(3)),
        Task::new(2, 5, 40, Some(3)),
        
        // 交互式作业
        Task::new(3, 1, 2, Some(1)),
        Task::new(4, 2, 2, Some(1)),
        Task::new(5, 3, 2, Some(1)),
        
        // I/O 密集型作业
        Task::new(6, 10, 10, Some(2)),
        Task::new(7, 12, 8, Some(2)),
    ];

    println!("\n工作负载配置:");
    println!("- 批处理作业: 2个 (执行时间 40-50, 优先级 3)");
    println!("- 交互式作业: 3个 (执行时间 2, 优先级 1)");
    println!("- I/O 密集型: 2个 (执行时间 8-10, 优先级 2)\n");

    let results = vec![
        ("FCFS", FcfsScheduler::new().schedule(&workload)),
        ("SJF", SjfScheduler::new(false).schedule(&workload)),
        ("SRTF", SjfScheduler::new(true).schedule(&workload)),
        ("RR(q=2)", RoundRobinScheduler::new(2).schedule(&workload)),
        ("Priority", PriorityScheduler::new(false).schedule(&workload)),
        ("MLFQ", MlfqScheduler::new(vec![2, 4, 8]).schedule(&workload)),
    ];

    // 打印详细结果
    let metrics: Vec<(String, _)> = results
        .iter()
        .map(|(name, result)| (name.to_string(), result.metrics))
        .collect();
    
    compare_metrics(&metrics);

    // 针对特定目标的建议
    println!("针对不同目标的算法建议:");
    println!("{:-<60}", "");
    
    // 找到最优响应时间的算法
    let best_response = results.iter()
        .min_by(|a, b| a.1.metrics.avg_response_time.partial_cmp(&b.1.metrics.avg_response_time).unwrap())
        .map(|(name, _)| *name)
        .unwrap_or("Unknown");
    
    // 找到最优周转时间的算法
    let best_turnaround = results.iter()
        .min_by(|a, b| a.1.metrics.avg_turnaround_time.partial_cmp(&b.1.metrics.avg_turnaround_time).unwrap())
        .map(|(name, _)| *name)
        .unwrap_or("Unknown");
    
    // 找到最优等待时间的算法
    let best_waiting = results.iter()
        .min_by(|a, b| a.1.metrics.avg_waiting_time.partial_cmp(&b.1.metrics.avg_waiting_time).unwrap())
        .map(|(name, _)| *name)
        .unwrap_or("Unknown");

    println!("最佳响应时间:    {:<15} (适合交互式系统)", best_response);
    println!("最佳周转时间:    {:<15} (适合批处理系统)", best_turnaround);
    println!("最佳等待时间:    {:<15} (最大化吞吐量)", best_waiting);
    println!("{:-<60}", "");
}
