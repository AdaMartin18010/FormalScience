# Scheduler Simulator - 调度器模拟器

一个用 Rust 编写的 CPU 调度算法模拟器，支持多种经典调度算法。

## 支持的调度算法

1. **FCFS (First-Come-First-Served)** - 先来先服务
2. **SJF (Shortest Job First)** - 短作业优先
3. **RR (Round Robin)** - 时间片轮转
4. **Priority Scheduling** - 优先级调度
5. **MLFQ (Multi-Level Feedback Queue)** - 多级反馈队列

## 项目结构

```
scheduler_simulator/
├── Cargo.toml
├── README.md
├── src/
│   ├── main.rs          # 程序入口
│   ├── tasks.rs         # 任务定义
│   ├── metrics.rs       # 性能指标
│   └── scheduler/       # 调度器实现
│       ├── mod.rs
│       ├── fcfs.rs
│       ├── sjf.rs
│       ├── round_robin.rs
│       ├── priority.rs
│       └── mlfq.rs
└── examples/
    └── demo.rs          # 使用示例
```

## 编译运行

```bash
# 编译
cargo build --release

# 运行
cargo run

# 运行示例
cargo run --example demo
```

## 性能指标

- **Turnaround Time** (周转时间): 任务完成时间 - 到达时间
- **Waiting Time** (等待时间): 任务在就绪队列中等待的时间
- **Response Time** (响应时间): 任务首次获得 CPU 的时间 - 到达时间
- **Throughput** (吞吐量): 单位时间内完成的任务数

## 示例输出

```
========================================
     CPU Scheduler Simulator
========================================

任务列表:
┌────┬──────────┬─────────┬──────────┐
│ ID │ Arrival  │  Burst  │ Priority │
├────┼──────────┼─────────┼──────────┤
│ 1  │    0     │    8    │    3     │
│ 2  │    1     │    4    │    1     │
│ 3  │    2     │    9    │    2     │
└────┴──────────┴─────────┴──────────┘

=== FCFS 调度结果 ===
... (详细调度过程) ...
```

## 许可证

MIT License
