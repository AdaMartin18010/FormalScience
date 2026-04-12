# FormalScience Rust 代码示例

本项目为 FormalScience 提供了丰富的 Rust 代码示例，涵盖调度算法、并发模式、异步运行时和系统编程等核心计算机科学主题。

## 项目结构

```
examples/rust/
├── Cargo.toml              # 项目配置
├── README.md               # 本文件
├── scheduling/             # 调度算法实现
│   ├── round_robin.rs      # 轮转调度算法
│   ├── priority_scheduler.rs # 优先级调度
│   ├── thread_pool.rs      # 线程池和工作窃取
│   ├── buddy_allocator.rs  # 伙伴系统内存分配器
│   └── async_io.rs         # 异步IO和epoll
├── concurrency/            # 并发模式实现
│   ├── locks.rs            # 锁（Mutex、RwLock、SpinLock）
│   ├── lock_free.rs        # 无锁数据结构
│   ├── channels.rs         # 通道（MPSC、广播）
│   └── atomic_memory.rs    # 原子操作和内存序
├── async/                  # 异步运行时
│   ├── futures_pin.rs      # Future和Pin详解
│   ├── waker_executor.rs   # Waker机制和执行器
│   └── tokio_examples.rs   # Tokio使用示例
└── system/                 # 系统编程
    ├── memory_management.rs # 内存管理
    ├── syscalls.rs         # 系统调用封装
    └── bpf_program.rs      # BPF程序开发
```

## 快速开始

### 环境要求

- Rust 1.70+ (建议使用最新稳定版)
- Cargo
- Linux 环境（部分示例需要）

### 编译和运行

```bash
# 克隆仓库后进入目录
cd examples/rust

# 编译所有示例
cargo build --examples

# 运行特定示例
cargo run --example scheduling_round_robin
cargo run --example concurrency_locks
cargo run --example async_tokio_examples

# 运行测试
cargo test

# 生成文档
cargo doc --open
```

## 内容详解

### 1. 调度算法 (scheduling/)

#### 轮转调度 (round_robin.rs)
- 基于时间片的进程调度
- 多级反馈队列 (MLFQ) 实现
- 优先级调度算法

#### 优先级调度 (priority_scheduler.rs)
- 抢占式和非抢占式优先级调度
- Aging 算法防止饥饿
- 速率单调调度 (Rate Monotonic)

#### 线程池 (thread_pool.rs)
- 基础线程池实现
- 工作窃取算法
- 带统计功能的增强型线程池

#### 伙伴系统 (buddy_allocator.rs)
- 经典伙伴系统内存分配算法
- Slab 分配器
- 内存分配统计和碎片分析

#### 异步IO (async_io.rs)
- Reactor 模式实现
- Proactor 模式实现
- 模拟 epoll 机制

### 2. 并发模式 (concurrency/)

#### 锁 (locks.rs)
- 自旋锁 (SpinLock) 实现
- 读写锁 (RwLock) 实现
- 顺序锁 (SeqLock)
- 性能对比

#### 无锁数据结构 (lock_free.rs)
- Treiber 无锁栈
- Michael-Scott 无锁队列
- RCU (Read-Copy-Update) 机制
- 原子计数器

#### 通道 (channels.rs)
- MPSC 通道实现
- 有界通道
- 广播通道
- select! 模式

#### 原子操作 (atomic_memory.rs)
- 各种内存序详解
- Acquire-Release 语义
- 内存屏障 (Fence)
- 自旋锁的原子操作实现

### 3. 异步运行时 (async/)

#### Future 和 Pin (futures_pin.rs)
- Future trait 实现
- Pin 和自引用结构
- 手动状态机转换
- 组合器实现

#### Waker 和执行器 (waker_executor.rs)
- 自定义 Waker 实现
- 简单执行器
- 改进的支持唤醒的执行器
- 任务调度

#### Tokio 示例 (tokio_examples.rs)
- 基本异步操作
- 并发控制 (join!, select!, timeout)
- 通道使用 (MPSC、广播、oneshot)
- 同步原语 (Mutex、RwLock、Semaphore)
- 网络编程 (TCP)
- 文件IO
- 任务管理

### 4. 系统编程 (system/)

#### 内存管理 (memory_management.rs)
- 内存布局分析
- 自定义分配器
- 对象池
- 竞技场分配器
- 零拷贝缓冲区
- 内存映射文件

#### 系统调用 (syscalls.rs)
- 文件操作封装
- 进程管理
- 信号处理
- 内存映射 (mmap)
- 时间和定时器
- 资源限制

#### BPF 程序 (bpf_program.rs)
- BPF 程序类型介绍
- XDP 程序示例
- Kprobe 程序示例
- BPF Map 使用
- 用户态加载器框架

## 核心概念图解

### 调度算法

```
┌─────────────────────────────────────────────────────┐
│                  调度算法分类                         │
├─────────────────────────────────────────────────────┤
│  抢占式        │  非抢占式       │  实时调度          │
│  ├── 轮转      │  ├── FIFO       │  ├── 速率单调      │
│  ├── 优先级    │  └── SJF        │  └── 最早截止期    │
│  └── MLFQ      │                 │                   │
└─────────────────────────────────────────────────────┘
```

### 并发模型

```
┌─────────────────────────────────────────────────────┐
│                  并发模型                            │
├─────────────────────────────────────────────────────┤
│  锁机制          │  无锁结构         │  消息传递      │
│  ├── Mutex       │  ├── 无锁栈       │  ├── Channel   │
│  ├── RwLock      │  ├── 无锁队列     │  └── Actor     │
│  └── SpinLock    │  └── RCU          │                │
└─────────────────────────────────────────────────────┘
```

### 异步运行时架构

```
┌─────────────────────────────────────────────────────┐
│                  异步运行时架构                      │
├─────────────────────────────────────────────────────┤
│  ┌──────────┐    ┌──────────┐    ┌──────────┐      │
│  │  Future  │───▶│  Waker   │───▶│ Executor │      │
│  └──────────┘    └──────────┘    └──────────┘      │
│       │                               │            │
│       ▼                               ▼            │
│  ┌──────────┐                    ┌──────────┐      │
│  │   Task   │◀───────────────────│ TaskQueue│      │
│  └──────────┘                    └──────────┘      │
└─────────────────────────────────────────────────────┘
```

## 学习路径建议

### 初学者
1. 从 `concurrency/locks.rs` 开始，理解基本的并发控制
2. 阅读 `async/futures_pin.rs`，理解异步基础概念
3. 尝试 `scheduling/round_robin.rs` 了解调度算法

### 进阶学习者
1. 深入研究 `concurrency/lock_free.rs` 的无锁编程
2. 分析 `async/waker_executor.rs` 的执行器实现
3. 研究 `system/memory_management.rs` 的内存管理技术

### 高级开发者
1. 实现新的调度算法或优化现有实现
2. 扩展 BPF 程序功能
3. 为 Tokio 编写自定义组件

## 相关文档

- [The Rust Programming Language](https://doc.rust-lang.org/book/)
- [Rust异步编程](https://rust-lang.github.io/async-book/)
- [Tokio文档](https://tokio.rs/)
- [Linux内核文档 - 调度器](https://www.kernel.org/doc/html/latest/scheduler/)
- [BPF文档](https://docs.kernel.org/bpf/)

## 贡献指南

欢迎提交 Issue 和 PR！请确保：

1. 代码通过 `cargo check` 和 `cargo test`
2. 添加适当的注释和文档
3. 遵循 Rust 代码规范 (`cargo fmt`, `cargo clippy`)
4. 更新相关的 README 文档

## 许可

MIT OR Apache-2.0
