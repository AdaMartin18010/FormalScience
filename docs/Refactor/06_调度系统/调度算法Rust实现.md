---
title: "调度算法 Rust 实现"
category: "调度系统"
subcategory: "一般"
order: 1
difficulty: "中级"
status: "已完成"
tags: ["任务调度", "调度", "资源分配", "调度系统", "一般"]
related: ["调度算法 Rust 实现", "目录", "线程池", "基本实现", "构建器模式"]
math: false
code: true
last_updated: "2026-04-12"
---

# 调度算法 Rust 实现

---

📌 **内容摘要**

本文档深入探讨调度算法 Rust 实现的核心原理和关键方法。内容涵盖调度系统领域的主要知识点，包括任务调度, 调度, 资源分配等关键主题。适合有一定基础的学习者系统学习。

**关键词**: 任务调度, 调度, 资源分配, 调度系统

📚 **学习目标**

- 掌握调度算法 Rust 实现的核心概念和主要方法
- 理解相关理论的应用场景
- 能够分析和实现相关算法

🎯 **难度级别**: 中级

⏱️ **预计阅读时间**: 15分钟

**前置知识**: 相关领域的基础概念, 算法与数据结构

---




本文档展示调度算法的 Rust 实现，包括线程池、工作窃取、优先级调度等。

## 目录

- [调度算法 Rust 实现](#调度算法-rust-实现)
  - [目录](#目录)
  - [线程池](#线程池)
    - [基本实现](#基本实现)
    - [构建器模式](#构建器模式)
    - [异步任务](#异步任务)
  - [工作窃取调度器](#工作窃取调度器)
    - [Chase-Lev 双端队列](#chase-lev-双端队列)
    - [工作线程](#工作线程)
  - [优先级调度器](#优先级调度器)
    - [优先级队列](#优先级队列)
    - [优先级调度](#优先级调度)
    - [速率限制调度器](#速率限制调度器)
  - [时间片轮转](#时间片轮转)
    - [轮转调度器](#轮转调度器)
    - [带权重的轮转](#带权重的轮转)
  - [多级反馈队列](#多级反馈队列)
    - [MLFQ 实现](#mlfq-实现)
  - [EDF 调度](#edf-调度)
    - [实时任务](#实时任务)
    - [EDF 调度器](#edf-调度器)
    - [周期性任务](#周期性任务)
  - [完整代码](#完整代码)
  - [编译与测试](#编译与测试)
  - [调度器对比](#调度器对比)
  - [📚 延伸阅读](#-延伸阅读)

## 线程池

### 基本实现

```rust
pub struct ThreadPool {
    workers: Vec<Worker>,
    sender: Option<mpsc::Sender<Message>>,
}

enum Message {
    NewTask(Task),
    Terminate,
}

impl ThreadPool {
    pub fn new(size: usize) -> Self {
        let (sender, receiver) = mpsc::channel();
        let receiver = Arc::new(Mutex::new(receiver));

        let mut workers = Vec::with_capacity(size);
        for id in 0..size {
            workers.push(Worker::new(id, Arc::clone(&receiver)));
        }

        ThreadPool { workers, sender: Some(sender) }
    }

    pub fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        let task = Box::new(f);
        self.sender.as_ref().unwrap().send(Message::NewTask(task)).unwrap();
    }
}
```

### 构建器模式

```rust
pub struct ThreadPoolBuilder {
    size: Option<usize>,
    stack_size: Option<usize>,
    name_prefix: Option<String>,
}

impl ThreadPoolBuilder {
    pub fn size(mut self, size: usize) -> Self {
        self.size = Some(size);
        self
    }

    pub fn build(self) -> ThreadPool {
        let size = self.size.unwrap_or_else(num_cpus::get);
        // ...
    }
}
```

### 异步任务

```rust
pub struct AsyncThreadPool {
    pool: ThreadPool,
}

impl AsyncThreadPool {
    pub fn spawn<F, T>(&self, f: F) -> TaskHandle<T>
    where
        F: FnOnce() -> T + Send + 'static,
        T: Send + 'static,
    {
        let (sender, receiver) = mpsc::channel();

        self.pool.execute(move || {
            let result = f();
            let _ = sender.send(result);
        });

        TaskHandle { receiver }
    }
}
```

## 工作窃取调度器

### Chase-Lev 双端队列

```rust
pub struct ChaseLevDeque<T> {
    buffer: Arc<ArrayQueue<T>>,
}

impl<T> ChaseLevDeque<T> {
    /// Worker 操作：从底部弹出
    pub fn pop(&self) -> Option<T> {
        self.buffer.pop()
    }

    /// Worker 操作：向底部推送
    pub fn push(&self, task: T) -> Result<(), T> {
        self.buffer.push(task).map_err(|e| e.0)
    }

    /// Stealer 操作：从顶部窃取
    pub fn steal(&self) -> Option<T> {
        self.buffer.pop()
    }
}
```

### 工作线程

```rust
pub struct Worker<T> {
    id: usize,
    deque: ChaseLevDeque<T>,
    stealers: Vec<ChaseLevDeque<T>>,
}

impl<T: Task> Worker<T> {
    pub fn run(&self, shutdown: Arc<AtomicUsize>) {
        while shutdown.load(Ordering::Relaxed) == 0 {
            // 1. 从本地队列获取任务
            if let Some(task) = self.deque.pop() {
                task.execute();
                continue;
            }

            // 2. 尝试窃取
            if self.steal() {
                continue;
            }

            // 3. 短暂自旋
            std::hint::spin_loop();
        }
    }

    fn steal(&self) -> bool {
        for stealer in &self.stealers {
            if let Some(task) = stealer.steal() {
                task.execute();
                return true;
            }
        }
        false
    }
}
```

## 优先级调度器

### 优先级队列

```rust
pub struct PriorityTask {
    priority: Priority,
    id: TaskId,
    created_at: Instant,
    task: Box<dyn FnOnce() + Send>,
}

impl Ord for PriorityTask {
    fn cmp(&self, other: &Self) -> Ordering {
        // 高优先级在前，同优先级先创建的先执行
        other.priority.cmp(&self.priority)
            .then_with(|| other.created_at.cmp(&self.created_at))
    }
}
```

### 优先级调度

```rust
pub struct PriorityScheduler {
    queue: Arc<(Mutex<BinaryHeap<PriorityTask>>, Condvar)>,
}

impl PriorityScheduler {
    pub fn spawn_with_priority<F>(&self, priority: Priority, f: F) -> TaskId
    where
        F: FnOnce() + Send + 'static,
    {
        let task = PriorityTask::new(priority, f);
        let id = task.id;

        let (lock, cvar) = &*self.queue;
        lock.lock().unwrap().push(task);
        cvar.notify_one();

        id
    }

    fn worker_loop(queue: Arc<(Mutex<BinaryHeap<PriorityTask>>, Condvar)>) {
        loop {
            let task = {
                let heap = lock.lock().unwrap();
                // 等待并获取最高优先级任务
                cvar.wait_while(heap, |h| h.is_empty()).unwrap().pop()
            };

            if let Some(task) = task {
                task.execute();
            }
        }
    }
}
```

### 速率限制调度器

```rust
pub struct RateLimitedScheduler {
    tokens: Mutex<f64>,
    max_tokens: f64,
    refill_rate: f64,
}

impl RateLimitedScheduler {
    pub fn spawn<F>(&self, cost: f64, f: F) -> Option<TaskId>
    where
        F: FnOnce() + Send + 'static,
    {
        let mut tokens = self.tokens.lock().unwrap();
        if *tokens >= cost {
            *tokens -= cost;
            // 提交任务
            Some(id)
        } else {
            None // 速率限制
        }
    }
}
```

## 时间片轮转

### 轮转调度器

```rust
pub struct RoundRobinScheduler {
    queue: Arc<Mutex<VecDeque<TimeSliceTask>>>,
    time_slice: Duration,
}

impl RoundRobinScheduler {
    fn worker_loop(queue: Arc<Mutex<VecDeque<TimeSliceTask>>>, time_slice: Duration) {
        loop {
            let mut task = queue.lock().unwrap().pop_front();

            if let Some(mut t) = task {
                match t.run(time_slice) {
                    RunResult::Completed => {}
                    RunResult::NeedsMoreTime => {
                        // 重新加入队列
                        queue.lock().unwrap().push_back(t);
                    }
                    // ...
                }
            }
        }
    }
}
```

### 带权重的轮转

```rust
impl WeightedRoundRobinScheduler {
    pub fn spawn(&self, task: impl Runnable, priority: u32) -> TaskId {
        // 根据优先级调整时间片
        let time_slice = self.base_time_slice * priority.max(1);
        // ...
    }
}
```

## 多级反馈队列

### MLFQ 实现

```rust
pub struct MlfqScheduler {
    queues: Vec<VecDeque<MlfqTask>>,
    boost_interval: Duration,
}

impl MlfqScheduler {
    pub fn new(num_threads: usize, num_queues: usize) -> Self {
        let mut queues = Vec::with_capacity(num_queues);
        for i in 0..num_queues {
            // 每个队列时间片是前一个的两倍
            let time_slice = DEFAULT_BASE_TIME_SLICE * (1u32 << i);
            queues.push(MlfqQueue::new(time_slice));
        }
        // ...
    }

    fn process_task(&mut self, mut task: MlfqTask) {
        let time_slice = self.queues[task.queue_level].time_slice();

        task.execute();

        // 如果用完时间片，降低优先级
        if elapsed >= time_slice && task.queue_level < self.num_queues - 1 {
            task.queue_level += 1;
        }
    }

    /// 周期性优先级提升
    fn boost_all(&mut self) {
        for i in (1..self.num_queues).rev() {
            while let Some(mut task) = self.queues[i].pop() {
                task.queue_level = 0;
                self.queues[0].push(task);
            }
        }
    }
}
```

## EDF 调度

### 实时任务

```rust
pub struct RealtimeTask {
    id: TaskId,
    deadline: Deadline,
    task: Box<dyn FnOnce() + Send>,
    is_hard: bool,
}

impl Ord for RealtimeTask {
    fn cmp(&self, other: &Self) -> Ordering {
        // 截止时间最早的优先级最高
        other.deadline.cmp(&self.deadline)
    }
}
```

### EDF 调度器

```rust
pub struct EdfScheduler {
    queue: Arc<Mutex<BinaryHeap<RealtimeTask>>>,
}

impl EdfScheduler {
    fn worker_loop(queue: Arc<Mutex<BinaryHeap<RealtimeTask>>>) {
        loop {
            let task = {
                let mut heap = queue.lock().unwrap();

                // 检查过期任务
                if let Some(task) = heap.peek() {
                    if task.deadline.is_expired() {
                        let expired = heap.pop().unwrap();
                        handle_deadline_miss(expired);
                        continue;
                    }
                }

                heap.pop()
            };

            if let Some(task) = task {
                if !task.deadline.is_expired() {
                    task.execute();
                }
            }
        }
    }

    /// 检查调度可行性
    pub fn is_schedulable(utilization: f64, num_processors: usize) -> bool {
        utilization <= num_processors as f64
    }
}
```

### 周期性任务

```rust
pub struct PeriodicTask {
    period: Duration,
    deadline: Duration,
    execution_time: Duration,
}

impl PeriodicTask {
    pub fn utilization(&self) -> f64 {
        self.execution_time.as_secs_f64() / self.period.as_secs_f64()
    }
}
```

## 完整代码

```
docs/Refactor/examples/rust/scheduling/
├── Cargo.toml
├── src/
│   ├── lib.rs
│   ├── thread_pool.rs       # 线程池
│   ├── work_stealing.rs     # 工作窃取
│   ├── priority_scheduler.rs # 优先级调度
│   ├── round_robin.rs       # 时间片轮转
│   ├── mlfq.rs              # 多级反馈队列
│   └── edf.rs               # EDF 调度
└── benches/
    └── scheduler_benchmark.rs
```

## 编译与测试

```bash
cd docs/Refactor/examples/rust/scheduling
cargo build
cargo test
cargo bench
```

## 调度器对比

| 调度器 | 特点 | 适用场景 |
|-------|------|---------|
| 线程池 | 简单、可控 | 通用并行任务 |
| 工作窃取 | 负载均衡 | 计算密集型 |
| 优先级 | 保证关键任务 | 实时系统 |
| 轮转 | 公平 | CPU 密集型 |
| MLFQ | 自适应 | 混合负载 |
| EDF | 最优实时 | 硬实时系统 |

---

## 📚 延伸阅读

- [01.2 调度算法分析](./01_调度理论基础/01.2_调度算法分析.md)
