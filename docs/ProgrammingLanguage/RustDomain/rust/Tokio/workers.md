# Rust异步多线程

下面是一个使用 Rust 2024 新特性实现的多线程工作者模式、观察者模式和任务池化模式的示例：

## 目录

- [Rust异步多线程](#rust异步多线程)
  - [目录](#目录)
  - [1. 项目依赖配置](#1-项目依赖配置)
    - [2. 任务定义和状态](#2-任务定义和状态)
    - [3. 工作者池实现](#3-工作者池实现)
    - [4. 异步队列实现](#4-异步队列实现)
    - [5. 观察者模式实现](#5-观察者模式实现)
    - [6. 任务生成器实现](#6-任务生成器实现)
    - [7. 任务调度器实现](#7-任务调度器实现)
    - [8. 使用示例](#8-使用示例)
    - [9. 自定义观察者示例](#9-自定义观察者示例)
    - [10. 任务优先级队列实现](#10-任务优先级队列实现)

## 1. 项目依赖配置

```toml
[dependencies]
tokio = { version = "1.0", features = ["full"] }
futures = "0.3"
async-trait = "0.1"
anyhow = "1.0"
tracing = "0.1"
dashmap = "5.5"
crossbeam = "0.8"
parking_lot = "0.12"
```

### 2. 任务定义和状态

```rust
#[derive(Debug, Clone)]
pub enum TaskState {
    Pending,
    Running,
    Completed(TaskResult),
    Failed(String),
}

#[derive(Debug, Clone)]
pub struct Task {
    id: String,
    priority: u32,
    payload: Vec<u8>,
    state: Arc<RwLock<TaskState>>,
}

#[derive(Debug, Clone)]
pub struct TaskResult {
    data: Vec<u8>,
    metadata: HashMap<String, String>,
}

impl Task {
    pub fn new(id: String, priority: u32, payload: Vec<u8>) -> Self {
        Self {
            id,
            priority,
            payload,
            state: Arc::new(RwLock::new(TaskState::Pending)),
        }
    }

    pub async fn set_state(&self, state: TaskState) {
        *self.state.write() = state;
    }

    pub async fn get_state(&self) -> TaskState {
        self.state.read().clone()
    }
}
```

### 3. 工作者池实现

```rust
pub struct WorkerPool {
    workers: Vec<Worker>,
    task_queue: Arc<AsyncQueue<Task>>,
    observers: Arc<DashMap<String, Box<dyn Observer>>>,
}

impl WorkerPool {
    pub fn new(num_workers: usize) -> Self {
        let task_queue = Arc::new(AsyncQueue::new());
        let observers = Arc::new(DashMap::new());
        let mut workers = Vec::with_capacity(num_workers);

        for id in 0..num_workers {
            workers.push(Worker::new(
                format!("worker-{}", id),
                task_queue.clone(),
                observers.clone(),
            ));
        }

        Self {
            workers,
            task_queue,
            observers,
        }
    }

    pub async fn start(&self) {
        for worker in &self.workers {
            worker.start().await;
        }
    }

    pub async fn submit_task(&self, task: Task) {
        self.task_queue.push(task).await;
    }

    pub fn add_observer(&self, observer: Box<dyn Observer>) {
        self.observers.insert(observer.id().to_string(), observer);
    }
}

pub struct Worker {
    id: String,
    task_queue: Arc<AsyncQueue<Task>>,
    observers: Arc<DashMap<String, Box<dyn Observer>>>,
}

impl Worker {
    pub fn new(
        id: String,
        task_queue: Arc<AsyncQueue<Task>>,
        observers: Arc<DashMap<String, Box<dyn Observer>>>,
    ) -> Self {
        Self {
            id,
            task_queue,
            observers,
        }
    }

    pub async fn start(&self) {
        let id = self.id.clone();
        let task_queue = self.task_queue.clone();
        let observers = self.observers.clone();

        tokio::spawn(async move {
            loop {
                if let Some(task) = task_queue.pop().await {
                    // 通知观察者任务开始
                    for observer in observers.iter() {
                        observer.on_task_start(&id, &task).await;
                    }

                    // 执行任务
                    let result = Self::process_task(&task).await;

                    // 更新任务状态
                    match result {
                        Ok(result) => {
                            task.set_state(TaskState::Completed(result)).await;
                            // 通知观察者任务完成
                            for observer in observers.iter() {
                                observer.on_task_complete(&id, &task).await;
                            }
                        }
                        Err(e) => {
                            task.set_state(TaskState::Failed(e.to_string())).await;
                            // 通知观察者任务失败
                            for observer in observers.iter() {
                                observer.on_task_failed(&id, &task, &e).await;
                            }
                        }
                    }
                }
            }
        });
    }

    async fn process_task(task: &Task) -> anyhow::Result<TaskResult> {
        // 模拟任务处理
        tokio::time::sleep(Duration::from_secs(1)).await;
        Ok(TaskResult {
            data: task.payload.clone(),
            metadata: HashMap::new(),
        })
    }
}
```

### 4. 异步队列实现

```rust
pub struct AsyncQueue<T> {
    inner: Arc<Mutex<VecDeque<T>>>,
    not_empty: Arc<Notify>,
}

impl<T> AsyncQueue<T> {
    pub fn new() -> Self {
        Self {
            inner: Arc::new(Mutex::new(VecDeque::new())),
            not_empty: Arc::new(Notify::new()),
        }
    }

    pub async fn push(&self, item: T) {
        {
            let mut queue = self.inner.lock().await;
            queue.push_back(item);
        }
        self.not_empty.notify_one();
    }

    pub async fn pop(&self) -> Option<T> {
        loop {
            {
                let mut queue = self.inner.lock().await;
                if let Some(item) = queue.pop_front() {
                    return Some(item);
                }
            }
            self.not_empty.notified().await;
        }
    }
}
```

### 5. 观察者模式实现

```rust
#[async_trait]
pub trait Observer: Send + Sync {
    fn id(&self) -> &str;
    async fn on_task_start(&self, worker_id: &str, task: &Task);
    async fn on_task_complete(&self, worker_id: &str, task: &Task);
    async fn on_task_failed(&self, worker_id: &str, task: &Task, error: &anyhow::Error);
}

pub struct LoggingObserver {
    id: String,
}

#[async_trait]
impl Observer for LoggingObserver {
    fn id(&self) -> &str {
        &self.id
    }

    async fn on_task_start(&self, worker_id: &str, task: &Task) {
        tracing::info!("Worker {} started task {}", worker_id, task.id);
    }

    async fn on_task_complete(&self, worker_id: &str, task: &Task) {
        tracing::info!("Worker {} completed task {}", worker_id, task.id);
    }

    async fn on_task_failed(&self, worker_id: &str, task: &Task, error: &anyhow::Error) {
        tracing::error!("Worker {} failed task {}: {}", worker_id, task.id, error);
    }
}
```

### 6. 任务生成器实现

```rust
pub struct TaskGenerator {
    gen: Pin<Box<dyn Generator<Yield = Task, Return = ()> + Send>>,
}

impl TaskGenerator {
    pub fn new() -> Self {
        Self {
            gen: Box::pin(|| {
                let mut id = 0;
                loop {
                    id += 1;
                    yield Task::new(
                        format!("task-{}", id),
                        rand::random::<u32>(),
                        vec![],
                    );
                }
            }),
        }
    }

    pub async fn next(&mut self) -> Option<Task> {
        match self.gen.as_mut().resume(()) {
            GeneratorState::Yielded(task) => Some(task),
            GeneratorState::Complete(()) => None,
        }
    }
}
```

### 7. 任务调度器实现

```rust
pub struct TaskScheduler {
    worker_pool: Arc<WorkerPool>,
    task_generator: TaskGenerator,
}

impl TaskScheduler {
    pub fn new(num_workers: usize) -> Self {
        Self {
            worker_pool: Arc::new(WorkerPool::new(num_workers)),
            task_generator: TaskGenerator::new(),
        }
    }

    pub async fn start(&self) {
        // 启动工作者池
        self.worker_pool.start().await;

        // 添加观察者
        self.worker_pool.add_observer(Box::new(LoggingObserver {
            id: "logging".to_string(),
        }));

        // 生成并提交任务
        let worker_pool = self.worker_pool.clone();
        let mut task_generator = self.task_generator.clone();

        tokio::spawn(async move {
            while let Some(task) = task_generator.next().await {
                worker_pool.submit_task(task).await;
            }
        });
    }
}
```

### 8. 使用示例

```rust
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    // 创建任务调度器
    let scheduler = TaskScheduler::new(4);

    // 启动调度器
    scheduler.start().await;

    // 等待一段时间
    tokio::time::sleep(Duration::from_secs(10)).await;

    Ok(())
}
```

### 9. 自定义观察者示例

```rust
pub struct MetricsObserver {
    id: String,
    metrics: Arc<Metrics>,
}

impl MetricsObserver {
    pub fn new(id: String) -> Self {
        Self {
            id,
            metrics: Arc::new(Metrics::new()),
        }
    }
}

#[async_trait]
impl Observer for MetricsObserver {
    fn id(&self) -> &str {
        &self.id
    }

    async fn on_task_start(&self, worker_id: &str, task: &Task) {
        self.metrics.task_started.inc();
        self.metrics.active_tasks.inc();
    }

    async fn on_task_complete(&self, worker_id: &str, task: &Task) {
        self.metrics.task_completed.inc();
        self.metrics.active_tasks.dec();
    }

    async fn on_task_failed(&self, worker_id: &str, task: &Task, error: &anyhow::Error) {
        self.metrics.task_failed.inc();
        self.metrics.active_tasks.dec();
    }
}
```

### 10. 任务优先级队列实现

```rust
pub struct PriorityQueue<T> {
    inner: BinaryHeap<(u32, T)>,
}

impl<T> PriorityQueue<T> {
    pub fn new() -> Self {
        Self {
            inner: BinaryHeap::new(),
        }
    }

    pub fn push(&mut self, priority: u32, item: T) {
        self.inner.push((priority, item));
    }

    pub fn pop(&mut self) -> Option<T> {
        self.inner.pop().map(|(_, item)| item)
    }
}

pub struct PriorityWorkerPool {
    workers: Vec<PriorityWorker>,
    task_queue: Arc<AsyncPriorityQueue<Task>>,
    observers: Arc<DashMap<String, Box<dyn Observer>>>,
}

impl PriorityWorkerPool {
    pub fn new(num_workers: usize) -> Self {
        let task_queue = Arc::new(AsyncPriorityQueue::new());
        let observers = Arc::new(DashMap::new());
        let mut workers = Vec::with_capacity(num_workers);

        for id in 0..num_workers {
            workers.push(PriorityWorker::new(
                format!("worker-{}", id),
                task_queue.clone(),
                observers.clone(),
            ));
        }

        Self {
            workers,
            task_queue,
            observers,
        }
    }
}
```

这个完整的示例展示了如何：

1. 使用生成器创建任务流
2. 实现异步工作者池
3. 实现观察者模式
4. 实现优先级任务队列
5. 使用 Tokio 进行异步处理
6. 实现任务状态管理
7. 提供可扩展的观察者接口
8. 支持任务优先级调度
9. 实现指标收集
10. 提供日志记录功能

通过这种方式，您可以构建一个高效的、可扩展的任务处理系统，支持：

- 异步任务处理
- 优先级调度
- 状态监控
- 指标收集
- 错误处理
- 可观察性

这个实现提供了良好的可扩展性和灵活性，可以根据需要添加更多功能和组件。
