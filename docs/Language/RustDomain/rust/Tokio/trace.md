# rust分布式日志实现

下面是一个详细的示例，展示如何在 Tokio 异步编程中结合 trace、console 和 OpenTelemetry 实现完整的日志、度量和跟踪功能。

## 目录

- [rust分布式日志实现](#rust分布式日志实现)
  - [目录](#目录)
  - [1. 项目依赖配置](#1-项目依赖配置)
    - [2. 基础设施代码](#2-基础设施代码)
    - [3. 创建自定义的跟踪宏](#3-创建自定义的跟踪宏)
    - [4. 实现业务逻辑](#4-实现业务逻辑)
    - [5. 实现 HTTP 服务器](#5-实现-http-服务器)
    - [6. 主程序入口](#6-主程序入口)
    - [7. 使用示例](#7-使用示例)
    - [8. 配置文件示例](#8-配置文件示例)
    - [9. 设计规范](#9-设计规范)
    - [10. 监控面板配置](#10-监控面板配置)
    - [\*1. 项目依赖配置](#1-项目依赖配置-1)
    - [2. 自定义跟踪器实现](#2-自定义跟踪器实现)
    - [3. 自定义日志格式化器](#3-自定义日志格式化器)
    - [4. 异步任务跟踪器](#4-异步任务跟踪器)
    - [5. 示例应用程序](#5-示例应用程序)
    - [6. 使用示例](#6-使用示例)
    - [7. 运行时环境变量配置](#7-运行时环境变量配置)
    - [8. 输出示例](#8-输出示例)
    - [9. 调试功能](#9-调试功能)
      - [1. **条件跟踪**](#1-条件跟踪)
      - [2. **性能分析**](#2-性能分析)
      - [3. **错误跟踪**](#3-错误跟踪)
    - [10. 最佳实践](#10-最佳实践)
      - [1. **使用有意义的 span 名称**](#1-使用有意义的-span-名称)
      - [2. **结构化日志记录**](#2-结构化日志记录)
      - [3. **错误处理与日志记录**](#3-错误处理与日志记录)
      - [4. **异步上下文传播**](#4-异步上下文传播)

## 1. 项目依赖配置

首先在 `Cargo.toml` 中添加必要的依赖：

```toml
[dependencies]
tokio = { version = "1.0", features = ["full"] }
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
tracing-opentelemetry = "0.18"
opentelemetry = { version = "0.18", features = ["rt-tokio"] }
opentelemetry-jaeger = "0.18"
opentelemetry-prometheus = "0.11"
prometheus = "0.13"
console = "0.15"
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
```

### 2. 基础设施代码

首先创建一个 `telemetry.rs` 文件来设置基础设施：

```rust
use opentelemetry::{
    global,
    sdk::{trace, Resource},
    KeyValue,
};
use opentelemetry_prometheus::PrometheusExporter;
use prometheus::{Registry, TextEncoder};
use std::sync::Arc;
use tracing_subscriber::{
    fmt, layer::SubscriberExt, util::SubscriberInitExt, EnvFilter, Registry as TracingRegistry,
};

pub struct TelemetryConfig {
    pub service_name: String,
    pub service_version: String,
    pub environment: String,
}

pub struct Telemetry {
    pub prometheus_registry: Registry,
    pub prometheus_exporter: PrometheusExporter,
}

impl Telemetry {
    pub async fn init(config: TelemetryConfig) -> Result<Self, Box<dyn std::error::Error>> {
        // 1. 设置 OpenTelemetry tracer
        let tracer = opentelemetry_jaeger::new_pipeline()
            .with_service_name(&config.service_name)
            .with_collector_endpoint("http://localhost:14268/api/traces")
            .with_trace_config(
                trace::config()
                    .with_resource(Resource::new(vec![
                        KeyValue::new("service.name", config.service_name.clone()),
                        KeyValue::new("service.version", config.service_version),
                        KeyValue::new("environment", config.environment),
                    ]))
                    .with_sampler(trace::Sampler::AlwaysOn),
            )
            .install_batch(opentelemetry::runtime::Tokio)?;

        // 2. 设置 Prometheus exporter
        let prometheus_registry = Registry::new();
        let prometheus_exporter = opentelemetry_prometheus::exporter()
            .with_registry(prometheus_registry.clone())
            .init();

        // 3. 设置 tracing subscriber
        let telemetry = tracing_opentelemetry::layer().with_tracer(tracer);
        
        let fmt_layer = fmt::layer()
            .with_target(true)
            .with_thread_ids(true)
            .with_line_number(true)
            .with_file(true);

        let env_filter = EnvFilter::try_from_default_env()
            .unwrap_or_else(|_| EnvFilter::new("info"));

        TracingRegistry::default()
            .with(env_filter)
            .with(fmt_layer)
            .with(telemetry)
            .init();

        Ok(Self {
            prometheus_registry,
            prometheus_exporter,
        })
    }

    pub fn get_metrics(&self) -> String {
        let encoder = TextEncoder::new();
        let metric_families = self.prometheus_registry.gather();
        encoder.encode_to_string(&metric_families).unwrap()
    }
}
```

### 3. 创建自定义的跟踪宏

创建 `macros.rs` 文件：

```rust
#[macro_export]
macro_rules! trace_async_fn {
    ($name:expr) => {
        tracing::info_span!(
            $name,
            thread_id = ?std::thread::current().id(),
            time = ?chrono::Utc::now()
        )
    };
}

#[macro_export]
macro_rules! trace_async_op {
    ($name:expr, $op:expr) => {
        async {
            let span = trace_async_fn!($name);
            let _guard = span.enter();
            let result = $op.await;
            tracing::info!("Operation completed");
            result
        }
    };
}
```

### 4. 实现业务逻辑

创建 `service.rs` 文件：

```rust
use std::time::Duration;
use tokio::time::sleep;
use tracing::{info, instrument};

#[derive(Debug)]
pub struct UserService {
    counter: prometheus::IntCounter,
}

impl UserService {
    pub fn new(registry: &prometheus::Registry) -> Self {
        let counter = prometheus::IntCounter::new(
            "user_operations_total",
            "Total number of user operations",
        ).unwrap();
        registry.register(Box::new(counter.clone())).unwrap();
        
        Self { counter }
    }

    #[instrument(name = "get_user", skip(self))]
    pub async fn get_user(&self, user_id: i32) -> Result<String, String> {
        info!(user_id = user_id, "Getting user information");
        self.counter.inc();
        
        // 模拟数据库查询
        sleep(Duration::from_millis(100)).await;
        
        Ok(format!("User {}", user_id))
    }

    #[instrument(name = "create_user", skip(self))]
    pub async fn create_user(&self, name: &str) -> Result<i32, String> {
        info!(name = name, "Creating new user");
        self.counter.inc();
        
        // 模拟数据库操作
        sleep(Duration::from_millis(200)).await;
        
        Ok(42)
    }
}
```

### 5. 实现 HTTP 服务器

创建 `server.rs` 文件：

```rust
use axum::{
    extract::Path,
    routing::{get, post},
    Router,
};
use std::sync::Arc;
use tracing::instrument;

pub struct AppState {
    user_service: Arc<UserService>,
    telemetry: Arc<Telemetry>,
}

#[instrument]
async fn get_user_handler(
    Path(user_id): Path<i32>,
    state: Arc<AppState>,
) -> Result<String, String> {
    state.user_service.get_user(user_id).await
}

#[instrument]
async fn create_user_handler(
    state: Arc<AppState>,
    name: String,
) -> Result<String, String> {
    let user_id = state.user_service.create_user(&name).await?;
    Ok(format!("Created user with ID: {}", user_id))
}

#[instrument]
async fn metrics_handler(state: Arc<AppState>) -> String {
    state.telemetry.get_metrics()
}

pub async fn run_server(
    user_service: Arc<UserService>,
    telemetry: Arc<Telemetry>,
) -> Result<(), Box<dyn std::error::Error>> {
    let state = Arc::new(AppState {
        user_service,
        telemetry,
    });

    let app = Router::new()
        .route("/users/:id", get(get_user_handler))
        .route("/users", post(create_user_handler))
        .route("/metrics", get(metrics_handler))
        .with_state(state);

    axum::Server::bind(&"0.0.0.0:3000".parse().unwrap())
        .serve(app.into_make_service())
        .await?;

    Ok(())
}
```

### 6. 主程序入口

创建 `main.rs` 文件：

```rust
mod telemetry;
mod macros;
mod service;
mod server;

use std::sync::Arc;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化遥测
    let telemetry_config = telemetry::TelemetryConfig {
        service_name: "my-service".to_string(),
        service_version: env!("CARGO_PKG_VERSION").to_string(),
        environment: "development".to_string(),
    };
    let telemetry = Arc::new(telemetry::Telemetry::init(telemetry_config).await?);

    // 初始化服务
    let user_service = Arc::new(service::UserService::new(&telemetry.prometheus_registry));

    // 运行服务器
    server::run_server(user_service, telemetry).await?;

    // 清理
    opentelemetry::global::shutdown_tracer_provider();

    Ok(())
}
```

### 7. 使用示例

```rust
// 在任何异步函数中使用跟踪
async fn example_operation() -> Result<(), String> {
    let span = trace_async_fn!("example_operation");
    let _guard = span.enter();

    // 执行一些操作
    trace_async_op!("sub_operation", async {
        tokio::time::sleep(Duration::from_secs(1)).await;
        Ok(())
    })
    .await
}
```

### 8. 配置文件示例

创建 `.env` 文件：

```env
RUST_LOG=info,my_service=debug
OTEL_SERVICE_NAME=my-service
OTEL_EXPORTER_JAEGER_ENDPOINT=http://localhost:14268/api/traces
```

### 9. 设计规范

1. **日志级别使用规范**：
   - ERROR: 影响系统运行的错误
   - WARN: 可能影响系统但不致命的警告
   - INFO: 重要的业务事件
   - DEBUG: 调试信息
   - TRACE: 详细的跟踪信息

2. **Span 命名规范**：
   - 使用小写字母和下划线
   - 包含操作类型和对象
   - 例如：`get_user`、`create_user`、`update_profile`

3. **Metric 命名规范**：
   - 使用下划线分隔的小写字母
   - 包含单位信息（如适用）
   - 例如：`http_requests_total`、`response_time_seconds`

4. **标签（Tag）使用规范**：
   - 使用有意义的键值对
   - 避免使用过多标签
   - 例如：`environment`、`service_name`、`endpoint`

5. **上下文传播规范**：
   - 使用 `tracing::Span` 确保上下文正确传播
   - 在异步边界保持跟踪上下文

6. **错误处理规范**：
   - 使用结构化的错误类型
   - 在错误发生时记录详细信息
   - 包含错误上下文

### 10. 监控面板配置

创建 Grafana 仪表板配置：

```json
{
  "dashboard": {
    "panels": [
      {
        "title": "Request Rate",
        "type": "graph",
        "targets": [
          {
            "expr": "rate(http_requests_total[5m])",
            "legendFormat": "{{endpoint}}"
          }
        ]
      },
      {
        "title": "Error Rate",
        "type": "graph",
        "targets": [
          {
            "expr": "rate(http_errors_total[5m])",
            "legendFormat": "{{endpoint}}"
          }
        ]
      }
    ]
  }
}
```

这个完整的示例展示了如何在 Tokio 异步应用程序中实现全面的可观测性。它包括：

- 分布式跟踪（使用 OpenTelemetry 和 Jaeger）
- 度量收集（使用 Prometheus）
- 结构化日志记录（使用 tracing）
- 自定义跟踪宏
- 完整的错误处理
- 清晰的代码组织
- 标准的命名约定
- 监控配置

通过这种方式，您可以构建一个具有完整可观测性的生产级应用程序。

下面是一个详细的示例，展示如何在 Tokio 异步编程中结合 tracing 和 console 实现完整的日志跟踪和调试功能。

### *1. 项目依赖配置

首先在 `Cargo.toml` 中添加必要的依赖：

```toml
[dependencies]
tokio = { version = "1.0", features = ["full"] }
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
tracing-futures = "0.2"
console = "0.15"
chrono = "0.4"
colored = "2.0"
```

### 2. 自定义跟踪器实现

创建 `tracer.rs` 文件：

```rust
use std::sync::atomic::{AtomicUsize, Ordering};
use tracing::{span, Level};
use console::style;
use chrono::Local;

static INDENT_LEVEL: AtomicUsize = AtomicUsize::new(0);

pub struct AsyncTracer {
    name: String,
    start_time: std::time::Instant,
}

impl AsyncTracer {
    pub fn new(name: &str) -> Self {
        let indent = INDENT_LEVEL.fetch_add(1, Ordering::SeqCst);
        let indent_str = "  ".repeat(indent);
        let timestamp = Local::now().format("%H:%M:%S%.3f");
        
        println!("{}{} {} {}", 
            indent_str,
            style(timestamp).dim(),
            style("→").blue(),
            style(&name).cyan()
        );

        Self {
            name: name.to_string(),
            start_time: std::time::Instant::now(),
        }
    }
}

impl Drop for AsyncTracer {
    fn drop(&mut self) {
        let indent = INDENT_LEVEL.fetch_sub(1, Ordering::SeqCst) - 1;
        let indent_str = "  ".repeat(indent);
        let duration = self.start_time.elapsed();
        let timestamp = Local::now().format("%H:%M:%S%.3f");

        println!("{}{} {} {} {}",
            indent_str,
            style(timestamp).dim(),
            style("←").green(),
            style(&self.name).cyan(),
            style(format!("(took {:.2?})", duration)).yellow()
        );
    }
}

#[macro_export]
macro_rules! trace_async {
    ($name:expr) => {
        let _tracer = crate::tracer::AsyncTracer::new($name);
    };
}
```

### 3. 自定义日志格式化器

创建 `logger.rs` 文件：

```rust
use tracing_subscriber::{
    fmt::{format::Writer, time::FormatTime, Format},
    Layer,
};
use console::style;
use std::io;

pub struct CustomFormatter;

impl<S, N> tracing_subscriber::fmt::format::Format<S, N> for CustomFormatter
where
    S: tracing::Subscriber + for<'a> tracing_subscriber::registry::LookupSpan<'a>,
    N: for<'a> FormatTime,
{
    fn format_event(
        &self,
        ctx: &tracing_subscriber::fmt::FmtContext<'_, S, N>,
        mut writer: Writer<'_>,
        event: &tracing::Event<'_>,
    ) -> std::fmt::Result {
        // 获取时间戳
        let timestamp = Local::now().format("%H:%M:%S%.3f");
        write!(writer, "{} ", style(timestamp).dim())?;

        // 获取日志级别并着色
        let level = event.metadata().level();
        let level_str = match *level {
            Level::ERROR => style("ERROR").red(),
            Level::WARN => style("WARN ").yellow(),
            Level::INFO => style("INFO ").green(),
            Level::DEBUG => style("DEBUG").blue(),
            Level::TRACE => style("TRACE").purple(),
        };
        write!(writer, "{} ", level_str)?;

        // 获取目标（模块路径）
        if let Some(target) = event.metadata().target() {
            write!(writer, "{} ", style(target).dim())?;
        }

        // 获取 span 上下文
        if let Some(scope) = ctx.event_scope() {
            for span in scope.from_root() {
                write!(writer, "{}", style("→").blue())?;
                write!(writer, "{} ", span.name())?;
            }
        }

        // 写入事件消息
        event.record(&mut writer);
        writeln!(writer)
    }
}
```

### 4. 异步任务跟踪器

创建 `task_tracker.rs` 文件：

```rust
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::Mutex;
use tracing::{info, warn};

#[derive(Debug, Clone)]
pub struct TaskInfo {
    pub name: String,
    pub start_time: std::time::Instant,
    pub status: TaskStatus,
}

#[derive(Debug, Clone)]
pub enum TaskStatus {
    Running,
    Completed,
    Failed(String),
}

pub struct TaskTracker {
    tasks: Arc<Mutex<HashMap<String, TaskInfo>>>,
}

impl TaskTracker {
    pub fn new() -> Self {
        Self {
            tasks: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    pub async fn start_task(&self, task_id: &str, name: &str) {
        let mut tasks = self.tasks.lock().await;
        tasks.insert(
            task_id.to_string(),
            TaskInfo {
                name: name.to_string(),
                start_time: std::time::Instant::now(),
                status: TaskStatus::Running,
            },
        );
        info!(task_id = task_id, name = name, "Task started");
    }

    pub async fn complete_task(&self, task_id: &str) {
        let mut tasks = self.tasks.lock().await;
        if let Some(task) = tasks.get_mut(task_id) {
            task.status = TaskStatus::Completed;
            let duration = task.start_time.elapsed();
            info!(
                task_id = task_id,
                name = task.name,
                duration = ?duration,
                "Task completed"
            );
        }
    }

    pub async fn fail_task(&self, task_id: &str, error: &str) {
        let mut tasks = self.tasks.lock().await;
        if let Some(task) = tasks.get_mut(task_id) {
            task.status = TaskStatus::Failed(error.to_string());
            let duration = task.start_time.elapsed();
            warn!(
                task_id = task_id,
                name = task.name,
                error = error,
                duration = ?duration,
                "Task failed"
            );
        }
    }
}
```

### 5. 示例应用程序

创建 `main.rs` 文件：

```rust
mod tracer;
mod logger;
mod task_tracker;

use tracing::{info, instrument};
use std::time::Duration;

#[tokio::main]
async fn main() {
    // 初始化跟踪器
    init_tracing();

    let tracker = task_tracker::TaskTracker::new();
    
    // 执行一些异步任务
    let handles = vec![
        tokio::spawn(complex_operation("task1", tracker.clone())),
        tokio::spawn(complex_operation("task2", tracker.clone())),
        tokio::spawn(complex_operation("task3", tracker.clone())),
    ];

    // 等待所有任务完成
    for handle in handles {
        if let Err(e) = handle.await {
            eprintln!("Task failed: {}", e);
        }
    }
}

#[instrument]
async fn complex_operation(task_id: &str, tracker: task_tracker::TaskTracker) -> Result<(), String> {
    trace_async!("complex_operation");
    tracker.start_task(task_id, "Complex Operation").await;

    // 第一步操作
    if let Err(e) = step_one(task_id).await {
        tracker.fail_task(task_id, &e).await;
        return Err(e);
    }

    // 第二步操作
    if let Err(e) = step_two(task_id).await {
        tracker.fail_task(task_id, &e).await;
        return Err(e);
    }

    tracker.complete_task(task_id).await;
    Ok(())
}

#[instrument]
async fn step_one(task_id: &str) -> Result<(), String> {
    trace_async!("step_one");
    info!(task_id = task_id, "Executing step one");
    tokio::time::sleep(Duration::from_millis(100)).await;
    Ok(())
}

#[instrument]
async fn step_two(task_id: &str) -> Result<(), String> {
    trace_async!("step_two");
    info!(task_id = task_id, "Executing step two");
    tokio::time::sleep(Duration::from_millis(150)).await;
    Ok(())
}

fn init_tracing() {
    use tracing_subscriber::prelude::*;
    
    let fmt_layer = tracing_subscriber::fmt::layer()
        .with_target(true)
        .with_thread_ids(true)
        .with_line_number(true)
        .with_formatter(logger::CustomFormatter);

    let filter_layer = tracing_subscriber::EnvFilter::try_from_default_env()
        .unwrap_or_else(|_| tracing_subscriber::EnvFilter::new("debug"));

    tracing_subscriber::registry()
        .with(filter_layer)
        .with(fmt_layer)
        .init();
}
```

### 6. 使用示例

```rust
// 在异步函数中使用跟踪
#[instrument]
async fn example_async_function() {
    trace_async!("example_async_function");
    
    info!("Starting async operation");
    
    // 执行一些异步操作
    tokio::time::sleep(Duration::from_secs(1)).await;
    
    info!("Async operation completed");
}
```

### 7. 运行时环境变量配置

```bash
RUST_LOG=debug,my_app=trace
```

### 8. 输出示例

运行程序后，您将看到类似以下的输出：

```text
12:34:56.789 INFO  my_app → complex_operation
  12:34:56.790 INFO  my_app   → step_one
    Executing step one
  12:34:56.891 INFO  my_app   ← step_one (took 101ms)
  12:34:56.891 INFO  my_app   → step_two
    Executing step two
  12:34:57.042 INFO  my_app   ← step_two (took 151ms)
12:34:57.042 INFO  my_app ← complex_operation (took 253ms)
```

### 9. 调试功能

#### 1. **条件跟踪**

```rust
#[instrument(skip_all, fields(user_id = ?user.id))]
async fn process_user(user: User) {
    if cfg!(debug_assertions) {
        trace_async!("process_user");
    }
    // ... 处理逻辑
}
```

#### 2. **性能分析**

```rust
async fn measure_performance<F, Fut, T>(name: &str, f: F) -> T
where
    F: FnOnce() -> Fut,
    Fut: std::future::Future<Output = T>,
{
    let start = std::time::Instant::now();
    let result = f().await;
    let duration = start.elapsed();
    
    info!(
        operation = name,
        duration_ms = duration.as_millis(),
        "Performance measurement"
    );
    
    result
}
```

#### 3. **错误跟踪**

```rust
#[derive(Debug)]
pub struct TracedError {
    message: String,
    span_context: tracing::span::Context,
}

impl std::error::Error for TracedError {}

impl std::fmt::Display for TracedError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} (in span: {:?})", self.message, self.span_context)
    }
}
```

### 10. 最佳实践

#### 1. **使用有意义的 span 名称**

```rust
#[instrument(name = "user.authentication", skip(password))]
async fn authenticate_user(username: &str, password: &str) {
    // ...
}
```

#### 2. **结构化日志记录**

```rust
info!(
    user_id = user.id,
    action = "login",
    status = "success",
    "User successfully logged in"
);
```

#### 3. **错误处理与日志记录**

```rust
match operation().await {
    Ok(result) => info!(value = ?result, "Operation succeeded"),
    Err(e) => error!(error = ?e, "Operation failed"),
}
```

#### 4. **异步上下文传播**

```rust
async fn process_request(request_id: String) {
    let span = span!(Level::INFO, "request", id = %request_id);
    let _enter = span.enter();
    
    // 所有子操作都将继承这个 span 上下文
    process_step_one().await;
    process_step_two().await;
}
```

这个完整的示例展示了如何在 Tokio 异步应用程序中实现全面的日志跟踪和调试功能。它提供了：

- 结构化的日志记录
- 异步操作的可视化跟踪
- 性能测量
- 错误跟踪
- 调试工具
- 最佳实践指南

通过这种方式，您可以更好地理解和调试异步程序的行为。
