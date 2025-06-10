# Rust异步日志

要实现一个基于 Tokio 和异步日志的 OpenTelemetry 架构，您需要实现以下功能：

1. **初始化 OpenTelemetry**：设置 OpenTelemetry 的全局配置，包括导出器和采样策略。

2. **创建 Tracer**：用于生成跟踪信息的 Tracer。

3. **创建 Span**：在代码中创建和管理 Span，以便跟踪操作的开始和结束。

4. **记录日志**：使用异步日志记录与 Span 相关的日志信息。

5. **导出跟踪数据**：将跟踪数据导出到后端（如 Jaeger、Zipkin 或其他支持的后端）。

6. **上下文传播**：在异步操作中传播上下文，以确保 Span 和 Trace ID 在不同的任务之间保持一致。

7. **错误处理**：处理在跟踪和日志记录过程中可能出现的错误。

以下是一个简单的示例，展示如何使用 Tokio、异步日志和 OpenTelemetry 实现这些功能。

## 目录

- [Rust异步日志](#rust异步日志)
  - [目录](#目录)
  - [1. 初始化 OpenTelemetry](#1-初始化-opentelemetry)
    - [2. 创建 Tracer](#2-创建-tracer)
    - [3. 创建 Span](#3-创建-span)
    - [4. 记录日志](#4-记录日志)
    - [5. 导出跟踪数据](#5-导出跟踪数据)
    - [6. 上下文传播](#6-上下文传播)
    - [7. 错误处理](#7-错误处理)
    - [总结](#总结)
    - [1. 项目依赖配置](#1-项目依赖配置)
    - [2. 日志管理器实现](#2-日志管理器实现)
    - [3. 跟踪器实现](#3-跟踪器实现)
    - [4. 执行跟踪器实现](#4-执行跟踪器实现)
    - [5. 异步任务跟踪器](#5-异步任务跟踪器)
    - [6. 使用示例](#6-使用示例)
    - [7. 错误处理和调试工具](#7-错误处理和调试工具)
    - [8. 日志分析工具](#8-日志分析工具)
    - [9. 配置示例](#9-配置示例)
    - [10. 使用示例](#10-使用示例)

## 1. 初始化 OpenTelemetry

首先，您需要在 `Cargo.toml` 中添加所需的依赖项：

```toml
[dependencies]
tokio = { version = "1", features = ["full"] }
opentelemetry = { version = "0.18", features = ["trace", "log"] }
opentelemetry-jaeger = "0.18"
log = "0.4"
env_logger = "0.10"
```

### 2. 创建 Tracer

在应用程序的入口点，初始化 OpenTelemetry 和日志记录：

```rust
use opentelemetry::{global, sdk::trace as sdktrace, trace::Tracer};
use opentelemetry_jaeger::Exporter;
use std::sync::Arc;

#[tokio::main]
async fn main() {
    // 初始化日志记录
    env_logger::init();

    // 初始化 OpenTelemetry
    let tracer = init_tracer().await;

    // 使用 Tracer 进行跟踪
    let span = tracer.start("main_span");
    let _guard = span.enter();

    // 记录日志
    log::info!("Starting the application...");

    // 其他业务逻辑
    // ...

    // 结束 Span
    drop(_guard);
    span.end();
    
    // 关闭 OpenTelemetry
    global::shutdown_tracer_provider();
}

async fn init_tracer() -> Arc<dyn Tracer> {
    let exporter = opentelemetry_jaeger::Exporter::builder()
        .with_agent_endpoint("127.0.0.1:6831")
        .with_service_name("my_service")
        .init()
        .await
        .expect("Failed to initialize Jaeger exporter");

    let tracer_provider = sdktrace::TracerProvider::builder()
        .with_simple_exporter(exporter)
        .build();

    global::set_tracer_provider(tracer_provider);
    global::tracer("my_tracer")
}
```

### 3. 创建 Span

在业务逻辑中创建 Span：

```rust
async fn perform_task(tracer: Arc<dyn Tracer>) {
    let span = tracer.start("perform_task_span");
    let _guard = span.enter();

    // 记录日志
    log::info!("Performing a task...");

    // 模拟异步操作
    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;

    // 结束 Span
    drop(_guard);
    span.end();
}
```

### 4. 记录日志

在 Span 内部记录日志信息：

```rust
async fn another_task(tracer: Arc<dyn Tracer>) {
    let span = tracer.start("another_task_span");
    let _guard = span.enter();

    log::info!("Starting another task...");

    // 模拟异步操作
    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;

    log::info!("Finished another task.");
    
    // 结束 Span
    drop(_guard);
    span.end();
}
```

### 5. 导出跟踪数据

在 `init_tracer` 函数中，您已经设置了 Jaeger 导出器。确保 Jaeger 代理正在运行并监听指定的端口。

### 6. 上下文传播

在异步操作中，您可以使用 `opentelemetry::Context` 来传播上下文。以下是一个示例：

```rust
async fn context_propagation_example(tracer: Arc<dyn Tracer>) {
    let span = tracer.start("context_propagation_span");
    let _guard = span.enter();

    // 记录日志
    log::info!("Context propagation example...");

    // 调用另一个异步函数
    another_task(tracer.clone()).await;

    // 结束 Span
    drop(_guard);
    span.end();
}
```

### 7. 错误处理

在跟踪和日志记录过程中，您可以使用 `Result` 类型来处理错误。例如：

```rust
async fn risky_operation() -> Result<(), String> {
    // 模拟可能失败的操作
    if rand::random::<u8>() % 2 == 0 {
        Err("Operation failed".to_string())
    } else {
        Ok(())
    }
}

async fn perform_risky_operation(tracer: Arc<dyn Tracer>) {
    let span = tracer.start("risky_operation_span");
    let _guard = span.enter();

    match risky_operation().await {
        Ok(_) => log::info!("Risky operation succeeded."),
        Err(e) => log::error!("Risky operation failed: {}", e),
    }

    // 结束 Span
    drop(_guard);
    span.end();
}
```

### 总结

通过以上步骤，您可以使用 Tokio 和异步日志结合 OpenTelemetry 实现一个完整的监控架构。
您可以根据需要扩展和修改这些示例，以适应您的具体应用场景。确保在生产环境中使用适当的错误处理和日志记录策略，以便更好地监控和调试应用程序。

下面是一个详细的示例，展示如何使用 Tokio、tracing、tracing-subscriber 和 console 实现日志的滚动覆盖、压缩存储以及跟踪程序执行顺序的功能。

### 1. 项目依赖配置

```toml
[dependencies]
tokio = { version = "1.0", features = ["full"] }
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
tracing-appender = "0.2"
console = "0.15"
chrono = "0.4"
serde_json = "1.0"
rolling-file = "0.2"
flate2 = "1.0"
```

### 2. 日志管理器实现

```rust
use std::path::PathBuf;
use std::sync::Arc;
use tokio::sync::Mutex;
use tracing_appender::rolling::{RollingFileAppender, Rotation};
use flate2::write::GzEncoder;
use flate2::Compression;

pub struct LogManager {
    log_dir: PathBuf,
    max_files: usize,
    current_file: Arc<Mutex<RollingFileAppender>>,
}

impl LogManager {
    pub fn new(log_dir: PathBuf, max_files: usize) -> Self {
        std::fs::create_dir_all(&log_dir).unwrap();
        
        let appender = RollingFileAppender::new(
            Rotation::DAILY,
            log_dir.clone(),
            "application.log",
        );

        Self {
            log_dir,
            max_files,
            current_file: Arc::new(Mutex::new(appender)),
        }
    }

    pub async fn rotate_logs(&self) {
        let pattern = format!("{}/application-*.log", self.log_dir.display());
        let mut files: Vec<PathBuf> = glob::glob(&pattern)
            .unwrap()
            .filter_map(Result::ok)
            .collect();
            
        files.sort();

        // 压缩旧日志文件
        while files.len() >= self.max_files {
            if let Some(old_file) = files.first() {
                self.compress_log(old_file).await;
                if let Err(e) = std::fs::remove_file(old_file) {
                    eprintln!("Failed to remove old log file: {}", e);
                }
                files.remove(0);
            }
        }
    }

    async fn compress_log(&self, file_path: &PathBuf) {
        let input = std::fs::File::open(file_path).unwrap();
        let gz_path = file_path.with_extension("log.gz");
        let output = std::fs::File::create(&gz_path).unwrap();
        
        let mut encoder = GzEncoder::new(output, Compression::default());
        std::io::copy(&mut std::io::BufReader::new(input), &mut encoder).unwrap();
        encoder.finish().unwrap();
    }
}
```

### 3. 跟踪器实现

```rust
use tracing::{span, Level, Subscriber};
use tracing_subscriber::{fmt, layer::SubscriberExt, Registry};
use console::style;

pub struct TracingManager {
    log_manager: Arc<LogManager>,
}

impl TracingManager {
    pub fn new(log_manager: Arc<LogManager>) -> Self {
        Self { log_manager }
    }

    pub fn init(&self) {
        let file_appender = self.log_manager.current_file.clone();
        
        // 文件输出层
        let file_layer = fmt::layer()
            .with_target(true)
            .with_thread_ids(true)
            .with_line_number(true)
            .with_file(true)
            .with_writer(file_appender);

        // 控制台输出层
        let console_layer = fmt::layer()
            .with_target(true)
            .with_ansi(true)
            .with_thread_ids(true)
            .with_line_number(true)
            .with_file(true)
            .with_writer(std::io::stdout)
            .with_formatter(CustomFormatter);

        // 环境过滤器
        let filter_layer = tracing_subscriber::EnvFilter::try_from_default_env()
            .unwrap_or_else(|_| tracing_subscriber::EnvFilter::new("debug"));

        // 注册订阅者
        Registry::default()
            .with(filter_layer)
            .with(console_layer)
            .with(file_layer)
            .init();
    }
}

struct CustomFormatter;

impl<S, N> fmt::FormatEvent<S, N> for CustomFormatter
where
    S: Subscriber + for<'a> tracing_subscriber::registry::LookupSpan<'a>,
    N: for<'a> fmt::FormatTime,
{
    fn format_event(
        &self,
        ctx: &fmt::FmtContext<'_, S, N>,
        mut writer: fmt::format::Writer<'_>,
        event: &tracing::Event<'_>,
    ) -> std::fmt::Result {
        let metadata = event.metadata();
        
        // 时间戳
        let timestamp = chrono::Local::now().format("%Y-%m-%d %H:%M:%S%.3f");
        write!(writer, "{} ", style(timestamp).dim())?;

        // 日志级别
        let level = match *metadata.level() {
            Level::ERROR => style("ERROR").red(),
            Level::WARN => style("WARN ").yellow(),
            Level::INFO => style("INFO ").green(),
            Level::DEBUG => style("DEBUG").blue(),
            Level::TRACE => style("TRACE").purple(),
        };
        write!(writer, "{} ", level)?;

        // 目标和位置信息
        if let Some(file) = metadata.file() {
            if let Some(line) = metadata.line() {
                write!(writer, "{}:{} ", style(file).dim(), style(line).dim())?;
            }
        }

        // 消息
        event.record(&mut writer);
        writeln!(writer)
    }
}
```

### 4. 执行跟踪器实现

```rust
use std::time::Instant;
use tracing::{info, warn, error};

pub struct ExecutionTracer {
    start_time: Instant,
    name: String,
    depth: usize,
}

impl ExecutionTracer {
    pub fn new(name: &str) -> Self {
        let depth = DEPTH.with(|d| {
            let mut d = d.borrow_mut();
            *d += 1;
            *d
        });

        let indent = "  ".repeat(depth - 1);
        info!("{}→ Starting {}", indent, name);

        Self {
            start_time: Instant::now(),
            name: name.to_string(),
            depth,
        }
    }
}

impl Drop for ExecutionTracer {
    fn drop(&mut self) {
        let duration = self.start_time.elapsed();
        let indent = "  ".repeat(self.depth - 1);
        
        info!(
            "{}← Completed {} (took {:?})",
            indent,
            self.name,
            duration
        );

        DEPTH.with(|d| {
            let mut d = d.borrow_mut();
            *d -= 1;
        });
    }
}

thread_local! {
    static DEPTH: std::cell::RefCell<usize> = std::cell::RefCell::new(0);
}
```

### 5. 异步任务跟踪器

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

pub struct AsyncTaskTracer<F: Future> {
    future: F,
    name: String,
    start_time: Option<Instant>,
}

impl<F: Future> AsyncTaskTracer<F> {
    pub fn new(name: &str, future: F) -> Self {
        Self {
            future,
            name: name.to_string(),
            start_time: None,
        }
    }
}

impl<F: Future> Future for AsyncTaskTracer<F> {
    type Output = F::Output;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        if self.start_time.is_none() {
            self.start_time = Some(Instant::now());
            info!("Starting async task: {}", self.name);
        }

        let future = unsafe { self.get_unchecked_mut() };
        let result = unsafe { Pin::new_unchecked(&mut future.future) }.poll(cx);

        if result.is_ready() {
            let duration = self.start_time.unwrap().elapsed();
            info!("Completed async task: {} (took {:?})", self.name, duration);
        }

        result
    }
}
```

### 6. 使用示例

```rust
#[tokio::main]
async fn main() {
    // 初始化日志管理器
    let log_manager = Arc::new(LogManager::new(
        PathBuf::from("logs"),
        5, // 保留最近5个日志文件
    ));

    // 初始化跟踪器
    let tracing_manager = TracingManager::new(log_manager.clone());
    tracing_manager.init();

    // 执行一些异步任务
    let task1 = async {
        let _trace = ExecutionTracer::new("Task 1");
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        nested_task().await;
    };

    let task2 = async {
        let _trace = ExecutionTracer::new("Task 2");
        tokio::time::sleep(tokio::time::Duration::from_millis(200)).await;
    };

    // 使用异步任务跟踪器
    let traced_task1 = AsyncTaskTracer::new("Task 1", task1);
    let traced_task2 = AsyncTaskTracer::new("Task 2", task2);

    // 并发执行任务
    tokio::join!(traced_task1, traced_task2);

    // 轮换日志文件
    log_manager.rotate_logs().await;
}

async fn nested_task() {
    let _trace = ExecutionTracer::new("Nested Task");
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
}
```

### 7. 错误处理和调试工具

```rust
pub struct DebugInfo {
    pub timestamp: chrono::DateTime<chrono::Local>,
    pub thread_id: std::thread::ThreadId,
    pub file: &'static str,
    pub line: u32,
}

#[macro_export]
macro_rules! debug_trace {
    ($msg:expr) => {
        let info = DebugInfo {
            timestamp: chrono::Local::now(),
            thread_id: std::thread::current().id(),
            file: file!(),
            line: line!(),
        };
        tracing::debug!(
            message = $msg,
            timestamp = %info.timestamp,
            thread_id = ?info.thread_id,
            file = info.file,
            line = info.line,
        );
    };
}

pub fn setup_panic_hook() {
    std::panic::set_hook(Box::new(|panic_info| {
        let backtrace = std::backtrace::Backtrace::capture();
        error!(
            panic = ?panic_info,
            backtrace = ?backtrace,
            "Program panic occurred"
        );
    }));
}
```

### 8. 日志分析工具

```rust
pub struct LogAnalyzer {
    log_dir: PathBuf,
}

impl LogAnalyzer {
    pub fn new(log_dir: PathBuf) -> Self {
        Self { log_dir }
    }

    pub async fn analyze_logs(&self) -> Result<LogStats, Box<dyn std::error::Error>> {
        let mut stats = LogStats::default();
        let pattern = format!("{}/application-*.log*", self.log_dir.display());
        
        for entry in glob::glob(&pattern)? {
            let path = entry?;
            let content = if path.extension().map_or(false, |ext| ext == "gz") {
                self.read_gz_file(&path)?
            } else {
                tokio::fs::read_to_string(&path).await?
            };

            self.process_log_content(&content, &mut stats);
        }

        Ok(stats)
    }

    fn read_gz_file(&self, path: &PathBuf) -> Result<String, Box<dyn std::error::Error>> {
        let file = std::fs::File::open(path)?;
        let decoder = flate2::read::GzDecoder::new(file);
        let mut content = String::new();
        std::io::Read::read_to_string(&mut std::io::BufReader::new(decoder), &mut content)?;
        Ok(content)
    }

    fn process_log_content(&self, content: &str, stats: &mut LogStats) {
        for line in content.lines() {
            if line.contains("ERROR") {
                stats.error_count += 1;
            } else if line.contains("WARN") {
                stats.warn_count += 1;
            }
            // 添加更多分析逻辑...
        }
    }
}

#[derive(Default)]
pub struct LogStats {
    pub error_count: usize,
    pub warn_count: usize,
    // 添加更多统计字段...
}
```

### 9. 配置示例

```rust
use serde::Deserialize;

#[derive(Deserialize)]
pub struct LogConfig {
    pub log_dir: String,
    pub max_files: usize,
    pub rotation_size: u64,
    pub compression_level: u32,
    pub log_level: String,
}

impl LogConfig {
    pub fn from_file(path: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let content = std::fs::read_to_string(path)?;
        Ok(toml::from_str(&content)?)
    }
}
```

### 10. 使用示例

```rust
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 加载配置
    let config = LogConfig::from_file("config/logging.toml")?;

    // 设置panic钩子
    setup_panic_hook();

    // 初始化日志系统
    let log_manager = Arc::new(LogManager::new(
        PathBuf::from(&config.log_dir),
        config.max_files,
    ));
    let tracing_manager = TracingManager::new(log_manager.clone());
    tracing_manager.init();

    // 执行一些操作
    let result = run_with_tracing().await;

    // 分析日志
    let analyzer = LogAnalyzer::new(PathBuf::from(&config.log_dir));
    let stats = analyzer.analyze_logs().await?;
    
    println!("Log analysis results:");
    println!("  Errors: {}", stats.error_count);
    println!("  Warnings: {}", stats.warn_count);

    result
}

async fn run_with_tracing() -> Result<(), Box<dyn std::error::Error>> {
    let _trace = ExecutionTracer::new("main_operation");
    
    debug_trace!("Starting main operation");
    
    // 执行一些异步操作...
    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
    
    debug_trace!("Main operation completed");
    Ok(())
}
```

这个完整的示例展示了如何：

1. 实现日志的滚动覆盖和压缩存储
2. 跟踪异步程序的执行顺序
3. 提供详细的调试信息
4. 分析日志文件
5. 处理错误和异常情况
6. 提供可配置的日志系统

通过这种方式，您可以构建一个强大的日志和调试系统，帮助您更好地理解和调试异步程序。
