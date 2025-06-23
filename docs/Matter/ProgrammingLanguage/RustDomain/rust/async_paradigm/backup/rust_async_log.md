# rust_async_log

下面介绍如何在 Rust 异步编程中集成可追踪日志的方案，
包括常用的开源堆栈、如何实现按照日期打 tag、输出到本地并滚动存储（有时还需要对旧日志进行压缩），
以及如何通过内置机制将日志与函数调用的语义顺序关联起来。

## 1. 开源日志堆栈

在 Rust 中实现异步环境下的日志记录，常用的方案主要有两大类：

### 1.1 基于传统日志接口

- **log crate + 后端实现**  
  使用 [`log`](https://crates.io/crates/log) 统一管理日志输出，再配合例如 [env_logger](https://crates.io/crates/env_logger)
  或 [pretty_env_logger](https://crates.io/crates/pretty_env_logger) 来作为日志后端。  
  **特点：** 操作简单，但不具备自动化的上下文追踪和函数调用关系记录，且对于异步场景中跨 await 边界的日志串联支持较弱。

### 1.2 基于结构化日志与追踪

- **tracing 生态**  
  由 Tokio 团队开发的 [`tracing`](https://crates.io/crates/tracing) 系列库专为异步环境设计，提供了以下功能：
  
  - **Span 与 Event：**  
    - **Span（跨度）：** 显示一个函数或代码块的执行范围；通过创建 span，在进入和退出函数时自动记录上下文信息。  
    - **Event（事件）：** 在 span 内部记录离散的日志信息（如调用时的详细数据）。  
  - **`#[instrument]` 属性宏：**  
    自动在函数入口创建 span，并捕获函数名称、参数等信息，保证即使函数中存在多个 `.await` 调用，该 span 也能保持，从而使得日志输出可以对应实际调用链的语义顺序。  
  - **Subscriber：**  
    例如 [`tracing-subscriber`](https://crates.io/crates/tracing-subscriber) 负责编排、格式化以及输出追踪数据。  
  
- **扩展：分布式追踪**  
  如果需要跨服务的追踪，还可以结合 [tracing-opentelemetry](https://crates.io/crates/tracing-opentelemetry) 和
  [opentelemetry-rust](https://crates.io/crates/opentelemetry) 将日志和追踪信息上报到 Jaeger、Zipkin 等系统。

- **其它方案：**  
  [slog](https://crates.io/crates/slog) 也是一种结构化日志系统，但在异步场景和自动上下文传播上，当前业内更推荐使用 tracing。

## 2. 按照日期打 Tag、输出压缩文件、本地滚动存储

为实现日志按日期分文件存储、自动滚动（例如每天一个文件）以及对旧日志进行压缩归档，可采用以下方案：

### 2.1 使用 tracing-appender

- **tracing-appender**  
  提供了简单的日志滚动策略，可以基于每日（或每小时等）滚动日志文件。例如：

  ```rust
  use tracing_appender::rolling::{RollingFileAppender, Rotation};
  use tracing_subscriber::fmt::writer::MakeWriterExt;

  // 创建每天旋转的文件，文件将存放在 "logs" 目录下，主日志文件名为 "app.log"
  let file_appender = RollingFileAppender::new(Rotation::DAILY, "logs", "app.log");
  // 构建非阻塞日志写入器
  let (non_blocking, _guard) = tracing_appender::non_blocking(file_appender);

  // 配置 Subscriber，将日志输出到非阻塞写入器，同时可结合控制台输出
  tracing_subscriber::fmt()
      .with_writer(non_blocking.and(std::io::stdout))
      .init();
  ```

- **压缩与归档**  
  目前 `tracing-appender` 本身不内置文件压缩功能。如果需要把滚动后的日志文件压缩（例如以日期作为 tag 后缀，同时自动生成 zip 或 tar.gz 文件），可以采用以下思路：
  
  - **后处理脚本：**  
    配合 cron 定时任务或后台线程监控日志目录，对旧日志文件按日期进行压缩归档。  
  - **第三方库：**  
    可以使用类似 [flexi_logger](https://crates.io/crates/flexi_logger) 的日志库，其内置支持日志滚动和压缩（不过 flexi_logger 的 async 适配能力较 tracing 稍逊，需根据项目需求做权衡）。

### 2.2 基于 flexi_logger

- **flexi_logger**  
  该库除了内置异步支持外，还支持文件滚动、命名、压缩归档等高级功能。  
  使用示例（简化版）：

  ```rust
  use flexi_logger::{Logger, Cleanup};
  
  fn main() {
      Logger::try_with_str("info")
          .unwrap()
          .log_to_file()
          .directory("logs")
          .rotate(
              flexi_logger::Criterion::Daily,
              flexi_logger::Naming::Timestamps,   // 日志文件中将嵌入日期 tag
              flexi_logger::Cleanup::KeepLogFiles(30), // 保留最近 30 天的日志
          )
          .compress();  // 启用压缩功能
      // 初始化后，后续使用 log crate 输出日志
      log::info!("程序启动");
  }
  ```

  *注意：* flexi_logger 可直接与 log 宏联用，对于一些简单的异步场景也能满足要求，但对于复杂的异步追踪，上面提到的 tracing 体系通常是首选。

## 3. 日志与函数调用语义顺序关联机制

在异步代码中，由于存在多次 await、任务切换等问题，要准确反映函数调用的语义顺序，可以依靠以下机制：

### 3.1 使用 Span

- **Span 的作用**  
  通过在函数开始时创建 span，记录进入函数、离开函数以及期间发生的事件，能够将整个函数调用过程“围起来”。
  当函数内有 await 调用时，该 span 依然存续，从而保证日志记录对应到函数调用的完整语义。

### 3.2 #[instrument] 属性宏

- **自动创建 span**  
  在异步函数上使用 `#[instrument]` 宏，能够自动生成一个 span，该 span 记录了函数名称、参数值等信息。例如：

  ```rust
  use tracing::{info, instrument};

  #[instrument]
  async fn my_async_function(arg: u32) {
      info!("进入 my_async_function");
      // 执行异步任务
      tokio::time::sleep(std::time::Duration::from_millis(100)).await;
      info!("结束 my_async_function");
  }
  ```

  这样，每次调用 `my_async_function` 时，框架将自动生成 span，并在 span 中嵌套所有内部的 event，可以清晰地还原函数调用的层级和执行顺序。

### 3.3 Subscriber 格式化输出

- **层级化显示**  
  配置 `tracing-subscriber` 时，可以选择合适的输出格式（例如树形结构），使得每个 span 的开始和结束能以层级关系显示，便于追踪调用链。

## 4. 思维导图总结

下面给出一个 Mermaid 思维导图，总结了 Rust async 中日志集成、滚动和函数调用语义关联机制：

```mermaid
flowchart TD
    A[Rust Async 日志集成]
    
    A --> B[开源堆栈]
    B --> B1[传统日志: log + env_logger]
    B --> B2[结构化追踪: tracing, tracing-subscriber]
    B --> B3[分布式追踪: tracing-opentelemetry + opentelemetry-rust]
    B --> B4[其它备选: slog, flexi_logger]
    
    A --> C[日志输出与滚动存储]
    C --> C1[tracing-appender]
    C1 --> C1a[支持基于时间（例如每日）的滚动文件]
    C1 --> C1b[可结合非阻塞写入和终端输出]
    C --> C2[flexi_logger]
    C2 --> C2a[内置文件滚动、日期 tag、压缩归档]
    
    A --> D[日志对应调用语义顺序]
    D --> D1[Span 记录函数调用上下文]
    D --> D2[#[instrument] 自动生成 Span]
    D --> D3[Subscriber 格式化显示层级调用关系]
```

## 5. 总结

1. **开源堆栈选择：**  
   推荐在异步程序中优先使用 `tracing` 生态，利用 `tracing-subscriber` 进行结构化记录；同时可结合 `tracing-appender` 实现基于时间的滚动存储。
   若需要同时具备内置压缩、日期 tag 等特性，则可考虑使用 `flexi_logger`（注意根据项目场景权衡其异步适配能力）。

2. **日志滚动与存储：**  
   - 使用 `tracing-appender` 可实现每日滚动，文件自动放在指定目录中。  
   - 若需要压缩归档，通常需要额外的处理（如 flexi_logger 内置支持或后续脚本处理）。

3. **日志与调用顺序关联：**  
   - 利用 Span 与 `#[instrument]` 属性自动捕获函数调用的上下文，从而在生成的结构化日志中体现清晰的调用链和语义顺序。

通过以上机制，可以在 Rust 的 async 编程中实现一个完整的、可跟踪的日志系统，满足开发、调试与运维对日志全面、清晰记录的要求。
