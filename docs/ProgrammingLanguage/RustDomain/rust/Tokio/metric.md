# Rust实现异步的metric

下面是一个结合 Tokio、tracing、console 和 OpenTelemetry 实现完整的异步调用跟踪和度量的示例：

## 目录

- [Rust实现异步的metric](#rust实现异步的metric)
  - [目录](#目录)
  - [1. 项目依赖配置](#1-项目依赖配置)
    - [2. 度量收集器实现](#2-度量收集器实现)
    - [3. 异步跟踪器实现](#3-异步跟踪器实现)
    - [4. 请求上下文实现](#4-请求上下文实现)
    - [5. 业务服务实现](#5-业务服务实现)
    - [6. HTTP 服务器实现](#6-http-服务器实现)
    - [7. 主程序入口](#7-主程序入口)
    - [8. 使用示例](#8-使用示例)
    - [9. Prometheus 查询示例](#9-prometheus-查询示例)
    - [10. Grafana 仪表板配置](#10-grafana-仪表板配置)

## 1. 项目依赖配置

```toml
[dependencies]
tokio = { version = "1.0", features = ["full"] }
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
tracing-opentelemetry = "0.18"
opentelemetry = { version = "0.18", features = ["rt-tokio"] }
opentelemetry-prometheus = "0.11"
prometheus = "0.13"
console = "0.15"
chrono = "0.4"
```

### 2. 度量收集器实现

```rust
use prometheus::{
    Counter, Histogram, HistogramOpts, IntCounter, IntCounterVec, IntGauge, Opts, Registry,
};
use std::sync::Arc;

pub struct Metrics {
    pub registry: Registry,
    pub request_counter: IntCounterVec,
    pub request_duration: Histogram,
    pub active_requests: IntGauge,
    pub error_counter: IntCounterVec,
}

impl Metrics {
    pub fn new() -> Arc<Self> {
        let registry = Registry::new();

        // 请求计数器
        let request_counter = IntCounterVec::new(
            Opts::new("request_total", "Total number of requests"),
            &["endpoint"],
        )
        .unwrap();
        registry.register(Box::new(request_counter.clone())).unwrap();

        // 请求持续时间
        let request_duration = Histogram::with_opts(
            HistogramOpts::new("request_duration_seconds", "Request duration in seconds")
        ).unwrap();
        registry.register(Box::new(request_duration.clone())).unwrap();

        // 活跃请求数
        let active_requests = IntGauge::new(
            "active_requests", 
            "Number of requests in progress"
        ).unwrap();
        registry.register(Box::new(active_requests.clone())).unwrap();

        // 错误计数器
        let error_counter = IntCounterVec::new(
            Opts::new("errors_total", "Total number of errors"),
            &["type"],
        )
        .unwrap();
        registry.register(Box::new(error_counter.clone())).unwrap();

        Arc::new(Self {
            registry,
            request_counter,
            request_duration,
            active_requests,
            error_counter,
        })
    }
}
```

### 3. 异步跟踪器实现

```rust
use std::time::Instant;
use tracing::{info, warn, error};

pub struct AsyncTracer {
    name: String,
    start_time: Instant,
    metrics: Arc<Metrics>,
}

impl AsyncTracer {
    pub fn new(name: &str, metrics: Arc<Metrics>) -> Self {
        let start_time = Instant::now();
        metrics.active_requests.inc();
        
        info!(operation = name, "Starting async operation");
        
        Self {
            name: name.to_string(),
            start_time,
            metrics,
        }
    }
}

impl Drop for AsyncTracer {
    fn drop(&mut self) {
        let duration = self.start_time.elapsed();
        self.metrics.active_requests.dec();
        self.metrics.request_duration.observe(duration.as_secs_f64());
        
        info!(
            operation = self.name,
            duration_ms = duration.as_millis(),
            "Completed async operation"
        );
    }
}
```

### 4. 请求上下文实现

```rust
use std::future::Future;
use tracing::Span;

pub struct RequestContext {
    pub trace_id: String,
    pub span: Span,
    pub metrics: Arc<Metrics>,
}

impl RequestContext {
    pub fn new(trace_id: String, metrics: Arc<Metrics>) -> Self {
        let span = tracing::span!(
            tracing::Level::INFO,
            "request",
            trace_id = %trace_id
        );
        
        Self {
            trace_id,
            span,
            metrics,
        }
    }

    pub async fn trace<F, Fut, T>(&self, name: &str, f: F) -> T
    where
        F: FnOnce() -> Fut,
        Fut: Future<Output = T>,
    {
        let _tracer = AsyncTracer::new(name, self.metrics.clone());
        let _guard = self.span.enter();
        f().await
    }
}
```

### 5. 业务服务实现

```rust
pub struct UserService {
    metrics: Arc<Metrics>,
}

impl UserService {
    pub fn new(metrics: Arc<Metrics>) -> Self {
        Self { metrics }
    }

    pub async fn get_user(&self, ctx: &RequestContext, user_id: i32) -> Result<String, String> {
        ctx.trace("get_user", async move {
            self.metrics.request_counter.with_label_values(&["get_user"]).inc();
            
            // 模拟数据库查询
            tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
            
            Ok(format!("User {}", user_id))
        })
        .await
    }

    pub async fn create_user(
        &self,
        ctx: &RequestContext,
        name: String,
    ) -> Result<i32, String> {
        ctx.trace("create_user", async move {
            self.metrics.request_counter.with_label_values(&["create_user"]).inc();
            
            // 模拟数据库操作
            tokio::time::sleep(tokio::time::Duration::from_millis(200)).await;
            
            Ok(42)
        })
        .await
    }
}
```

### 6. HTTP 服务器实现

```rust
use axum::{
    extract::Path,
    routing::{get, post},
    Router,
};

pub struct AppState {
    user_service: Arc<UserService>,
    metrics: Arc<Metrics>,
}

async fn get_user_handler(
    Path(user_id): Path<i32>,
    State(state): State<Arc<AppState>>,
) -> Result<String, String> {
    let ctx = RequestContext::new(
        uuid::Uuid::new_v4().to_string(),
        state.metrics.clone(),
    );
    
    state.user_service.get_user(&ctx, user_id).await
}

async fn create_user_handler(
    State(state): State<Arc<AppState>>,
    Json(payload): Json<CreateUserRequest>,
) -> Result<String, String> {
    let ctx = RequestContext::new(
        uuid::Uuid::new_v4().to_string(),
        state.metrics.clone(),
    );
    
    let user_id = state.user_service.create_user(&ctx, payload.name).await?;
    Ok(format!("Created user with ID: {}", user_id))
}

async fn metrics_handler(
    State(state): State<Arc<AppState>>,
) -> String {
    use prometheus::Encoder;
    let encoder = prometheus::TextEncoder::new();
    let metric_families = state.metrics.registry.gather();
    encoder.encode_to_string(&metric_families).unwrap()
}
```

### 7. 主程序入口

```rust
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化 tracing
    init_tracing()?;

    // 初始化 metrics
    let metrics = Metrics::new();

    // 初始化服务
    let user_service = Arc::new(UserService::new(metrics.clone()));

    // 创建应用状态
    let state = Arc::new(AppState {
        user_service,
        metrics: metrics.clone(),
    });

    // 创建路由
    let app = Router::new()
        .route("/users/:id", get(get_user_handler))
        .route("/users", post(create_user_handler))
        .route("/metrics", get(metrics_handler))
        .with_state(state);

    // 启动服务器
    println!("Server running on http://localhost:3000");
    axum::Server::bind(&"0.0.0.0:3000".parse().unwrap())
        .serve(app.into_make_service())
        .await?;

    Ok(())
}

fn init_tracing() -> Result<(), Box<dyn std::error::Error>> {
    use tracing_subscriber::prelude::*;
    
    let fmt_layer = tracing_subscriber::fmt::layer()
        .with_target(true)
        .with_thread_ids(true)
        .with_line_number(true);

    let filter_layer = tracing_subscriber::EnvFilter::try_from_default_env()
        .unwrap_or_else(|_| tracing_subscriber::EnvFilter::new("debug"));

    tracing_subscriber::registry()
        .with(filter_layer)
        .with(fmt_layer)
        .init();

    Ok(())
}
```

### 8. 使用示例

```rust
// 在任何异步函数中使用跟踪和度量
async fn example_operation(ctx: &RequestContext) -> Result<(), String> {
    ctx.trace("example_operation", async {
        // 增加计数器
        ctx.metrics.request_counter
            .with_label_values(&["example_operation"])
            .inc();
            
        // 执行操作
        tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
        
        if rand::random::<bool>() {
            ctx.metrics.error_counter
                .with_label_values(&["example_error"])
                .inc();
            Err("Random error".to_string())
        } else {
            Ok(())
        }
    })
    .await
}
```

### 9. Prometheus 查询示例

```promql
# 请求总数
rate(request_total[5m])

# 请求持续时间
histogram_quantile(0.95, rate(request_duration_seconds_bucket[5m]))

# 活跃请求数
active_requests

# 错误率
rate(errors_total[5m])
```

### 10. Grafana 仪表板配置

```json
{
  "dashboard": {
    "panels": [
      {
        "title": "Request Rate",
        "type": "graph",
        "targets": [
          {
            "expr": "rate(request_total[5m])",
            "legendFormat": "{{endpoint}}"
          }
        ]
      },
      {
        "title": "Request Duration",
        "type": "graph",
        "targets": [
          {
            "expr": "histogram_quantile(0.95, rate(request_duration_seconds_bucket[5m]))",
            "legendFormat": "p95"
          }
        ]
      },
      {
        "title": "Active Requests",
        "type": "gauge",
        "targets": [
          {
            "expr": "active_requests",
            "legendFormat": "active"
          }
        ]
      },
      {
        "title": "Error Rate",
        "type": "graph",
        "targets": [
          {
            "expr": "rate(errors_total[5m])",
            "legendFormat": "{{type}}"
          }
        ]
      }
    ]
  }
}
```

这个完整的示例展示了如何：

1. 使用 tracing 进行异步操作的跟踪
2. 使用 Prometheus 进行度量收集
3. 实现请求上下文和跟踪器
4. 在业务逻辑中集成跟踪和度量
5. 提供度量指标的 HTTP 端点
6. 配置 Prometheus 查询和 Grafana 仪表板

通过这种方式，您可以全面监控异步应用程序的性能和行为。
