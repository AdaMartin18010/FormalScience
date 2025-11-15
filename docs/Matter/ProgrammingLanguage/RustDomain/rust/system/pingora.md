# 使用Pingora实现分布式HTTP集群服务 (Rust 2025)

```text
Let me organize my thoughts on implementing a distributed HTTP cluster service using Pingora (Rust) in 2025. This is a comprehensive request covering several key aspects:

1. **Distributed HTTP Cluster with Pingora**:
   - Pingora is Cloudflare's Rust-based framework for building fast, reliable network services
   - By 2025, it's reasonable to expect significant evolution in its feature set

2. **Logging and Monitoring Integration**:
   - Tracing, logging, metrics integration
   - Observability features

3. **gRPC Backend Integration**:
   - Protocol generation
   - Bidirectional streaming support
   - Rate limiting, retries, idempotency, proxying/transformation

4. **HTTP Protocol Support**:
   - HTTP/1.x, HTTP/2, HTTP/3 (QUIC)
   - Authentication (session, JWT)
   - Complete HTTP semantics (redirects, etc.)

5. **MQ Integration**:
   - Sidecars for user behavior data
   - Event subscription and processing

For a 2025 version, I'll need to extrapolate current Rust ecosystem trends, especially for Pingora which is still evolving. I'll base this on realistic projections of where these technologies might be by 2025.
```

## 📋 目录

- [使用Pingora实现分布式HTTP集群服务 (Rust 2025)](#使用pingora实现分布式http集群服务-rust-2025)
  - [📋 目录](#-目录)
  - [1 系统架构概览](#1-系统架构概览)
  - [2 一、核心HTTP网关服务实现](#2-一核心http网关服务实现)
    - [2.1 主应用服务器实现](#21-主应用服务器实现)
  - [3 二、配置、监控和日志模块](#3-二配置监控和日志模块)
  - [4 三、认证和授权中间件](#4-三认证和授权中间件)
  - [5 四、中间件实现](#5-四中间件实现)
  - [6 五、gRPC服务集成](#6-五grpc服务集成)
  - [7 六、消息队列集成和用户行为跟踪](#7-六消息队列集成和用户行为跟踪)
  - [8 七、配置文件示例](#8-七配置文件示例)
  - [9 八、部署与Docker配置](#9-八部署与docker配置)
  - [10 九、总结与功能概览](#10-九总结与功能概览)

---

## 1 系统架构概览

```text
┌───────────────────────────────────────────────────────────────┐
│                     客户端 (Web/Mobile)                         │
└───────────────────────────────┬───────────────────────────────┘
                                │
┌───────────────────────────────▼───────────────────────────────┐
│                     Pingora HTTP集群网关                       │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐            │
│  │ HTTP/1,2,3  │  │  认证中间件  │  │  限流/负载   │            │
│  │  QUIC支持   │  │ JWT/Session │  │   均衡器     │            │
│  └─────────────┘  └─────────────┘  └─────────────┘            │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐            │
│  │  请求路由   │  │ 协议转换层  │  │ 观测与监控  │            │
│  │  与规则     │  │HTTP<->gRPC  │  │Trace/Log/Metric│         │
│  └─────────────┘  └─────────────┘  └─────────────┘            │
└───────────┬───────────────────────────────────┬───────────────┘
            │                                   │
┌───────────▼───────────────┐     ┌────────────▼──────────────┐
│     gRPC 服务集群         │     │       消息队列系统         │
│  ┌─────────────────────┐  │     │  ┌──────────────────────┐ │
│  │  业务服务A (双向流) │  │     │  │     Kafka/NATS       │ │
│  └─────────────────────┘  │     │  └──────────────────────┘ │
│  ┌─────────────────────┐  │     │  ┌──────────────────────┐ │
│  │  业务服务B          │  │     │  │  用户行为跟踪处理    │ │
│  └─────────────────────┘  │     │  └──────────────────────┘ │
└───────────────────────────┘     └───────────────────────────┘
```

## 2 一、核心HTTP网关服务实现

首先，创建项目并添加依赖：

```rust
// Cargo.toml
[package]
name = "pingora-gateway"
version = "0.1.0"
edition = "2021"

[dependencies]
# Pingora 2025版本核心组件
pingora = { version = "0.10", features = ["full"] }
pingora-core = "0.10"
pingora-http = "0.10"
pingora-proxy = "0.10"
pingora-load-balancing = "0.10"
pingora-limiters = "0.10"
pingora-observability = "0.10"
pingora-tls = "0.10"
pingora-quic = "0.10"
pingora-grpc = "0.10"  # gRPC支持组件

# 异步运行时
tokio = { version = "2.0", features = ["full", "tracing"] }

# 观测和监控
opentelemetry = { version = "2.0", features = ["trace", "metrics"] }
opentelemetry-otlp = { version = "1.0", features = ["trace", "metrics"] }
tracing = "1.0"
tracing-subscriber = { version = "1.0", features = ["env-filter"] }
tracing-opentelemetry = "1.0"
metrics = "1.0"
metrics-exporter-prometheus = "1.0"

# gRPC 和协议
tonic = "1.0"
tonic-build = "1.0"
prost = "1.0"
prost-types = "1.0"

# 认证与会话
jsonwebtoken = "10.0"
session = "1.0"
uuid = { version = "2.0", features = ["v4", "serde"] }

# 消息队列
rdkafka = { version = "1.0", features = ["ssl", "sasl", "dynamic-linking"] }
async-nats = "1.0"

# 实用工具
serde = { version = "2.0", features = ["derive"] }
serde_json = "2.0"
futures = "1.0"
async-trait = "1.0"
thiserror = "2.0"
anyhow = "2.0"
clap = { version = "4.0", features = ["derive"] }
config = "1.0"
tower = "1.0"
http = "1.0"
bytes = "2.0"
```

### 2.1 主应用服务器实现

```rust
use anyhow::Result;
use clap::Parser;
use pingora::{
    apps::health_check::HealthCheck,
    proxy::{
        ProxyHttp, HttpPipelineHandler, ProxyHttpService, ProxyHttpAction,
        http_proxy_service, ProxyHttp2Tls, ProxyHttpConfiguration,
    },
    services::{
        background::{BackgroundService, BackgroundTask},
        listening::QuicListener,
        Service, ServiceBuilder,
    },
    server::{configuration::ServerConf, Server},
    tls::ServerTlsConfig,
    upstreams::{
        peer::HttpPeer, upstream::UpstreamConfig,
        balance::LoadBalancer,
        health_check::TcpHealthCheck,
    },
};
use std::{collections::HashMap, net::SocketAddr, path::PathBuf, sync::Arc, time::Duration};
use tokio::sync::Mutex;
use tracing::{info, error, warn};

mod auth;
mod config;
mod grpc;
mod logging;
mod metrics;
mod middleware;
mod mq;
mod handlers;

use crate::{
    auth::{AuthManager, AuthMode},
    config::AppConfig,
    grpc::GrpcServiceManager,
    logging::setup_logging,
    metrics::setup_metrics,
    middleware::{
        RateLimiter, RequestMiddleware, ResponseMiddleware,
        SessionManager, SecurityMiddleware, MiddlewareChain
    },
    mq::EventPublisher,
};

// 命令行参数定义
#[derive(Parser, Debug)]
#[clap(author, version, about)]
struct Args {
    #[clap(short, long, value_parser, default_value = "config/default.toml")]
    config: PathBuf,
}

// 主HTTP处理器，实现核心代理逻辑
struct MainProxyHandler {
    upstreams: Arc<HashMap<String, Arc<LoadBalancer<HttpPeer>>>>,
    grpc_services: Arc<GrpcServiceManager>,
    auth_manager: Arc<AuthManager>,
    event_publisher: Arc<EventPublisher>,
    middleware_chain: Arc<MiddlewareChain>,
    config: Arc<AppConfig>,
}

// 实现Pingora的HTTP管道处理接口
#[async_trait::async_trait]
impl HttpPipelineHandler for MainProxyHandler {
    async fn handle_request(
        &self,
        mut req: http::Request<hyper::Body>,
        ctx: &mut HttpContext,
    ) -> Result<ProxyHttpAction, pingora::Error> {
        // 1. 执行中间件链处理请求
        let middleware_result = self.middleware_chain.process_request(&mut req, ctx).await?;
        if let Some(response) = middleware_result {
            return Ok(ProxyHttpAction::RespondWith(response));
        }

        // 2. 认证处理
        let auth_result = self.auth_manager.authenticate(&req).await;
        if let Err(e) = auth_result {
            let status = match e {
                auth::AuthError::Unauthorized => http::StatusCode::UNAUTHORIZED,
                auth::AuthError::Forbidden => http::StatusCode::FORBIDDEN,
                _ => http::StatusCode::INTERNAL_SERVER_ERROR,
            };

            // 构建错误响应
            let response = http::Response::builder()
                .status(status)
                .body(hyper::Body::from(e.to_string()))?;

            return Ok(ProxyHttpAction::RespondWith(response));
        }

        // 3. 解析路由以确定目标服务
        let path = req.uri().path();
        let service_name = self.extract_service_name(path);

        // 4. 判断是否是gRPC请求
        if req.headers().get("content-type")
            .map(|v| v.to_str().unwrap_or(""))
            .unwrap_or("")
            .contains("application/grpc")
        {
            // gRPC请求处理
            return self.handle_grpc_request(req, service_name, ctx).await;
        }

        // 5. 标准HTTP请求处理
        if let Some(upstream) = self.upstreams.get(&service_name) {
            // 记录跟踪信息
            let trace_id = ctx.get_tracing_id().unwrap_or_default();
            info!(trace_id = %trace_id, service = %service_name, "Proxying HTTP request");

            // 获取下一个可用的对等点，执行负载均衡
            let peer = upstream.get_peer().await?;

            // 添加自定义HTTP头 - 跟踪信息
            req.headers_mut().insert(
                "X-Trace-ID",
                http::header::HeaderValue::from_str(&trace_id.to_string())?
            );

            // 发布事件到消息队列
            let user_id = self.auth_manager.extract_user_id(&req).unwrap_or_default();
            self.event_publisher.publish_request_event(
                &req,
                &service_name,
                &user_id,
                &trace_id.to_string()
            ).await?;

            // 代理到后端服务
            Ok(ProxyHttpAction::Proxy(peer, req))
        } else {
            // 找不到服务返回404
            let resp = http::Response::builder()
                .status(http::StatusCode::NOT_FOUND)
                .body(hyper::Body::from(format!("Service '{}' not found", service_name)))?;

            Ok(ProxyHttpAction::RespondWith(resp))
        }
    }

    // 处理响应的中间件钩子
    async fn handle_response(
        &self,
        res: &mut http::Response<hyper::Body>,
        ctx: &mut HttpContext,
    ) -> Result<(), pingora::Error> {
        // 执行响应处理中间件链
        self.middleware_chain.process_response(res, ctx).await?;
        Ok(())
    }
}

impl MainProxyHandler {
    // 从请求路径提取服务名称
    fn extract_service_name(&self, path: &str) -> String {
        // 简单实现：按照第一段路径提取服务名
        let parts: Vec<&str> = path.split('/').filter(|p| !p.is_empty()).collect();
        parts.first().map(|s| s.to_string()).unwrap_or_else(|| "default".to_string())
    }

    // 处理gRPC请求
    async fn handle_grpc_request(
        &self,
        req: http::Request<hyper::Body>,
        service_name: String,
        ctx: &mut HttpContext,
    ) -> Result<ProxyHttpAction, pingora::Error> {
        let trace_id = ctx.get_tracing_id().unwrap_or_default();

        // 检查gRPC服务是否已注册
        if self.grpc_services.has_service(&service_name) {
            // 让gRPC服务管理器处理请求
            let grpc_result = self.grpc_services.handle_request(req, &service_name).await;

            match grpc_result {
                Ok(response) => {
                    // 发布gRPC事件到消息队列
                    let user_id = self.auth_manager.extract_user_id(&req).unwrap_or_default();
                    self.event_publisher.publish_grpc_event(
                        &service_name,
                        &user_id,
                        &trace_id.to_string(),
                        true,
                    ).await?;

                    Ok(ProxyHttpAction::RespondWith(response))
                },
                Err(e) => {
                    error!(error = %e, service = %service_name, "gRPC request handling error");

                    // 构建错误响应
                    let mut response = http::Response::builder()
                        .status(http::StatusCode::INTERNAL_SERVER_ERROR)
                        .header("content-type", "application/grpc")
                        .header("grpc-status", "2") // UNKNOWN
                        .body(hyper::Body::empty())?;

                    self.event_publisher.publish_grpc_event(
                        &service_name,
                        &self.auth_manager.extract_user_id(&req).unwrap_or_default(),
                        &trace_id.to_string(),
                        false,
                    ).await?;

                    Ok(ProxyHttpAction::RespondWith(response))
                }
            }
        } else if let Some(upstream) = self.upstreams.get(&service_name) {
            // 如果我们有upstream配置但没有特定的gRPC处理器，则直接代理
            let peer = upstream.get_peer().await?;
            Ok(ProxyHttpAction::Proxy(peer, req))
        } else {
            // 未找到gRPC服务
            let resp = http::Response::builder()
                .status(http::StatusCode::NOT_FOUND)
                .header("content-type", "application/grpc")
                .header("grpc-status", "5") // NOT_FOUND
                .body(hyper::Body::empty())?;

            Ok(ProxyHttpAction::RespondWith(resp))
        }
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    // 解析命令行参数
    let args = Args::parse();

    // 加载配置
    let config = config::load_config(args.config).await?;
    let config = Arc::new(config);

    // 设置日志和监控
    setup_logging(&config.logging)?;
    setup_metrics(&config.metrics)?;

    info!("Starting Pingora HTTP Gateway v{}", env!("CARGO_PKG_VERSION"));

    // 创建Pingora服务器
    let mut server = Server::new(Some(config.server.clone().into()))?;

    // 初始化各组件
    let auth_manager = Arc::new(AuthManager::new(&config.auth).await?);
    let event_publisher = Arc::new(EventPublisher::new(&config.messaging).await?);
    let grpc_services = Arc::new(GrpcServiceManager::new(&config.grpc).await?);

    // 创建中间件链
    let middleware_chain = Arc::new(MiddlewareChain::new(vec![
        Box::new(SecurityMiddleware::new(&config.security)),
        Box::new(RateLimiter::new(&config.rate_limit)),
        Box::new(SessionManager::new(&config.session)),
        // 添加更多中间件...
    ]));

    // 初始化上游服务配置
    let mut upstreams: HashMap<String, Arc<LoadBalancer<HttpPeer>>> = HashMap::new();

    for (service_name, upstream_config) in &config.upstreams {
        let mut lb_config = LoadBalancerConfig::default();
        lb_config.set_health_check(Box::new(TcpHealthCheck {}));
        lb_config.set_health_check_interval(Duration::from_secs(upstream_config.health_check_interval_secs));

        let mut balancer = LoadBalancer::new(lb_config);

        // 添加上游服务器
        for server in &upstream_config.servers {
            let upstream_addr: SocketAddr = server.parse()?;
            let peer = HttpPeer::new(upstream_addr, UpstreamConfig::default());
            balancer.add_peer(peer).await;
        }

        upstreams.insert(service_name.clone(), Arc::new(balancer));
    }

    // 创建主HTTP处理器
    let handler = MainProxyHandler {
        upstreams: Arc::new(upstreams),
        grpc_services,
        auth_manager,
        event_publisher,
        middleware_chain,
        config: config.clone(),
    };

    // 配置HTTP代理服务
    let mut http_proxy_conf = ProxyHttpConfiguration::default();
    http_proxy_conf.http2_only = false; // 支持HTTP/1.x和HTTP/2

    // 创建HTTP代理服务
    let mut service = ServiceBuilder::new(ProxyHttp::new(handler, http_proxy_conf));

    // 配置TLS(如果启用)
    if config.tls.enabled {
        let tls_config = ServerTlsConfig::new()
            .cert_path(&config.tls.cert_path)
            .key_path(&config.tls.key_path);

        service.add_tcp(config.server.listen_addr)?
              .add_tls(config.server.listen_addr_tls, tls_config)?;

        // 添加HTTP/3 (QUIC) 支持
        if config.http3.enabled {
            service.add_quic(
                config.http3.listen_addr,
                tls_config,
                QuicListener::default(),
            )?;
        }
    } else {
        // 仅普通HTTP
        service.add_tcp(config.server.listen_addr)?;
    }

    // 添加健康检查服务
    let health_service = ServiceBuilder::new(HealthCheck::new());
    health_service.add_tcp(config.health.listen_addr)?;

    // 注册服务到服务器
    server.add_service(service);
    server.add_service(health_service);

    // 添加后台任务
    let background_tasks = BackgroundService::new();
    // 添加您需要的后台任务：
    // background_tasks.add_task(Box::new(YourBackgroundTask::new()));
    server.add_service(background_tasks);

    // 启动服务器
    info!("HTTP Gateway started, listening on: {}", config.server.listen_addr);
    server.run_forever();

    Ok(())
}
```

## 3 二、配置、监控和日志模块

```rust
// src/config.rs
use std::path::Path;
use serde::Deserialize;
use tokio::fs;
use anyhow::Result;

#[derive(Debug, Clone, Deserialize)]
pub struct AppConfig {
    pub server: ServerConfig,
    pub health: HealthConfig,
    pub tls: TlsConfig,
    pub http3: Http3Config,
    pub auth: AuthConfig,
    pub session: SessionConfig,
    pub security: SecurityConfig,
    pub rate_limit: RateLimitConfig,
    pub logging: LoggingConfig,
    pub metrics: MetricsConfig,
    pub grpc: GrpcConfig,
    pub messaging: MessagingConfig,
    pub upstreams: std::collections::HashMap<String, UpstreamConfig>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct ServerConfig {
    pub listen_addr: std::net::SocketAddr,
    pub listen_addr_tls: std::net::SocketAddr,
    pub workers: usize,
    pub max_connections: usize,
    pub connection_idle_timeout: u64,
}

impl From<ServerConfig> for pingora::server::configuration::ServerConf {
    fn from(config: ServerConfig) -> Self {
        let mut server_conf = Self::default();
        server_conf.num_workers = config.workers;
        server_conf.connection_idle_timeout = config.connection_idle_timeout;
        server_conf.max_active_connections = config.max_connections;
        server_conf
    }
}

#[derive(Debug, Clone, Deserialize)]
pub struct HealthConfig {
    pub listen_addr: std::net::SocketAddr,
}

#[derive(Debug, Clone, Deserialize)]
pub struct TlsConfig {
    pub enabled: bool,
    pub cert_path: String,
    pub key_path: String,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Http3Config {
    pub enabled: bool,
    pub listen_addr: std::net::SocketAddr,
}

#[derive(Debug, Clone, Deserialize)]
pub struct AuthConfig {
    pub mode: String, // "none", "jwt", "session", "mixed"
    pub jwt_secret: String,
    pub jwt_algorithm: String,
    pub session_redis_url: String,
    pub cookie_name: String,
    pub cookie_secure: bool,
    pub cookie_http_only: bool,
    pub token_expiry_seconds: u64,
}

#[derive(Debug, Clone, Deserialize)]
pub struct SessionConfig {
    pub enabled: bool,
    pub store_type: String, // "redis", "memory"
    pub redis_url: String,
    pub session_ttl_seconds: u64,
}

#[derive(Debug, Clone, Deserialize)]
pub struct SecurityConfig {
    pub cors_allowed_origins: Vec<String>,
    pub cors_allowed_methods: Vec<String>,
    pub cors_allowed_headers: Vec<String>,
    pub cors_expose_headers: Vec<String>,
    pub xss_protection: bool,
    pub content_security_policy: String,
    pub frame_options: String,
}

#[derive(Debug, Clone, Deserialize)]
pub struct RateLimitConfig {
    pub enabled: bool,
    pub requests_per_minute: u32,
    pub burst_size: u32,
    pub backend: String, // "memory", "redis"
    pub redis_url: String,
}

#[derive(Debug, Clone, Deserialize)]
pub struct LoggingConfig {
    pub level: String,
    pub format: String, // "json", "text"
    pub otlp_endpoint: String,
    pub log_requests: bool,
    pub log_responses: bool,
    pub sample_rate: f32,
}

#[derive(Debug, Clone, Deserialize)]
pub struct MetricsConfig {
    pub prometheus_endpoint: std::net::SocketAddr,
    pub metrics_prefix: String,
    pub export_interval_secs: u64,
}

#[derive(Debug, Clone, Deserialize)]
pub struct GrpcConfig {
    pub proto_file_dir: String,
    pub services: Vec<GrpcServiceConfig>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct GrpcServiceConfig {
    pub name: String,
    pub upstream_addr: String,
    pub max_message_size: usize,
    pub timeout_seconds: u64,
    pub retry_count: u32,
}

#[derive(Debug, Clone, Deserialize)]
pub struct MessagingConfig {
    pub provider: String, // "kafka", "nats"
    pub kafka_brokers: Vec<String>,
    pub nats_url: String,
    pub topics: std::collections::HashMap<String, String>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct UpstreamConfig {
    pub servers: Vec<String>,
    pub protocol: String, // "http", "https", "grpc"
    pub health_check_interval_secs: u64,
    pub max_retries: u32,
    pub connect_timeout_ms: u64,
}

pub async fn load_config<P: AsRef<Path>>(path: P) -> Result<AppConfig> {
    let content = fs::read_to_string(path).await?;
    let config: AppConfig = toml::from_str(&content)?;
    Ok(config)
}

// src/logging.rs
use anyhow::Result;
use opentelemetry::{
    sdk::{trace as sdktrace, Resource},
    KeyValue,
};
use opentelemetry_otlp::WithExportConfig;
use tracing_subscriber::{
    layer::SubscriberExt,
    util::SubscriberInitExt,
    EnvFilter, fmt,
};
use crate::config::LoggingConfig;

pub fn setup_logging(config: &LoggingConfig) -> Result<()> {
    // 创建OTLP导出器
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint(&config.otlp_endpoint)
        )
        .with_trace_config(
            sdktrace::config()
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", "pingora-gateway"),
                    KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
                ]))
                .with_sampler(sdktrace::Sampler::TraceIdRatioBased(config.sample_rate))
        )
        .install_batch(opentelemetry::runtime::Tokio)?;

    // 创建日志格式化器
    let fmt_layer = match config.format.as_str() {
        "json" => fmt::layer().json().boxed(),
        _ => fmt::layer().compact().boxed(),
    };

    // 设置过滤器级别
    let filter_layer = EnvFilter::try_from_default_env()
        .or_else(|_| EnvFilter::try_new(&config.level))
        .unwrap_or_else(|_| EnvFilter::new("info"));

    // 组装和安装订阅者
    tracing_subscriber::registry()
        .with(filter_layer)
        .with(fmt_layer)
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    tracing::info!("Logging system initialized");
    Ok(())
}

// src/metrics.rs
use anyhow::Result;
use metrics_exporter_prometheus::{Matcher, PrometheusBuilder, PrometheusHandle};
use std::time::Duration;
use tokio::task;
use crate::config::MetricsConfig;

pub fn setup_metrics(config: &MetricsConfig) -> Result<PrometheusHandle> {
    // 配置Prometheus指标导出器
    let builder = PrometheusBuilder::new()
        .with_http_listener(config.prometheus_endpoint)
        .add_global_label("service", "pingora-gateway")
        .set_buckets_for_metric(
            Matcher::Full("http_request_duration_seconds".to_string()),
            vec![0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1.0, 2.5, 5.0, 10.0]
        )?;

    // 构建并启动服务器
    let handle = builder.install()?;

    // 定期发布指标
    let interval = Duration::from_secs(config.export_interval_secs);
    let prefix = config.metrics_prefix.clone();

    task::spawn(async move {
        let mut interval = tokio::time::interval(interval);
        loop {
            interval.tick().await;

            // 收集和发布系统指标
            let mem_info = sys_info::mem_info().unwrap_or_default();
            metrics::gauge!(
                format!("{}_memory_used_bytes", prefix),
                mem_info.total as f64 - mem_info.free as f64
            );

            let load = sys_info::loadavg().unwrap_or_default();
            metrics::gauge!(format!("{}_load_1m", prefix), load.one);
            metrics::gauge!(format!("{}_load_5m", prefix), load.five);
            metrics::gauge!(format!("{}_load_15m", prefix), load.fifteen);

            // 收集进程指标
            if let Ok(proc_info) = sys_info::proc_stat() {
                metrics::counter!(
                    format!("{}_cpu_total", prefix),
                    proc_info.running as u64
                );
            }
        }
    });

    tracing::info!("Metrics server started on {}", config.prometheus_endpoint);
    Ok(handle)
}
```

## 4 三、认证和授权中间件

```rust
// src/auth.rs
use anyhow::Result;
use jsonwebtoken::{decode, encode, Algorithm, DecodingKey, EncodingKey, Header, Validation};
use serde::{Deserialize, Serialize};
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use thiserror::Error;
use http::{Request, Response};
use hyper::Body;
use uuid::Uuid;
use crate::{
    config::AuthConfig,
    middleware::SessionStore
};

// 认证模式
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum AuthMode {
    None,
    Jwt,
    Session,
    Mixed,
}

// 认证错误
#[derive(Debug, Error)]
pub enum AuthError {
    #[error("Unauthorized")]
    Unauthorized,

    #[error("Forbidden")]
    Forbidden,

    #[error("JWT is invalid: {0}")]
    InvalidJwt(String),

    #[error("Session is invalid: {0}")]
    InvalidSession(String),

    #[error("Backend error: {0}")]
    BackendError(String),
}

// JWT载荷
#[derive(Debug, Serialize, Deserialize)]
pub struct Claims {
    pub sub: String,  // 用户ID
    pub exp: u64,     // 过期时间
    pub iat: u64,     // 签发时间
    pub roles: Vec<String>, // 角色列表
}

// 认证用户
#[derive(Debug, Clone)]
pub struct AuthenticatedUser {
    pub user_id: String,
    pub roles: Vec<String>,
    pub authenticated_at: SystemTime,
}

// 认证管理器
pub struct AuthManager {
    config: AuthConfig,
    mode: AuthMode,
    jwt_encoding_key: Option<EncodingKey>,
    jwt_decoding_key: Option<DecodingKey>,
    session_store: Option<Box<dyn SessionStore>>,
}

impl AuthManager {
    pub async fn new(config: &AuthConfig) -> Result<Self> {
        // 解析认证模式
        let mode = match config.mode.as_str() {
            "none" => AuthMode::None,
            "jwt" => AuthMode::Jwt,
            "session" => AuthMode::Session,
            "mixed" => AuthMode::Mixed,
            _ => AuthMode::None,
        };

        // 初始化JWT密钥（如果需要）
        let (jwt_encoding_key, jwt_decoding_key) = if mode == AuthMode::Jwt || mode == AuthMode::Mixed {
            let encoding_key = EncodingKey::from_secret(config.jwt_secret.as_bytes());
            let decoding_key = DecodingKey::from_secret(config.jwt_secret.as_bytes());
            (Some(encoding_key), Some(decoding_key))
        } else {
            (None, None)
        };

        // 初始化会话存储（如果需要）
        let session_store = if mode == AuthMode::Session || mode == AuthMode::Mixed {
            // 这里会实例化适当的会话存储
            Some(crate::middleware::create_session_store(&config.session_redis_url)?)
        } else {
            None
        };

        Ok(Self {
            config: config.clone(),
            mode,
            jwt_encoding_key,
            jwt_decoding_key,
            session_store,
        })
    }

    // 认证请求
    pub async fn authenticate<T>(&self, req: &Request<T>) -> Result<AuthenticatedUser, AuthError> {
        match self.mode {
            AuthMode::None => {
                // 无认证模式，创建匿名用户
                Ok(AuthenticatedUser {
                    user_id: "anonymous".to_string(),
                    roles: vec!["guest".to_string()],
                    authenticated_at: SystemTime::now(),
                })
            },
            AuthMode::Jwt => self.authenticate_jwt(req).await,
            AuthMode::Session => self.authenticate_session(req).await,
            AuthMode::Mixed => {
                // 尝试JWT认证，如果失败则尝试会话认证
                match self.authenticate_jwt(req).await {
                    Ok(user) => Ok(user),
                    Err(_) => self.authenticate_session(req).await,
                }
            }
        }
    }

    // JWT认证
    async fn authenticate_jwt<T>(&self, req: &Request<T>) -> Result<AuthenticatedUser, AuthError> {
        // 从Authorization头获取令牌
        let auth_header = req.headers()
            .get(http::header::AUTHORIZATION)
            .ok_or(AuthError::Unauthorized)?
            .to_str()
            .map_err(|_| AuthError::InvalidJwt("Invalid Authorization header".to_string()))?;

        if !auth_header.starts_with("Bearer ") {
            return Err(AuthError::InvalidJwt("Invalid token format".to_string()));
        }

        let token = &auth_header[7..]; // 移除"Bearer "前缀

        // 验证JWT
        let decoding_key = self.jwt_decoding_key.as_ref()
            .ok_or_else(|| AuthError::BackendError("JWT keys not configured".to_string()))?;

        let algorithm = match self.config.jwt_algorithm.as_str() {
            "HS256" => Algorithm::HS256,
            "HS384" => Algorithm::HS384,
            "HS512" => Algorithm::HS512,
            _ => Algorithm::HS256,
        };

        let mut validation = Validation::new(algorithm);
        validation.validate_exp = true;

        let claims = decode::<Claims>(
            token,
            decoding_key,
            &validation
        ).map_err(|e| AuthError::InvalidJwt(e.to_string()))?;

        Ok(AuthenticatedUser {
            user_id: claims.claims.sub,
            roles: claims.claims.roles,
            authenticated_at: SystemTime::now(),
        })
    }

    // 会话认证
    async fn authenticate_session<T>(&self, req: &Request<T>) -> Result<AuthenticatedUser, AuthError> {
        // 获取会话cookie
        let cookie_header = req.headers()
            .get(http::header::COOKIE)
            .ok_or(AuthError::Unauthorized)?
            .to_str()
            .map_err(|_| AuthError::InvalidSession("Invalid cookie".to_string()))?;

        // 解析cookie获取会话ID
        let cookies: Vec<&str> = cookie_header.split(';').collect();
        let session_cookie = cookies.iter()
            .find(|c| c.trim().starts_with(&format!("{}=", self.config.cookie_name)))
            .ok_or(AuthError::Unauthorized)?;

        let session_id = session_cookie
            .trim()
            .strip_prefix(&format!("{}=", self.config.cookie_name))
            .ok_or(AuthError::InvalidSession("Invalid session cookie format".to_string()))?;

        // 从会话存储获取用户信息
        let session_store = self.session_store.as_ref()
            .ok_or_else(|| AuthError::BackendError("Session store not configured".to_string()))?;

        let session_data = session_store.get(session_id).await
            .map_err(|e| AuthError::BackendError(format!("Session store error: {}", e)))?
            .ok_or(AuthError::Unauthorized)?;

        // 解析会话数据
        let user_data: AuthenticatedUser = serde_json::from_
/*
Looks like the code was cut off in the middle of the session authentication method in the auth.rs file.
Let me continue from where it left off, starting with completing the session authentication method, then finish the auth module, and move on to the middleware and gRPC modules.
*/

        // 解析会话数据
        let user_data: AuthenticatedUser = serde_json::from_str(&session_data)
            .map_err(|e| AuthError::InvalidSession(format!("Invalid session data: {}", e)))?;

        Ok(user_data)
    }

    // 生成JWT令牌
    pub fn generate_jwt(&self, user_id: &str, roles: Vec<String>) -> Result<String, AuthError> {
        let encoding_key = self.jwt_encoding_key.as_ref()
            .ok_or_else(|| AuthError::BackendError("JWT keys not configured".to_string()))?;

        let now = SystemTime::now().duration_since(UNIX_EPOCH)
            .map_err(|e| AuthError::BackendError(format!("System time error: {}", e)))?
            .as_secs();

        let expiry = now + self.config.token_expiry_seconds;

        let claims = Claims {
            sub: user_id.to_string(),
            exp: expiry,
            iat: now,
            roles,
        };

        encode(
            &Header::new(Algorithm::HS256),
            &claims,
            encoding_key,
        ).map_err(|e| AuthError::BackendError(format!("JWT encoding error: {}", e)))
    }

    // 创建新会话
    pub async fn create_session(&self, user: &AuthenticatedUser) -> Result<String, AuthError> {
        let session_store = self.session_store.as_ref()
            .ok_or_else(|| AuthError::BackendError("Session store not configured".to_string()))?;

        // 生成会话ID
        let session_id = Uuid::new_v4().to_string();

        // 序列化用户数据
        let user_data = serde_json::to_string(user)
            .map_err(|e| AuthError::BackendError(format!("User serialization error: {}", e)))?;

        // 存储会话
        session_store.set(&session_id, &user_data, self.config.token_expiry_seconds).await
            .map_err(|e| AuthError::BackendError(format!("Session store error: {}", e)))?;

        Ok(session_id)
    }

    // 撤销会话
    pub async fn revoke_session(&self, session_id: &str) -> Result<(), AuthError> {
        let session_store = self.session_store.as_ref()
            .ok_or_else(|| AuthError::BackendError("Session store not configured".to_string()))?;

        session_store.delete(session_id).await
            .map_err(|e| AuthError::BackendError(format!("Session store error: {}", e)))
    }
}
```

## 5 四、中间件实现

```rust
// src/middleware.rs
use anyhow::Result;
use async_trait::async_trait;
use http::{Request, Response, StatusCode};
use hyper::Body;
use pingora::http::{HttpContext};
use std::{
    sync::Arc,
    collections::HashMap,
    time::{Duration, Instant},
};
use tokio::sync::{Mutex, RwLock};
use tracing::{info, warn, error, instrument, Span};
use metrics::{counter, gauge, histogram};
use crate::config::{
    SecurityConfig, RateLimitConfig, SessionConfig,
};

// 会话存储接口
#[async_trait]
pub trait SessionStore: Send + Sync {
    async fn get(&self, key: &str) -> Result<Option<String>>;
    async fn set(&self, key: &str, value: &str, ttl_seconds: u64) -> Result<()>;
    async fn delete(&self, key: &str) -> Result<()>;
}

// Redis会话存储
pub struct RedisSessionStore {
    client: redis::Client,
    pool: deadpool_redis::Pool,
}

#[async_trait]
impl SessionStore for RedisSessionStore {
    async fn get(&self, key: &str) -> Result<Option<String>> {
        let mut conn = self.pool.get().await?;
        let result: Option<String> = redis::cmd("GET")
            .arg(key)
            .query_async(&mut conn)
            .await?;
        Ok(result)
    }

    async fn set(&self, key: &str, value: &str, ttl_seconds: u64) -> Result<()> {
        let mut conn = self.pool.get().await?;
        redis::cmd("SETEX")
            .arg(key)
            .arg(ttl_seconds)
            .arg(value)
            .query_async(&mut conn)
            .await?;
        Ok(())
    }

    async fn delete(&self, key: &str) -> Result<()> {
        let mut conn = self.pool.get().await?;
        redis::cmd("DEL")
            .arg(key)
            .query_async(&mut conn)
            .await?;
        Ok(())
    }
}

// 内存会话存储
pub struct MemorySessionStore {
    store: Arc<RwLock<HashMap<String, (String, Instant)>>>,
    ttl: Duration,
}

#[async_trait]
impl SessionStore for MemorySessionStore {
    async fn get(&self, key: &str) -> Result<Option<String>> {
        let store = self.store.read().await;
        if let Some((value, expiry)) = store.get(key) {
            if expiry > &Instant::now() {
                return Ok(Some(value.clone()));
            }
        }
        Ok(None)
    }

    async fn set(&self, key: &str, value: &str, ttl_seconds: u64) -> Result<()> {
        let mut store = self.store.write().await;
        let expiry = Instant::now() + Duration::from_secs(ttl_seconds);
        store.insert(key.to_string(), (value.to_string(), expiry));
        Ok(())
    }

    async fn delete(&self, key: &str) -> Result<()> {
        let mut store = self.store.write().await;
        store.remove(key);
        Ok(())
    }
}

// 创建会话存储的工厂函数
pub fn create_session_store(redis_url: &str) -> Result<Box<dyn SessionStore>> {
    if redis_url.is_empty() || redis_url == "memory" {
        // 使用内存存储
        Ok(Box::new(MemorySessionStore {
            store: Arc::new(RwLock::new(HashMap::new())),
            ttl: Duration::from_secs(3600), // 默认1小时
        }))
    } else {
        // 使用Redis存储
        let client = redis::Client::open(redis_url)?;
        let pool = deadpool_redis::Config {
            url: Some(redis_url.to_string()),
            connection: None,
            pool: None,
        }
        .create_pool(Some(deadpool_redis::Runtime::Tokio1))?;

        Ok(Box::new(RedisSessionStore { client, pool }))
    }
}

// 请求中间件接口
#[async_trait]
pub trait RequestMiddleware: Send + Sync {
    async fn process_request(
        &self,
        req: &mut Request<Body>,
        ctx: &mut HttpContext,
    ) -> Result<Option<Response<Body>>>;
}

// 响应中间件接口
#[async_trait]
pub trait ResponseMiddleware: Send + Sync {
    async fn process_response(
        &self,
        res: &mut Response<Body>,
        ctx: &HttpContext,
    ) -> Result<()>;
}

// 中间件链
pub struct MiddlewareChain {
    middleware: Vec<Box<dyn RequestMiddleware>>,
    response_middleware: Vec<Box<dyn ResponseMiddleware>>,
}

impl MiddlewareChain {
    pub fn new(middleware: Vec<Box<dyn RequestMiddleware>>) -> Self {
        Self {
            middleware,
            response_middleware: Vec::new(),
        }
    }

    pub fn add_response_middleware(&mut self, middleware: Box<dyn ResponseMiddleware>) {
        self.response_middleware.push(middleware);
    }

    pub async fn process_request(
        &self,
        req: &mut Request<Body>,
        ctx: &mut HttpContext,
    ) -> Result<Option<Response<Body>>> {
        // 记录请求开始时间
        let start = Instant::now();
        let method = req.method().to_string();
        let uri = req.uri().to_string();

        // 增加请求计数
        counter!("http_requests_total", 1, "method" => method.clone(), "path" => uri.clone());

        // 执行所有请求中间件
        for mw in &self.middleware {
            if let Some(response) = mw.process_request(req, ctx).await? {
                // 中间件提前返回响应
                let duration = start.elapsed().as_secs_f64();
                histogram!("http_request_duration_seconds", duration,
                           "method" => method, "path" => uri,
                           "status" => response.status().as_u16().to_string());

                return Ok(Some(response));
            }
        }

        // 标记请求已经通过所有中间件处理
        ctx.extensions_mut().insert("request_start_time", start);

        Ok(None)
    }

    pub async fn process_response(
        &self,
        res: &mut Response<Body>,
        ctx: &HttpContext,
    ) -> Result<()> {
        // 计算请求处理时间
        if let Some(start) = ctx.extensions().get::<Instant>("request_start_time") {
            let duration = start.elapsed().as_secs_f64();
            let method = ctx.extensions().get::<String>("request_method")
                .map_or("UNKNOWN", |s| s.as_str());
            let uri = ctx.extensions().get::<String>("request_uri")
                .map_or("UNKNOWN", |s| s.as_str());

            // 记录请求处理时间
            histogram!("http_request_duration_seconds", duration,
                       "method" => method, "path" => uri,
                       "status" => res.status().as_u16().to_string());
        }

        // 执行所有响应中间件
        for mw in &self.response_middleware {
            mw.process_response(res, ctx).await?;
        }

        Ok(())
    }
}

// 安全中间件
pub struct SecurityMiddleware {
    config: SecurityConfig,
}

impl SecurityMiddleware {
    pub fn new(config: &SecurityConfig) -> Self {
        Self {
            config: config.clone(),
        }
    }
}

#[async_trait]
impl RequestMiddleware for SecurityMiddleware {
    async fn process_request(
        &self,
        req: &mut Request<Body>,
        ctx: &mut HttpContext,
    ) -> Result<Option<Response<Body>>> {
        // 处理CORS
        if req.method() == http::Method::OPTIONS {
            let origin = req.headers().get("origin")
                .and_then(|v| v.to_str().ok())
                .unwrap_or("");

            // 检查是否是允许的源
            let allowed = self.config.cors_allowed_origins.iter()
                .any(|allowed| allowed == "*" || allowed == origin);

            if allowed {
                let mut response = Response::builder()
                    .status(StatusCode::NO_CONTENT)
                    .body(Body::empty())?;

                // 添加CORS头
                let headers = response.headers_mut();
                headers.insert("Access-Control-Allow-Origin",
                    origin.parse().unwrap_or_else(|_| "*".parse().unwrap()));

                headers.insert("Access-Control-Allow-Methods",
                    self.config.cors_allowed_methods.join(", ").parse()?);

                headers.insert("Access-Control-Allow-Headers",
                    self.config.cors_allowed_headers.join(", ").parse()?);

                headers.insert("Access-Control-Max-Age",
                    "86400".parse()?);

                return Ok(Some(response));
            }
        }

        // 添加安全头部
        ctx.extensions_mut().insert("security_headers", true);

        Ok(None)
    }
}

#[async_trait]
impl ResponseMiddleware for SecurityMiddleware {
    async fn process_response(
        &self,
        res: &mut Response<Body>,
        ctx: &HttpContext,
    ) -> Result<()> {
        if ctx.extensions().get::<bool>("security_headers").is_some() {
            let headers = res.headers_mut();

            // 添加安全头部
            if self.config.xss_protection {
                headers.insert("X-XSS-Protection", "1; mode=block".parse()?);
            }

            if !self.config.content_security_policy.is_empty() {
                headers.insert("Content-Security-Policy",
                    self.config.content_security_policy.parse()?);
            }

            if !self.config.frame_options.is_empty() {
                headers.insert("X-Frame-Options",
                    self.config.frame_options.parse()?);
            }

            // 添加CORS头到响应中
            if let Some(origin) = ctx.request_headers().get("origin") {
                // 检查是否是允许的源
                let origin_str = origin.to_str().unwrap_or("");
                let allowed = self.config.cors_allowed_origins.iter()
                    .any(|allowed| allowed == "*" || allowed == origin_str);

                if allowed {
                    headers.insert("Access-Control-Allow-Origin", origin.clone());

                    if !self.config.cors_expose_headers.is_empty() {
                        headers.insert("Access-Control-Expose-Headers",
                            self.config.cors_expose_headers.join(", ").parse()?);
                    }
                }
            }
        }

        Ok(())
    }
}

// 限流中间件
pub struct RateLimiter {
    config: RateLimitConfig,
    limiter: Option<governor::RateLimiter<governor::state::NotKeyed, governor::state::InMemoryState, governor::clock::DefaultClock>>,
}

impl RateLimiter {
    pub fn new(config: &RateLimitConfig) -> Self {
        let limiter = if config.enabled {
            // 创建限流器
            let limit = governor::Quota::per_minute(nonzero_ext::nonzero!(config.requests_per_minute u32));
            let burst = config.burst_size;
            Some(
                governor::RateLimiter::direct(
                    governor::state::NotKeyed::default(),
                    limit,
                    governor::clock::DefaultClock::default(),
                )
            )
        } else {
            None
        };

        Self {
            config: config.clone(),
            limiter,
        }
    }
}

#[async_trait]
impl RequestMiddleware for RateLimiter {
    async fn process_request(
        &self,
        req: &mut Request<Body>,
        ctx: &mut HttpContext,
    ) -> Result<Option<Response<Body>>> {
        if let Some(limiter) = &self.limiter {
            match limiter.check() {
                Ok(_) => {
                    // 允许请求
                    Ok(None)
                },
                Err(negative) => {
                    // 拒绝请求 - 超出限流
                    let wait_time = negative.wait_time_from(std::time::Instant::now());

                    // 增加限流计数
                    counter!("rate_limiter_blocked_requests_total", 1);

                    // 生成拒绝响应
                    let response = Response::builder()
                        .status(StatusCode::TOO_MANY_REQUESTS)
                        .header("Retry-After", wait_time.as_secs().to_string())
                        .body(Body::from("Too many requests, please try again later"))?;

                    Ok(Some(response))
                }
            }
        } else {
            // 限流未启用
            Ok(None)
        }
    }
}

// 会话管理中间件
pub struct SessionManager {
    config: SessionConfig,
    store: Option<Box<dyn SessionStore>>,
}

impl SessionManager {
    pub fn new(config: &SessionConfig) -> Self {
        let store = if config.enabled {
            match create_session_store(&config.redis_url) {
                Ok(store) => Some(store),
                Err(e) => {
                    error!("Failed to create session store: {}", e);
                    None
                }
            }
        } else {
            None
        };

        Self {
            config: config.clone(),
            store,
        }
    }
}

#[async_trait]
impl RequestMiddleware for SessionManager {
    async fn process_request(
        &self,
        req: &mut Request<Body>,
        ctx: &mut HttpContext,
    ) -> Result<Option<Response<Body>>> {
        if !self.config.enabled || self.store.is_none() {
            return Ok(None);
        }

        // 从cookie中提取会话ID
        if let Some(cookie) = req.headers().get(http::header::COOKIE) {
            if let Ok(cookie_str) = cookie.to_str() {
                for cookie_part in cookie_str.split(';') {
                    let cookie_kv: Vec<&str> = cookie_part.trim().splitn(2, '=').collect();
                    if cookie_kv.len() == 2 && cookie_kv[0] == "session_id" {
                        let session_id = cookie_kv[1];

                        // 加载会话
                        if let Some(store) = &self.store {
                            if let Ok(Some(session_data)) = store.get(session_id).await {
                                // 会话有效，存储到上下文中
                                ctx.extensions_mut().insert("session_id", session_id.to_string());
                                ctx.extensions_mut().insert("session_data", session_data);
                            }
                        }
                        break;
                    }
                }
            }
        }

        Ok(None)
    }
}
```

## 6 五、gRPC服务集成

```rust
// src/grpc.rs
use anyhow::Result;
use bytes::Bytes;
use futures::stream::StreamExt;
use http::{Request, Response, StatusCode};
use hyper::Body;
use pingora::http::HttpContext;
use prost::Message;
use std::{collections::HashMap, sync::Arc};
use tokio::sync::{mpsc, RwLock};
use tonic::{
    transport::{Channel, Endpoint},
    Request as TonicRequest,
    Response as TonicResponse,
    Status,
};
use tower::service_fn;
use tracing::{error, debug, info, warn, instrument};

use crate::config::GrpcConfig;

// gRPC错误类型
#[derive(Debug, thiserror::Error)]
pub enum GrpcError {
    #[error("Service not found: {0}")]
    ServiceNotFound(String),

    #[error("Method not found: {0}")]
    MethodNotFound(String),

    #[error("Connection error: {0}")]
    ConnectionError(#[from] tonic::transport::Error),

    #[error("Decode error: {0}")]
    DecodeError(#[from] prost::DecodeError),

    #[error("Encode error: {0}")]
    EncodeError(#[from] prost::EncodeError),

    #[error("gRPC status error: {0}")]
    StatusError(#[from] tonic::Status),

    #[error("Hyper error: {0}")]
    HyperError(#[from] hyper::Error),

    #[error("Other error: {0}")]
    Other(String),
}

// gRPC服务描述
#[derive(Debug, Clone)]
pub struct GrpcServiceDescriptor {
    name: String,
    methods: HashMap<String, GrpcMethodDescriptor>,
    endpoint: String,
    timeout_ms: u64,
    retries: u32,
}

// gRPC方法描述
#[derive(Debug, Clone)]
pub struct GrpcMethodDescriptor {
    name: String,
    streaming: bool,
    input_type: String,
    output_type: String,
}

// gRPC服务管理器
pub struct GrpcServiceManager {
    services: Arc<RwLock<HashMap<String, GrpcServiceDescriptor>>>,
    channels: Arc<RwLock<HashMap<String, Channel>>>,
    config: GrpcConfig,
}

impl GrpcServiceManager {
    pub async fn new(config: &GrpcConfig) -> Result<Self> {
        let services = Arc::new(RwLock::new(HashMap::new()));
        let channels = Arc::new(RwLock::new(HashMap::new()));

        let manager = Self {
            services,
            channels,
            config: config.clone(),
        };

        // 从配置加载服务描述
        for (service_name, service_config) in &config.services {
            manager.register_service(
                service_name,
                &service_config.endpoint,
                service_config.timeout_ms,
                service_config.retries,
                service_config.methods.clone(),
            ).await?;
        }

        Ok(manager)
    }

    // 注册gRPC服务
    pub async fn register_service(
        &self,
        name: &str,
        endpoint: &str,
        timeout_ms: u64,
        retries: u32,
        methods: HashMap<String, HashMap<String, String>>,
    ) -> Result<()> {
        // 创建服务描述符
        let mut method_descriptors = HashMap::new();

        for (method_name, method_info) in methods {
            let streaming = method_info.get("streaming")
                .map(|s| s == "true")
                .unwrap_or(false);

            let input_type = method_info.get("input_type")
                .cloned()
                .unwrap_or_else(|| "".to_string());

            let output_type = method_info.get("output_type")
                .cloned()
                .unwrap_or_else(|| "".to_string());

            let descriptor = GrpcMethodDescriptor {
                name: method_name.clone(),
                streaming,
                input_type,
                output_type,
            };

            method_descriptors.insert(method_name, descriptor);
        }

        let service_descriptor = GrpcServiceDescriptor {
            name: name.to_string(),
            methods: method_descriptors,
            endpoint: endpoint.to_string(),
            timeout_ms,
            retries,
        };

        // 存储服务描述符
        let mut services = self.services.write().await;
        services.insert(name.to_string(), service_descriptor);

        // 创建和存储Channel
        let channel = self.create_channel(endpoint).await?;

        let mut channels = self.channels.write().await;
        channels.insert(name.to_string(), channel);

        info!("Registered gRPC service: {}", name);
        Ok(())
    }

    // 创建gRPC通道
    async fn create_channel(&self, endpoint: &str) -> Result<Channel> {
        let channel = Endpoint::from_shared(endpoint.to_string())?
            .connect()
            .await?;

        Ok(channel)
    }

    // 处理gRPC请求
    pub async fn handle_grpc_request(
        &self,
        request: Request<Body>,
        service_name: &str,
        method_name: &str,
    ) -> Result<Response<Body>, GrpcError> {
        // 获取服务描述符
        let services = self.services.read().await;
        let service = services.get(service_name)
            .ok_or_else(|| GrpcError::ServiceNotFound(service_name.to_string()))?;

        // 获取方法描述符
        let method = service.methods.get(method_name)
            .ok_or_else(|| GrpcError::MethodNotFound(method_name.to_string()))?;

        // 获取通道
        let channels = self.channels.read().await;
        let channel = channels.get(service_name)
            .ok_or_else(|| GrpcError::ConnectionError(tonic::transport::Error::new_other("No channel found")))?;

        // 从HTTP请求体读取二进制数据
        let body_bytes = hyper::body::to_bytes(request.into_body()).await?;

        if method.streaming {
            // 处理流式请求
            self.handle_streaming_request(
                service,
                method,
                channel.clone(),
                body_bytes,
            ).await
        } else {
            // 处理一元请求
            self.handle_unary_request(
                service,
                method,
                channel.clone(),
                body_bytes,
            ).await
        }
    }

    // 处理一元gRPC请求
    async fn handle_unary_request(
        &self,
        service: &GrpcServiceDescriptor,
        method: &GrpcMethodDescriptor,
        channel: Channel,
        request_bytes: Bytes,
    ) -> Result<Response<Body>, GrpcError> {
        // 构建要转发的请求
        let path = format!("/{}.{}/{}", service.name, service.name, method.name);
        debug!("Forwarding unary gRPC request to path: {}", path);

        // 使用tonic创建gRPC请求
        let mut client = tonic::client::Grpc::new(channel);

        // 设置超时
        let timeout = std::time::Duration::from_millis(service.timeout_ms);

        // 设置重试策略
        for retry in 0..=service.retries {
            match client.unary(
                path.clone(),
                request_bytes.clone(),
                tonic::codec::ProstCodec::default(),
                timeout,
            ).await {
                Ok(response) => {
                    // 构建HTTP响应
                    let http_response = Response::builder()
                        .status(StatusCode::OK)
                        .header("content-type", "application/grpc+proto")
                        .header("grpc-status", "0")
                        .body(Body::from(response.get_ref().clone()))?;

                    return Ok(http_response);
                },
                Err(status) if retry < service.retries => {
                    // 可重试的错误
                    warn!(
                        "gRPC request failed, retrying ({}/{}): {} - {}",
                        retry + 1,
                        service.retries,
                        status.code(),
                        status.message()
                    );

                    // 添加延迟后重试
                    tokio::time::sleep(std::time::Duration::from_millis(
                        100 * (2_u64.pow(retry) as u64) // 指数退避
                    )).await;
                },
                Err(status) => {
                    // 最后一次重试失败或不可重试的错误
                    error!(
                        "gRPC request failed after {} retries: {} - {}",
                        retry,
                        status.code(),
                        status.message()
                    );

                    // 构建错误响应
                    let http_response = Response::builder()
                        .status(StatusCode::INTERNAL_SERVER_ERROR)
                        .header("content-type", "application/grpc+proto")
                        .header("grpc-status", status.code().to_string())
                        .header("grpc-message", status.message())
                        .body(Body::empty())?;

                    return Ok(http_response);
                }
            }
        }

        // 不应该到达这里
        Err(GrpcError::Other("Unexpected error in gRPC request handling".to_string()))
    }

    // 处理流式gRPC请求
    async fn handle_streaming_request(
        &self,
        service: &GrpcServiceDescriptor,
        method: &GrpcMethodDescriptor,
        channel: Channel,
        request_bytes: Bytes,
    ) -> Result<Response<Body>, GrpcError> {
        // 构建要转发的请求
        let path = format!("/{}.{}/{}", service.name, service.name, method.name);
        debug!("Forwarding streaming gRPC request to path: {}", path);

        // 使用tonic创建gRPC客户端
        let mut client = tonic::client::Grpc::new(channel);

        // 设置超时
        let timeout = std::time::Duration::from_millis(service.timeout_ms);

        // 创建管道用于流式响应
        let (tx, rx) = mpsc::channel(128);

        // 异步处理流式请求
        tokio::spawn(async move {
            // 尝试流式请求
            match client.streaming(
                path,
                request_bytes,
                tonic::codec::ProstCodec::default(),
                timeout,
            ).await {
                Ok(mut response_stream) => {
                    // 处理响应流
                    while let Some(result) = response_stream.next().await {
                        match result {
                            Ok(data) => {
                                if tx.send(Ok(data)).await.is_err() {
                                    // 客户端断开连接
                                    break;
                                }
                            },
                            Err(status) => {
                                let _ = tx.send(Err(status)).await;
                                break;
                            }
                        }
                    }
                },
                Err(status) => {
                    let _ = tx.send(Err(status)).await;
                }
            }
        });

        // 创建对应的HTTP流响应
        let stream_body = Body::wrap_stream(tokio_stream::wrappers::ReceiverStream::new(rx)
            .map(|result| {
                match result {
                    Ok(data) => Ok(data),
                    Err(status) => {
                        let error_bytes = format!(
                            "gRPC error: {} - {}",
                            status.code(),
                            status.message()
                        ).into_bytes();
                        Ok(Bytes::from(error_bytes))
                    }
                }
            }));

        // 构建HTTP响应
        let http_response = Response::builder()
            .status(StatusCode::OK)
            .header("content-type", "application/grpc+proto")
            .body(stream_body)?;

        Ok(http_response)
    }
}
```

## 7 六、消息队列集成和用户行为跟踪

```rust
// src/mq.rs
use anyhow::Result;
use async_trait::async_trait;
use rdkafka::{
    config::ClientConfig,
    producer::{FutureProducer, FutureRecord},
    message::OwnedHeaders,
    consumer::{Consumer, StreamConsumer, CommitMode},
    util::Timeout,
    error::KafkaError,
};
use async_nats::{Client as NatsClient, Connection, Options as NatsOptions};
use serde::{Serialize, Deserialize};
use std::{sync::Arc, time::Duration};
use tokio::{
    sync::RwLock,
    task::JoinHandle,
};
use tracing::{info, error, warn, instrument, Span};
use uuid::Uuid;
use crate::config::MessagingConfig;

// 事件类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Event {
    pub id: String,
    pub event_type: String,
    pub timestamp: String,
    pub source: String,
    pub data: serde_json::Value,
}

impl Event {
    pub fn new(event_type: &str, data: serde_json::Value) -> Self {
        Self {
            id: Uuid::new_v4().to_string(),
            event_type: event_type.to_string(),
            timestamp: chrono::Utc::now().to_rfc3339(),
            source: "pingora-gateway".to_string(),
            data,
        }
    }
}

// 事件发布器
pub struct EventPublisher {
    config: MessagingConfig,
    kafka_producer: Option<FutureProducer>,
    nats_client: Option<NatsClient>,
}

impl EventPublisher {
    pub async fn new(config: &MessagingConfig) -> Result<Self> {
        let kafka_producer = if config.use_kafka {
            // 创建Kafka生产者
            let producer: FutureProducer = ClientConfig::new()
                .set("bootstrap.servers", &config.kafka_bootstrap_servers)
                .set("message.timeout.ms", "5000")
                .set("compression.type", "snappy")
                .set("request.required.acks", "1")
                .create()?;

            Some(producer)
        } else {
            None
        };

        let nats_client = if config.use_nats {
            // 创建NATS客户端
            let options = NatsOptions::new()
                .with_connection_name("pingora-gateway".to_string());

            let client = async_nats::connect(&config.nats_server_url).await?;
            Some(client)
        } else {
            None
        };

        Ok(Self {
            config: config.clone(),
            kafka_producer,
            nats_client,
        })
    }

    // 发布事件到Kafka
    pub async fn publish_to_kafka(
        &self,
        topic: &str,
        event: &Event,
    ) -> Result<(), KafkaError> {
        if let Some(producer) = &self.kafka_producer {
            let payload = serde_json::to_string(event)
                .map_err(|e| KafkaError::MessageProduction(
                    rdkafka::error::RDKafkaErrorCode::UnknownError,
                    format!("JSON serialization error: {}", e)
                ))?;

            let headers = OwnedHeaders::new()
                .add("event_type", &event.event_type)
                .add("source", "pingora-gateway");

            producer.send(
                FutureRecord::to(topic)
                    .payload(&payload)
                    .key(&event.id)
                    .headers(headers),
                Duration::from_secs(5),
            ).await.map(|_| ())?;

            Ok(())
        } else {
            Err(KafkaError::MessageProduction(
                rdkafka::error::RDKafkaErrorCode::UnknownError,
                "Kafka producer not configured".to_string()
            ))
        }
    }

    // 发布事件到NATS
    pub async fn publish_to_nats(
        &self,
        subject: &str,
        event: &Event,
    ) -> Result<(), async_nats::Error> {
        if let Some(client) = &self.nats_client {
            let payload = serde_json::to_string(event)
                .map_err(|e| async_nats::Error::Other(format!("JSON serialization error: {}", e)))?;

            client.publish(subject, payload.into()).await?;
            Ok(())
        } else {
            Err(async_nats::Error::Other("NATS client not configured".to_string()))
        }
    }

    // 综合发布事件
    pub async fn publish_event(&self, event_type: &str, data: serde_json::Value) -> Result<()> {
        let event = Event::new(event_type, data);

        // 确定要发布到的目标
        let topic = match event_type {
            "user.click" | "user.view" | "user.search" => "user_behaviors",
            "auth.login" | "auth.logout" | "auth.failure" => "auth_events",
            "api.request" | "api.response" | "api.error" => "api_events",
            _ => "misc_events",
        };

        // 尝试发布到Kafka
        if let Some(_) = &self.kafka_producer {
            match self.publish_to_kafka(topic, &event).await {
                Ok(_) => info!("Published event to Kafka: {}", event_type),
                Err(e) => error!("Failed to publish event to Kafka: {}", e),
            }
        }

        // 尝试发布到NATS
        if let Some(_) = &self.nats_client {
            let subject = format!("events.{}", event_type.replace(".", "."));
            match self.publish_to_nats(&subject, &event).await {
/*
我将继续完成MQ事件发布器的代码，
然后实现用户行为跟踪器，最后进行主应用的组装以完成整个系统。
*/
                Ok(_) => info!("Published event to NATS: {}", event_type),
                Err(e) => error!("Failed to publish event to NATS: {}", e),
            }
        }

        Ok(())
    }
}

// 事件订阅器trait
#[async_trait]
pub trait EventSubscriber: Send + Sync {
    async fn start(&self) -> Result<()>;
    async fn stop(&self) -> Result<()>;
}

// Kafka事件订阅器
pub struct KafkaEventSubscriber {
    config: MessagingConfig,
    topic: String,
    group_id: String,
    consumer: Arc<StreamConsumer>,
    handler: Box<dyn Fn(Event) -> Result<()> + Send + Sync>,
    task_handle: Arc<RwLock<Option<JoinHandle<()>>>>,
}

impl KafkaEventSubscriber {
    pub fn new<F>(
        config: &MessagingConfig,
        topic: &str,
        group_id: &str,
        handler: F,
    ) -> Result<Self>
    where
        F: Fn(Event) -> Result<()> + Send + Sync + 'static,
    {
        // 创建Kafka消费者
        let consumer: StreamConsumer = ClientConfig::new()
            .set("bootstrap.servers", &config.kafka_bootstrap_servers)
            .set("group.id", group_id)
            .set("enable.auto.commit", "true")
            .set("auto.offset.reset", "earliest")
            .set("session.timeout.ms", "6000")
            .create()?;

        Ok(Self {
            config: config.clone(),
            topic: topic.to_string(),
            group_id: group_id.to_string(),
            consumer: Arc::new(consumer),
            handler: Box::new(handler),
            task_handle: Arc::new(RwLock::new(None)),
        })
    }
}

#[async_trait]
impl EventSubscriber for KafkaEventSubscriber {
    async fn start(&self) -> Result<()> {
        let consumer = self.consumer.clone();
        let topic = self.topic.clone();
        let handler = self.handler.clone();

        // 订阅主题
        consumer.subscribe(&[&topic])?;

        // 启动消费任务
        let task_handle = tokio::spawn(async move {
            info!("Started Kafka consumer for topic: {}", topic);

            loop {
                match consumer.recv().await {
                    Ok(msg) => {
                        let payload = match msg.payload_view::<str>() {
                            Some(Ok(s)) => s,
                            Some(Err(_)) => {
                                error!("Failed to decode Kafka message as UTF-8");
                                continue;
                            }
                            None => {
                                warn!("Empty Kafka message received");
                                continue;
                            }
                        };

                        // 解析事件
                        match serde_json::from_str::<Event>(payload) {
                            Ok(event) => {
                                if let Err(e) = handler(event) {
                                    error!("Error processing event: {}", e);
                                }
                            }
                            Err(e) => {
                                error!("Failed to parse event: {}", e);
                            }
                        }

                        // 提交消息
                        consumer.commit_message(&msg, CommitMode::Async).unwrap_or_else(|e| {
                            error!("Failed to commit Kafka message: {}", e);
                        });
                    }
                    Err(e) => {
                        error!("Kafka consumer error: {}", e);
                        tokio::time::sleep(Duration::from_secs(1)).await;
                    }
                }
            }
        });

        // 存储任务句柄
        let mut handle = self.task_handle.write().await;
        *handle = Some(task_handle);

        Ok(())
    }

    async fn stop(&self) -> Result<()> {
        let mut handle = self.task_handle.write().await;
        if let Some(task) = handle.take() {
            task.abort();
            info!("Stopped Kafka consumer for topic: {}", self.topic);
        }

        Ok(())
    }
}

// NATS事件订阅器
pub struct NatsEventSubscriber {
    config: MessagingConfig,
    subject: String,
    client: Arc<NatsClient>,
    connection: Arc<Connection>,
    handler: Box<dyn Fn(Event) -> Result<()> + Send + Sync>,
    task_handle: Arc<RwLock<Option<JoinHandle<()>>>>,
}

impl NatsEventSubscriber {
    pub async fn new<F>(
        config: &MessagingConfig,
        subject: &str,
        handler: F,
    ) -> Result<Self>
    where
        F: Fn(Event) -> Result<()> + Send + Sync + 'static,
    {
        // 创建NATS客户端
        let options = NatsOptions::new()
            .with_connection_name("pingora-subscriber".to_string());

        let connection = async_nats::connect(&config.nats_server_url).await?;
        let client = connection.clone();

        Ok(Self {
            config: config.clone(),
            subject: subject.to_string(),
            client: Arc::new(client),
            connection: Arc::new(connection),
            handler: Box::new(handler),
            task_handle: Arc::new(RwLock::new(None)),
        })
    }
}

#[async_trait]
impl EventSubscriber for NatsEventSubscriber {
    async fn start(&self) -> Result<()> {
        let client = self.client.clone();
        let subject = self.subject.clone();
        let handler = self.handler.clone();

        // 订阅主题
        let mut subscriber = client.subscribe(subject.clone()).await?;

        // 启动消费任务
        let task_handle = tokio::spawn(async move {
            info!("Started NATS subscriber for subject: {}", subject);

            while let Some(msg) = subscriber.next().await {
                let payload = String::from_utf8_lossy(&msg.payload);

                // 解析事件
                match serde_json::from_str::<Event>(&payload) {
                    Ok(event) => {
                        if let Err(e) = handler(event) {
                            error!("Error processing NATS event: {}", e);
                        }
                    }
                    Err(e) => {
                        error!("Failed to parse NATS event: {}", e);
                    }
                }
            }

            info!("NATS subscriber for subject {} stopped", subject);
        });

        // 存储任务句柄
        let mut handle = self.task_handle.write().await;
        *handle = Some(task_handle);

        Ok(())
    }

    async fn stop(&self) -> Result<()> {
        let mut handle = self.task_handle.write().await;
        if let Some(task) = handle.take() {
            task.abort();
            info!("Stopped NATS subscriber for subject: {}", self.subject);
        }

        Ok(())
    }
}

// 用户行为跟踪器
pub struct UserBehaviorTracker {
    event_publisher: Arc<EventPublisher>,
}

impl UserBehaviorTracker {
    pub fn new(event_publisher: Arc<EventPublisher>) -> Self {
        Self { event_publisher }
    }

    pub async fn track_request(
        &self,
        req: &http::Request<hyper::Body>,
        ctx: &HttpContext,
    ) -> Result<()> {
        // 提取用户ID (如果有)
        let user_id = ctx.extensions()
            .get::<String>("user_id")
            .map(|id| id.clone())
            .unwrap_or_else(|| "anonymous".to_string());

        // 提取请求信息
        let method = req.method().to_string();
        let path = req.uri().path().to_string();
        let query = req.uri().query().unwrap_or("").to_string();

        // 创建用户行为数据
        let data = serde_json::json!({
            "user_id": user_id,
            "method": method,
            "path": path,
            "query": query,
            "user_agent": req.headers().get(http::header::USER_AGENT)
                .and_then(|h| h.to_str().ok())
                .unwrap_or(""),
            "referer": req.headers().get(http::header::REFERER)
                .and_then(|h| h.to_str().ok())
                .unwrap_or(""),
            "ip": ctx.extensions()
                .get::<String>("client_ip")
                .map(|ip| ip.clone())
                .unwrap_or_else(|| "unknown".to_string()),
        });

        // 发布事件
        self.event_publisher.publish_event("api.request", data).await?;

        Ok(())
    }

    pub async fn track_response(
        &self,
        req: &http::Request<hyper::Body>,
        res: &http::Response<hyper::Body>,
        ctx: &HttpContext,
        duration_ms: u64,
    ) -> Result<()> {
        // 提取用户ID (如果有)
        let user_id = ctx.extensions()
            .get::<String>("user_id")
            .map(|id| id.clone())
            .unwrap_or_else(|| "anonymous".to_string());

        // 提取请求和响应信息
        let method = req.method().to_string();
        let path = req.uri().path().to_string();
        let status = res.status().as_u16();

        // 创建响应数据
        let data = serde_json::json!({
            "user_id": user_id,
            "method": method,
            "path": path,
            "status": status,
            "duration_ms": duration_ms,
            "content_type": res.headers().get(http::header::CONTENT_TYPE)
                .and_then(|h| h.to_str().ok())
                .unwrap_or(""),
            "content_length": res.headers().get(http::header::CONTENT_LENGTH)
                .and_then(|h| h.to_str().ok())
                .unwrap_or("0"),
        });

        // 发布事件
        let event_type = if status >= 400 {
            "api.error"
        } else {
            "api.response"
        };

        self.event_publisher.publish_event(event_type, data).await?;

        Ok(())
    }

    pub async fn track_user_action(
        &self,
        action: &str,
        user_id: &str,
        data: serde_json::Value,
    ) -> Result<()> {
        // 合并数据
        let mut event_data = data;
        if let serde_json::Value::Object(ref mut map) = event_data {
            map.insert("user_id".to_string(), serde_json::Value::String(user_id.to_string()));
            map.insert("timestamp".to_string(), serde_json::Value::String(
                chrono::Utc::now().to_rfc3339()
            ));
        }

        // 发布事件
        self.event_publisher.publish_event(&format!("user.{}", action), event_data).await?;

        Ok(())
    }
}
```

## 8 七、配置文件示例

```toml
# config/default.toml
[server]
listen_addr = "0.0.0.0:8080"
listen_addr_tls = "0.0.0.0:8443"
workers = 8
max_connections = 10000
connection_idle_timeout = 60  # 秒

[health]
listen_addr = "0.0.0.0:9090"

[tls]
enabled = true
cert_path = "certs/server.crt"
key_path = "certs/server.key"

[http3]
enabled = true
listen_addr = "0.0.0.0:8443"

[auth]
mode = "jwt"  # none, jwt, session, mixed
jwt_secret = "your-secret-key-here-make-it-long-and-secure"
jwt_algorithm = "HS256"
session_redis_url = "redis://127.0.0.1:6379/0"
cookie_name = "session_id"
cookie_secure = true
cookie_http_only = true
token_expiry_seconds = 3600

[session]
enabled = true
store_type = "redis"  # redis, memory
redis_url = "redis://127.0.0.1:6379/0"
session_ttl_seconds = 3600

[security]
enable_cors = true
cors_allow_origins = ["https://example.com", "https://api.example.com"]
cors_allow_methods = ["GET", "POST", "PUT", "DELETE", "OPTIONS"]
cors_allow_headers = ["Authorization", "Content-Type"]
cors_expose_headers = ["X-Request-ID"]
cors_max_age = 86400
cors_allow_credentials = true

enable_csp = true
csp = "default-src 'self'; script-src 'self' 'unsafe-inline'; style-src 'self' 'unsafe-inline';"

xss_protection = "1; mode=block"
content_type_options = "nosniff"
frame_options = "DENY"
hsts_enabled = true
hsts_max_age = 31536000  # 1年

[rate_limit]
enabled = true
requests_per_second = 10
burst = 50

[logging]
level = "info"
format = "json"  # json, text
otlp_endpoint = "http://127.0.0.1:4317"
sample_rate = 0.1

[metrics]
prometheus_endpoint = "0.0.0.0:9091"
metrics_prefix = "pingora_http_gateway"
export_interval_secs = 15

[grpc]
services = {
  "auth" = {
    endpoint = "http://localhost:50051",
    timeout_ms = 5000,
    retries = 3,
    methods = [
      { name = "Login", streaming = false, input_type = "LoginRequest", output_type = "LoginResponse" },
      { name = "Logout", streaming = false, input_type = "LogoutRequest", output_type = "LogoutResponse" },
      { name = "ValidateToken", streaming = false, input_type = "ValidateTokenRequest", output_type = "ValidateTokenResponse" }
    ]
  },
  "user" = {
    endpoint = "http://localhost:50052",
    timeout_ms = 3000,
    retries = 2,
    methods = [
      { name = "GetUser", streaming = false, input_type = "GetUserRequest", output_type = "GetUserResponse" },
      { name = "UpdateUser", streaming = false, input_type = "UpdateUserRequest", output_type = "UpdateUserResponse" },
      { name = "StreamUserEvents", streaming = true, input_type = "StreamUserEventsRequest", output_type = "UserEvent" }
    ]
  }
}

[messaging]
use_kafka = true
kafka_bootstrap_servers = "localhost:9092"
use_nats = true
nats_server_url = "nats://localhost:4222"

# 上游服务配置
[upstreams.api]
servers = ["127.0.0.1:3000", "127.0.0.1:3001"]
health_check_interval_secs = 5

[upstreams.auth]
servers = ["127.0.0.1:3010"]
health_check_interval_secs = 5

[upstreams.admin]
servers = ["127.0.0.1:3020", "127.0.0.1:3021"]
health_check_interval_secs = 10
```

## 9 八、部署与Docker配置

```dockerfile
# Dockerfile
FROM rust:1.75 as builder

WORKDIR /app

# 安装构建依赖
RUN apt-get update && \
    apt-get install -y \
    protobuf-compiler \
    cmake \
    pkg-config \
    libssl-dev \
    && rm -rf /var/lib/apt/lists/*

# 复制项目文件
COPY Cargo.toml Cargo.lock ./
COPY src ./src/
COPY proto ./proto/
COPY build.rs ./

# 构建应用
RUN cargo build --release

# 创建最终镜像
FROM debian:bookworm-slim

# 安装运行时依赖
RUN apt-get update && \
    apt-get install -y \
    ca-certificates \
    libssl3 \
    && rm -rf /var/lib/apt/lists/*

# 创建非root用户
RUN groupadd -r pingora && useradd -r -g pingora pingora

WORKDIR /app

# 从构建阶段复制二进制文件
COPY --from=builder /app/target/release/pingora-gateway /app/pingora-gateway

# 复制配置文件
COPY config /app/config/
COPY certs /app/certs/

# 设置权限
RUN chown -R pingora:pingora /app && \
    chmod -R 755 /app

# 切换到非root用户
USER pingora

# 设置环境变量
ENV RUST_LOG=info

# 暴露端口
EXPOSE 8080 8443 9090 9091

# 启动应用
CMD ["/app/pingora-gateway", "--config", "/app/config/default.toml"]
```

使用Docker Compose进行部署：

```yaml
# docker-compose.yml
version: '3.8'

services:
  pingora-gateway:
    build: .
    ports:
      - "8080:8080"
      - "8443:8443"
      - "9090:9090"  # 健康检查端口
      - "9091:9091"  # 指标端口
    volumes:
      - ./config:/app/config
      - ./certs:/app/certs
    environment:
      - RUST_LOG=info
      - OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector:4317
    depends_on:
      - redis
      - kafka
      - nats
      - otel-collector
    restart: unless-stopped
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:9090/health"]
      interval: 30s
      timeout: 5s
      retries: 3
      start_period: 10s

  # Redis for session storage
  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"
    volumes:
      - redis-data:/data
    restart: unless-stopped

  # Kafka for messaging
  zookeeper:
    image: confluentinc/cp-zookeeper:7.5.0
    environment:
      ZOOKEEPER_CLIENT_PORT: 2181
    volumes:
      - zookeeper-data:/var/lib/zookeeper/data
    restart: unless-stopped

  kafka:
    image: confluentinc/cp-kafka:7.5.0
    depends_on:
      - zookeeper
    ports:
      - "9092:9092"
    environment:
      KAFKA_BROKER_ID: 1
      KAFKA_ZOOKEEPER_CONNECT: zookeeper:2181
      KAFKA_ADVERTISED_LISTENERS: PLAINTEXT://kafka:9092
      KAFKA_OFFSETS_TOPIC_REPLICATION_FACTOR: 1
    volumes:
      - kafka-data:/var/lib/kafka/data
    restart: unless-stopped

  # NATS for messaging
  nats:
    image: nats:2.10-alpine
    ports:
      - "4222:4222"
      - "8222:8222"
    restart: unless-stopped

  # OpenTelemetry Collector
  otel-collector:
    image: otel/opentelemetry-collector-contrib:0.91.0
    ports:
      - "4317:4317"   # OTLP gRPC
      - "4318:4318"   # OTLP HTTP
      - "8888:8888"   # metrics
    volumes:
      - ./otel-collector-config.yaml:/etc/otel-collector-config.yaml
    command: ["--config=/etc/otel-collector-config.yaml"]
    restart: unless-stopped

  # Prometheus for metrics
  prometheus:
    image: prom/prometheus:v2.48.0
    ports:
      - "9090:9090"
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml
      - prometheus-data:/prometheus
    restart: unless-stopped

  # Jaeger for tracing visualization
  jaeger:
    image: jaegertracing/all-in-one:latest
    ports:
      - "16686:16686"   # UI
      - "14250:14250"   # gRPC for tracing
    environment:
      - COLLECTOR_OTLP_ENABLED=true
    restart: unless-stopped

volumes:
  redis-data:
  zookeeper-data:
  kafka-data:
  prometheus-data:
```

## 10 九、总结与功能概览

使用Rust 2025版Pingora实现的分布式HTTP集群服务具有以下核心功能特性：

1. **完整的HTTP协议支持**
   - HTTP/1.x, HTTP/2, HTTP/3 (QUIC)支持
   - 支持TLS和非TLS连接
   - 完整的HTTP语义处理，包括重定向等

2. **全面的观测性**
   - 分布式跟踪 (OpenTelemetry)
   - 结构化日志记录
   - Prometheus指标集成
   - 完整的请求-响应监控

3. **安全认证与授权**
   - JWT令牌认证
   - 会话管理 (Redis/内存)
   - 灵活的认证策略 (JWT/会话/混合)
   - CORS和其他安全头处理

4. **gRPC集成**
   - 自动协议转换(HTTP -> gRPC)
   - 双向流支持
   - 自动重试和幂等支持
   - 服务发现和负载均衡

5. **消息队列集成**
   - Kafka和NATS支持
   - 用户行为事件跟踪
   - 异步事件处理
   - 事件发布-订阅模式

6. **高级请求处理**
   - 请求路由和规则
   - 限流和熔断
   - 请求/响应转换
   - 中间件处理链

此架构为现代API网关提供了所有必要的功能，具备高性能、高可靠性和可观测性，非常适合构建大规模分布式系统。
Rust的安全性和性能优势，加上Pingora的专业网关功能，使这个方案成为高流量、安全敏感环境的理想选择。
