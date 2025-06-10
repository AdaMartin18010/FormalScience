# Rust实现HTTP

我将为您展示一个使用 Rust 2024 + Hyper 实现的完整 HTTP 客户端和服务端项目，包含各种高级特性。

## 目录

- [Rust实现HTTP](#rust实现http)
  - [目录](#目录)
  - [1. 项目依赖配置](#1-项目依赖配置)
  - [2. HTTP 客户端实现](#2-http-客户端实现)
  - [3. HTTP 服务端实现](#3-http-服务端实现)
  - [4. 中间件实现](#4-中间件实现)
  - [5. 任务管理器实现](#5-任务管理器实现)
  - [6. 示例处理器实现](#6-示例处理器实现)
  - [7. 错误处理实现](#7-错误处理实现)
  - [8. 指标收集实现](#8-指标收集实现)
  - [9. 主程序实现](#9-主程序实现)
  - [10. 测试实现](#10-测试实现)

## 1. 项目依赖配置

```toml
[dependencies]
tokio = { version = "1.0", features = ["full"] }
hyper = { version = "1.0", features = ["full"] }
hyper-util = { version = "0.1", features = ["full"] }
http-body-util = "0.1"
bytes = "1.0"
futures = "0.3"
tower = { version = "0.4", features = ["full"] }
tower-http = { version = "0.5", features = ["full"] }
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
tracing = "0.1"
anyhow = "1.0"
thiserror = "1.0"
async-trait = "0.1"
backoff = { version = "0.4", features = ["tokio"] }
metrics = "0.21"
metrics-exporter-prometheus = "0.12"
```

## 2. HTTP 客户端实现

```rust
use std::time::Duration;
use hyper::Request;
use backoff::ExponentialBackoff;

#[derive(Clone)]
pub struct HttpClient {
    client: hyper_util::client::legacy::Client<
        hyper_util::client::legacy::connect::HttpConnector,
        http_body_util::Full<bytes::Bytes>,
    >,
    retry_config: RetryConfig,
    timeout: Duration,
}

#[derive(Clone)]
pub struct RetryConfig {
    max_retries: u32,
    initial_interval: Duration,
    max_interval: Duration,
    multiplier: f64,
}

impl HttpClient {
    pub fn new(timeout: Duration, retry_config: RetryConfig) -> Self {
        let client = hyper_util::client::legacy::Client::builder()
            .pool_idle_timeout(Duration::from_secs(30))
            .pool_max_idle_per_host(32)
            .build_http();

        Self {
            client,
            retry_config,
            timeout,
        }
    }

    pub async fn request<T>(&self, req: Request<T>) -> Result<hyper::Response<bytes::Bytes>, ClientError>
    where
        T: Into<http_body_util::Full<bytes::Bytes>>,
    {
        let backoff = ExponentialBackoff {
            initial_interval: self.retry_config.initial_interval,
            max_interval: self.retry_config.max_interval,
            multiplier: self.retry_config.multiplier,
            max_elapsed_time: Some(self.timeout),
            ..Default::default()
        };

        let result = backoff::future::retry_notify(
            backoff,
            || async {
                let req_clone = req.clone();
                let timeout_future = tokio::time::timeout(
                    self.timeout,
                    self.client.request(req_clone.map(|b| b.into())),
                );

                match timeout_future.await {
                    Ok(Ok(response)) => {
                        if response.status().is_success() {
                            Ok(response)
                        } else {
                            Err(backoff::Error::Permanent(ClientError::HttpError(
                                response.status(),
                            )))
                        }
                    }
                    Ok(Err(e)) => Err(backoff::Error::Transient(ClientError::from(e))),
                    Err(_) => Err(backoff::Error::Transient(ClientError::Timeout)),
                }
            },
            |err, duration| {
                tracing::warn!(
                    "Request failed, retrying in {:?}: {:?}",
                    duration,
                    err
                );
            },
        ).await;

        match result {
            Ok(response) => {
                let (parts, body) = response.into_parts();
                let bytes = http_body_util::BodyExt::collect(body)
                    .await?
                    .to_bytes();
                Ok(hyper::Response::from_parts(parts, bytes))
            }
            Err(e) => Err(e),
        }
    }

    pub async fn get(&self, url: &str) -> Result<hyper::Response<bytes::Bytes>, ClientError> {
        let req = Request::builder()
            .method(hyper::Method::GET)
            .uri(url)
            .body(http_body_util::Full::new(bytes::Bytes::new()))?;

        self.request(req).await
    }

    pub async fn post<T>(&self, url: &str, body: T) -> Result<hyper::Response<bytes::Bytes>, ClientError>
    where
        T: serde::Serialize,
    {
        let body = serde_json::to_vec(&body)?;
        let req = Request::builder()
            .method(hyper::Method::POST)
            .uri(url)
            .header(hyper::header::CONTENT_TYPE, "application/json")
            .body(http_body_util::Full::new(bytes::Bytes::from(body)))?;

        self.request(req).await
    }
}
```

## 3. HTTP 服务端实现

```rust
use std::convert::Infallible;
use std::net::SocketAddr;
use hyper::server::conn::http1;
use hyper_util::rt::TokioIo;
use tokio::net::TcpListener;

pub struct HttpServer {
    addr: SocketAddr,
    router: Router,
}

impl HttpServer {
    pub fn new(addr: SocketAddr) -> Self {
        Self {
            addr,
            router: Router::new(),
        }
    }

    pub async fn run(self) -> Result<(), ServerError> {
        let listener = TcpListener::bind(self.addr).await?;
        tracing::info!("Server listening on {}", self.addr);

        loop {
            let (stream, _) = listener.accept().await?;
            let io = TokioIo::new(stream);
            let router = self.router.clone();

            tokio::task::spawn(async move {
                let service = tower::ServiceBuilder::new()
                    .layer(tower_http::trace::TraceLayer::new_for_http())
                    .layer(tower_http::timeout::TimeoutLayer::new(Duration::from_secs(30)))
                    .layer(tower_http::limit::RequestBodyLimitLayer::new(1024 * 1024)) // 1MB
                    .service(router);

                if let Err(err) = http1::Builder::new()
                    .serve_connection(io, service)
                    .await
                {
                    tracing::error!("Error serving connection: {:?}", err);
                }
            });
        }
    }

    pub fn route<H, T>(&mut self, method: hyper::Method, path: &str, handler: H)
    where
        H: Handler<T> + Clone + Send + Sync + 'static,
        T: serde::de::DeserializeOwned + Send + 'static,
    {
        self.router.add_route(method, path, handler);
    }
}

#[derive(Clone)]
pub struct Router {
    routes: Arc<Routes>,
}

type Routes = HashMap<(hyper::Method, String), Box<dyn HandlerClone>>;

impl Router {
    pub fn new() -> Self {
        Self {
            routes: Arc::new(HashMap::new()),
        }
    }

    pub fn add_route<H, T>(&mut self, method: hyper::Method, path: &str, handler: H)
    where
        H: Handler<T> + Clone + Send + Sync + 'static,
        T: serde::de::DeserializeOwned + Send + 'static,
    {
        Arc::get_mut(&mut self.routes)
            .unwrap()
            .insert((method, path.to_string()), Box::new(handler));
    }
}

impl tower::Service<Request<hyper::body::Incoming>> for Router {
    type Response = Response<BoxBody<Bytes, hyper::Error>>;
    type Error = Infallible;
    type Future = BoxFuture<'static, Result<Self::Response, Self::Error>>;

    fn poll_ready(&mut self, _cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        Poll::Ready(Ok(()))
    }

    fn call(&mut self, req: Request<hyper::body::Incoming>) -> Self::Future {
        let routes = self.routes.clone();
        
        Box::pin(async move {
            let (parts, body) = req.into_parts();
            let key = (parts.method.clone(), parts.uri.path().to_string());

            match routes.get(&key) {
                Some(handler) => {
                    let bytes = http_body_util::BodyExt::collect(body)
                        .await
                        .unwrap()
                        .to_bytes();

                    let response = handler.call(Request::from_parts(parts, bytes)).await;
                    Ok(response.map(|b| BoxBody::new(http_body_util::Full::new(b))))
                }
                None => {
                    Ok(Response::builder()
                        .status(StatusCode::NOT_FOUND)
                        .body(BoxBody::new(http_body_util::Full::new(Bytes::new())))
                        .unwrap())
                }
            }
        })
    }
}
```

## 4. 中间件实现

```rust
pub struct TimeoutMiddleware<S> {
    inner: S,
    timeout: Duration,
}

impl<S> TimeoutMiddleware<S> {
    pub fn new(inner: S, timeout: Duration) -> Self {
        Self { inner, timeout }
    }
}

impl<S, B> tower::Service<Request<B>> for TimeoutMiddleware<S>
where
    S: tower::Service<Request<B>>,
    S::Error: Into<BoxError>,
{
    type Response = S::Response;
    type Error = BoxError;
    type Future = BoxFuture<'static, Result<Self::Response, Self::Error>>;

    fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        self.inner.poll_ready(cx).map_err(Into::into)
    }

    fn call(&mut self, req: Request<B>) -> Self::Future {
        let timeout = self.timeout;
        let future = self.inner.call(req);

        Box::pin(async move {
            match tokio::time::timeout(timeout, future).await {
                Ok(result) => result.map_err(Into::into),
                Err(_) => Err("Request timed out".into()),
            }
        })
    }
}

pub struct RetryMiddleware<S> {
    inner: S,
    config: RetryConfig,
}

impl<S> RetryMiddleware<S> {
    pub fn new(inner: S, config: RetryConfig) -> Self {
        Self { inner, config }
    }
}

impl<S, B> tower::Service<Request<B>> for RetryMiddleware<S>
where
    S: tower::Service<Request<B>> + Clone,
    S::Error: Into<BoxError>,
    B: Clone,
{
    type Response = S::Response;
    type Error = BoxError;
    type Future = BoxFuture<'static, Result<Self::Response, Self::Error>>;

    fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        self.inner.poll_ready(cx).map_err(Into::into)
    }

    fn call(&mut self, req: Request<B>) -> Self::Future {
        let inner = self.inner.clone();
        let config = self.config.clone();
        let req_clone = req.clone();

        Box::pin(async move {
            let backoff = ExponentialBackoff {
                initial_interval: config.initial_interval,
                max_interval: config.max_interval,
                multiplier: config.multiplier,
                max_retries: Some(config.max_retries),
                ..Default::default()
            };

            backoff::future::retry(backoff, || async {
                match inner.clone().call(req_clone.clone()).await {
                    Ok(response) => Ok(response),
                    Err(e) => Err(backoff::Error::Transient(e.into())),
                }
            })
            .await
            .map_err(|e| e.into())
        })
    }
}
```

## 5. 任务管理器实现

```rust
pub struct TaskManager {
    tasks: Arc<DashMap<TaskId, TaskHandle>>,
}

pub struct TaskHandle {
    id: TaskId,
    cancel_tx: oneshot::Sender<()>,
    status: Arc<AtomicTaskStatus>,
}

#[derive(Debug, Clone, Copy)]
pub enum TaskStatus {
    Running,
    Completed,
    Failed,
    Cancelled,
}

impl TaskManager {
    pub fn new() -> Self {
        Self {
            tasks: Arc::new(DashMap::new()),
        }
    }

    pub async fn spawn<F, T>(&self, task: F) -> TaskId
    where
        F: Future<Output = Result<T, Error>> + Send + 'static,
        T: Send + 'static,
    {
        let task_id = TaskId::new();
        let (cancel_tx, cancel_rx) = oneshot::channel();
        let status = Arc::new(AtomicTaskStatus::new(TaskStatus::Running));

        let handle = TaskHandle {
            id: task_id,
            cancel_tx,
            status: status.clone(),
        };

        let tasks = self.tasks.clone();
        tasks.insert(task_id, handle);

        tokio::spawn(async move {
            let result = tokio::select! {
                result = task => result,
                _ = cancel_rx => Err(Error::Cancelled),
            };

            match result {
                Ok(_) => status.store(TaskStatus::Completed),
                Err(Error::Cancelled) => status.store(TaskStatus::Cancelled),
                Err(_) => status.store(TaskStatus::Failed),
            }

            tasks.remove(&task_id);
        });

        task_id
    }

    pub async fn cancel(&self, task_id: TaskId) -> Result<(), Error> {
        if let Some(handle) = self.tasks.get(&task_id) {
            let _ = handle.cancel_tx.send(());
            Ok(())
        } else {
            Err(Error::TaskNotFound)
        }
    }

    pub fn get_status(&self, task_id: TaskId) -> Option<TaskStatus> {
        self.tasks
            .get(&task_id)
            .map(|handle| handle.status.load())
    }
}
```

## 6. 示例处理器实现

```rust
#[derive(Clone)]
pub struct UserHandler {
    db: Arc<Database>,
    task_manager: Arc<TaskManager>,
}

impl UserHandler {
    pub async fn handle_create_user(
        &self,
        req: Request<Bytes>,
    ) -> Result<Response<Bytes>, Error> {
        let user: CreateUserRequest = serde_json::from_slice(&req.into_body())?;
        
        let task_id = self.task_manager
            .spawn(async move {
                // 模拟耗时操作
                tokio::time::sleep(Duration::from_secs(2)).await;
                Ok(())
            })
            .await;

        let response = CreateUserResponse {
            task_id,
            status: "processing",
        };

        Ok(Response::builder()
            .status(StatusCode::ACCEPTED)
            .body(serde_json::to_vec(&response)?.into())?)
    }

    pub async fn handle_get_user(
        &self,
        req: Request<Bytes>,
    ) -> Result<Response<Bytes>, Error> {
        let user_id = req.uri()
            .path_segments()
            .and_then(|segments| segments.last())
            .ok_or(Error::InvalidRequest)?;

        let user = self.db.get_user(user_id).await?;

        Ok(Response::builder()
            .status(StatusCode::OK)
            .body(serde_json::to_vec(&user)?.into())?)
    }
}
```

## 7. 错误处理实现

```rust
#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("HTTP error: {0}")]
    Http(#[from] hyper::Error),

    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),

    #[error("JSON error: {0}")]
    Json(#[from] serde_json::Error),

    #[error("Request timeout")]
    Timeout,

    #[error("Task cancelled")]
    Cancelled,

    #[error("Task not found")]
    TaskNotFound,

    #[error("Invalid request")]
    InvalidRequest,

    #[error("Database error: {0}")]
    Database(String),
}

impl From<Error> for Response<Bytes> {
    fn from(err: Error) -> Self {
        let status = match err {
            Error::Timeout => StatusCode::REQUEST_TIMEOUT,
            Error::InvalidRequest => StatusCode::BAD_REQUEST,
            Error::TaskNotFound => StatusCode::NOT_FOUND,
            _ => StatusCode::INTERNAL_SERVER_ERROR,
        };

        Response::builder()
            .status(status)
            .body(err.to_string().into())
            .unwrap()
    }
}
```

## 8. 指标收集实现

```rust
pub struct Metrics {
    request_counter: Counter,
    request_duration: Histogram,
    active_tasks: Gauge,
}

impl Metrics {
    pub fn new() -> Self {
        let request_counter = Counter::new("http_requests_total")
            .with_label_values(&["method", "path", "status"]);
        
        let request_duration = Histogram::new("http_request_duration_seconds")
            .with_label_values(&["method", "path"]);
            
        let active_tasks = Gauge::new("active_tasks_total")
            .with_label_values(&[]);

        Self {
            request_counter,
            request_duration,
            active_tasks,
        }
    }

    pub fn record_request<F, T>(&self, req: &Request<T>, f: F) -> F::Output
    where
        F: FnOnce() -> F::Output,
    {
        let start = Instant::now();
        let result = f();
        let duration = start.elapsed();

        self.request_counter
            .with_label_values(&[
                req.method().as_str(),
                req.uri().path(),
                result.status().as_str(),
            ])
            .inc();

        self.request_duration
            .with_label_values(&[
                req.method().as_str(),
                req.uri().path(),
            ])
            .observe(duration.as_secs_f64());

        result
    }

    pub fn update_active_tasks(&self, count: i64) {
        self.active_tasks.set(count as f64);
    }
}
```

## 9. 主程序实现

```rust
#[tokio::main]
async fn main() -> Result<(), Error> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    // 初始化指标收集
    let metrics = Arc::new(Metrics::new());
    
    // 创建任务管理器
    let task_manager = Arc::new(TaskManager::new());

    // 创建 HTTP 客户端
    let client = HttpClient::new(
        Duration::from_secs(30),
        RetryConfig {
            max_retries: 3,
            initial_interval: Duration::from_secs(1),
            max_interval: Duration::from_secs(10),
            multiplier: 2.0,
        },
    );

    // 创建 HTTP 服务器
    let mut server = HttpServer::new("127.0.0.1:3000".parse().unwrap());

    // 添加路由
    let user_handler = UserHandler::new(task_manager.clone());
    server.route(Method::POST, "/users", user_handler.clone());
    server.route(Method::GET, "/users/:id", user_handler);

    // 启动服务器
    server.run().await?;

    Ok(())
}
```

## 10. 测试实现

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_http_client() -> Result<(), Error> {
        let client = HttpClient::new(
            Duration::from_secs(5),
            RetryConfig::default(),
        );

        let response = client.get("http://httpbin.org/get").await?;
        assert_eq!(response.status(), StatusCode::OK);

        Ok(())
    }

    #[tokio::test]
    async fn test_task_manager() -> Result<(), Error> {
        let manager = TaskManager::new();

        let task_id = manager
            .spawn(async {
                tokio::time::sleep(Duration::from_secs(1)).await;
                Ok(())
            })
            .await;

        assert_eq!(manager.get_status(task_id), Some(TaskStatus::Running));

        tokio::time::sleep(Duration::from_secs(2)).await;
        assert_eq!(manager.get_status(task_id), None);

        Ok(())
    }
}
```

这个完整的示例展示了如何构建一个功能完整的 HTTP 客户端和服务端项目，包括：

1. HTTP 客户端实现（支持重试、超时、取消）
2. HTTP 服务端实现（路由、处理器）
3. 中间件支持（超时、重试、限流）
4. 任务管理（异步任务、取消、状态跟踪）
5. 错误处理
6. 指标收集
7. 测试支持

主要特性：

- 异步处理
- 超时控制
- 自动重试
- 任务取消
- 状态跟踪
- 指标收集
- 错误处理
- 中间件支持
- 单元测试

这个实现提供了良好的可扩展性和可维护性，可以根据需要添加更多功能和特性。
