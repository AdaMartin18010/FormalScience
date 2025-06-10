# Rust and Tonic 全特性实现分布式系统

下面是一个使用 Rust 2024 和 Tonic 全特性实现的分布式系统示例：

## 目录

- [Rust and Tonic 全特性实现分布式系统](#rust-and-tonic-全特性实现分布式系统)
  - [目录](#目录)
  - [1. 项目依赖配置](#1-项目依赖配置)
    - [2. Proto 定义](#2-proto-定义)
    - [3. 服务实现](#3-服务实现)
    - [4. 集群管理器实现](#4-集群管理器实现)
    - [5. 任务管理器实现](#5-任务管理器实现)
    - [6. 文件管理器实现](#6-文件管理器实现)
    - [7. 客户端实现](#7-客户端实现)
    - [8. 服务器启动](#8-服务器启动)
    - [9. 中间件实现](#9-中间件实现)
    - [10. 使用示例](#10-使用示例)

## 1. 项目依赖配置

```toml
[dependencies]
tonic = { version = "0.10", features = ["tls", "transport", "compression"] }
prost = "0.12"
tokio = { version = "1.0", features = ["full"] }
tokio-stream = { version = "0.1", features = ["net"] }
futures = "0.3"
async-stream = "0.3"
tower = { version = "0.4", features = ["full"] }
hyper = { version = "0.14", features = ["full"] }
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
tracing = "0.1"
anyhow = "1.0"

[build-dependencies]
tonic-build = { version = "0.10", features = ["prost"] }
```

### 2. Proto 定义

```protobuf
// distributed_system.proto
syntax = "proto3";
package distributed;

import "google/protobuf/empty.proto";
import "google/protobuf/timestamp.proto";

// 节点服务
service NodeService {
    // 节点注册
    rpc Register (RegisterRequest) returns (RegisterResponse);
    
    // 健康检查
    rpc HealthCheck (HealthCheckRequest) returns (stream HealthCheckResponse);
    
    // 双向流通信
    rpc Communicate (stream Message) returns (stream Message);
    
    // 文件传输
    rpc TransferFile (stream FileChunk) returns (FileResponse);
    
    // 任务处理
    rpc ProcessTask (TaskRequest) returns (TaskResponse);
    
    // 集群状态
    rpc GetClusterState (google.protobuf.Empty) returns (ClusterState);
}

message RegisterRequest {
    string node_id = 1;
    string address = 2;
    repeated string capabilities = 3;
    map<string, string> metadata = 4;
}

message RegisterResponse {
    string cluster_id = 1;
    repeated Node nodes = 2;
    bool success = 3;
}

message HealthCheckRequest {
    string node_id = 1;
}

message HealthCheckResponse {
    string node_id = 1;
    Status status = 2;
    google.protobuf.Timestamp timestamp = 3;
    map<string, string> metrics = 4;
}

message Message {
    string from_node = 1;
    string to_node = 2;
    MessageType type = 3;
    bytes payload = 4;
    google.protobuf.Timestamp timestamp = 5;
}

enum MessageType {
    UNKNOWN = 0;
    REQUEST = 1;
    RESPONSE = 2;
    EVENT = 3;
    ERROR = 4;
}

message FileChunk {
    string file_id = 1;
    bytes data = 2;
    uint32 chunk_number = 3;
    bool is_last = 4;
}

message FileResponse {
    string file_id = 1;
    bool success = 2;
    string message = 3;
}

message TaskRequest {
    string task_id = 1;
    string task_type = 2;
    bytes payload = 3;
    int32 priority = 4;
    map<string, string> metadata = 5;
}

message TaskResponse {
    string task_id = 1;
    Status status = 2;
    bytes result = 3;
    string error = 4;
}

message ClusterState {
    repeated Node nodes = 1;
    map<string, string> metrics = 2;
    repeated Task active_tasks = 3;
}

message Node {
    string node_id = 1;
    string address = 2;
    Status status = 3;
    repeated string capabilities = 4;
    map<string, string> metadata = 5;
}

enum Status {
    UNKNOWN = 0;
    HEALTHY = 1;
    DEGRADED = 2;
    UNHEALTHY = 3;
}

message Task {
    string task_id = 1;
    string task_type = 2;
    Status status = 3;
    string assigned_node = 4;
    google.protobuf.Timestamp created_at = 5;
    google.protobuf.Timestamp updated_at = 6;
}
```

### 3. 服务实现

```rust
use distributed::node_service_server::{NodeService, NodeServiceServer};
use tonic::{transport::Server, Request, Response, Status};
use tokio_stream::wrappers::ReceiverStream;
use futures::{Stream, StreamExt};
use std::pin::Pin;
use std::sync::Arc;
use tokio::sync::mpsc;

pub struct DistributedNode {
    node_id: String,
    cluster: Arc<ClusterManager>,
    task_manager: Arc<TaskManager>,
    file_manager: Arc<FileManager>,
}

#[tonic::async_trait]
impl NodeService for DistributedNode {
    async fn register(
        &self,
        request: Request<RegisterRequest>,
    ) -> Result<Response<RegisterResponse>, Status> {
        let req = request.into_inner();
        
        // 注册节点
        let result = self.cluster.register_node(Node {
            node_id: req.node_id,
            address: req.address,
            capabilities: req.capabilities,
            metadata: req.metadata,
            status: Status::HEALTHY,
        }).await.map_err(|e| Status::internal(e.to_string()))?;

        Ok(Response::new(RegisterResponse {
            cluster_id: result.cluster_id,
            nodes: result.nodes,
            success: true,
        }))
    }

    type HealthCheckStream = Pin<Box<dyn Stream<Item = Result<HealthCheckResponse, Status>> + Send>>;

    async fn health_check(
        &self,
        request: Request<HealthCheckRequest>,
    ) -> Result<Response<Self::HealthCheckStream>, Status> {
        let node_id = request.into_inner().node_id;
        let (tx, rx) = mpsc::channel(100);
        let cluster = self.cluster.clone();

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(std::time::Duration::from_secs(1));
            loop {
                interval.tick().await;
                
                let health_status = cluster.get_node_health(&node_id).await;
                if let Ok(status) = health_status {
                    let _ = tx.send(Ok(HealthCheckResponse {
                        node_id: node_id.clone(),
                        status: status.into(),
                        timestamp: Some(prost_types::Timestamp::from(std::time::SystemTime::now())),
                        metrics: cluster.get_node_metrics(&node_id).await.unwrap_or_default(),
                    })).await;
                }
            }
        });

        Ok(Response::new(Box::pin(ReceiverStream::new(rx))))
    }

    type CommunicateStream = Pin<Box<dyn Stream<Item = Result<Message, Status>> + Send>>;

    async fn communicate(
        &self,
        request: Request<tonic::Streaming<Message>>,
    ) -> Result<Response<Self::CommunicateStream>, Status> {
        let mut stream = request.into_inner();
        let (tx, rx) = mpsc::channel(100);
        let node_id = self.node_id.clone();

        tokio::spawn(async move {
            while let Some(message) = stream.next().await {
                match message {
                    Ok(msg) => {
                        // 处理接收到的消息
                        let response = Message {
                            from_node: node_id.clone(),
                            to_node: msg.from_node,
                            type_: MessageType::Response as i32,
                            payload: msg.payload,
                            timestamp: Some(prost_types::Timestamp::from(std::time::SystemTime::now())),
                        };
                        let _ = tx.send(Ok(response)).await;
                    }
                    Err(e) => {
                        let _ = tx.send(Err(e)).await;
                        break;
                    }
                }
            }
        });

        Ok(Response::new(Box::pin(ReceiverStream::new(rx))))
    }

    async fn transfer_file(
        &self,
        request: Request<tonic::Streaming<FileChunk>>,
    ) -> Result<Response<FileResponse>, Status> {
        let mut stream = request.into_inner();
        let file_manager = self.file_manager.clone();
        let mut chunks = Vec::new();

        while let Some(chunk) = stream.next().await {
            let chunk = chunk?;
            chunks.push(chunk);
        }

        // 处理文件传输
        match file_manager.process_file_chunks(chunks).await {
            Ok(file_id) => Ok(Response::new(FileResponse {
                file_id,
                success: true,
                message: "File transferred successfully".to_string(),
            })),
            Err(e) => Ok(Response::new(FileResponse {
                file_id: String::new(),
                success: false,
                message: e.to_string(),
            })),
        }
    }

    async fn process_task(
        &self,
        request: Request<TaskRequest>,
    ) -> Result<Response<TaskResponse>, Status> {
        let task = request.into_inner();
        
        // 处理任务
        match self.task_manager.process_task(task).await {
            Ok(result) => Ok(Response::new(TaskResponse {
                task_id: result.task_id,
                status: Status::HEALTHY,
                result: result.result,
                error: String::new(),
            })),
            Err(e) => Ok(Response::new(TaskResponse {
                task_id: task.task_id,
                status: Status::UNHEALTHY,
                result: Vec::new(),
                error: e.to_string(),
            })),
        }
    }

    async fn get_cluster_state(
        &self,
        _request: Request<()>,
    ) -> Result<Response<ClusterState>, Status> {
        let state = self.cluster.get_state().await
            .map_err(|e| Status::internal(e.to_string()))?;
            
        Ok(Response::new(state))
    }
}
```

### 4. 集群管理器实现

```rust
pub struct ClusterManager {
    nodes: Arc<DashMap<String, Node>>,
    metrics: Arc<DashMap<String, HashMap<String, String>>>,
    tasks: Arc<DashMap<String, Task>>,
}

impl ClusterManager {
    pub fn new() -> Self {
        Self {
            nodes: Arc::new(DashMap::new()),
            metrics: Arc::new(DashMap::new()),
            tasks: Arc::new(DashMap::new()),
        }
    }

    pub async fn register_node(&self, node: Node) -> anyhow::Result<RegisterResult> {
        self.nodes.insert(node.node_id.clone(), node);
        
        Ok(RegisterResult {
            cluster_id: "cluster-1".to_string(),
            nodes: self.nodes.iter().map(|n| n.clone()).collect(),
        })
    }

    pub async fn get_node_health(&self, node_id: &str) -> anyhow::Result<Status> {
        self.nodes
            .get(node_id)
            .map(|node| node.status)
            .ok_or_else(|| anyhow::anyhow!("Node not found"))
    }

    pub async fn get_node_metrics(&self, node_id: &str) -> anyhow::Result<HashMap<String, String>> {
        self.metrics
            .get(node_id)
            .map(|m| m.clone())
            .ok_or_else(|| anyhow::anyhow!("Metrics not found"))
    }

    pub async fn get_state(&self) -> anyhow::Result<ClusterState> {
        Ok(ClusterState {
            nodes: self.nodes.iter().map(|n| n.clone()).collect(),
            metrics: self.get_cluster_metrics().await?,
            active_tasks: self.tasks.iter().map(|t| t.clone()).collect(),
        })
    }

    async fn get_cluster_metrics(&self) -> anyhow::Result<HashMap<String, String>> {
        let mut metrics = HashMap::new();
        for node_metrics in self.metrics.iter() {
            metrics.extend(node_metrics.clone());
        }
        Ok(metrics)
    }
}
```

### 5. 任务管理器实现

```rust
pub struct TaskManager {
    tasks: Arc<DashMap<String, TaskInfo>>,
    workers: Arc<WorkerPool>,
}

impl TaskManager {
    pub fn new(num_workers: usize) -> Self {
        Self {
            tasks: Arc::new(DashMap::new()),
            workers: Arc::new(WorkerPool::new(num_workers)),
        }
    }

    pub async fn process_task(&self, request: TaskRequest) -> anyhow::Result<TaskResult> {
        let task = Task {
            task_id: request.task_id.clone(),
            payload: request.payload,
            priority: request.priority,
            metadata: request.metadata,
        };

        // 提交任务到工作者池
        let result = self.workers.submit_task(task).await?;

        Ok(TaskResult {
            task_id: request.task_id,
            result: result.data,
        })
    }
}
```

### 6. 文件管理器实现

```rust
pub struct FileManager {
    storage: Arc<FileStorage>,
}

impl FileManager {
    pub fn new() -> Self {
        Self {
            storage: Arc::new(FileStorage::new()),
        }
    }

    pub async fn process_file_chunks(&self, chunks: Vec<FileChunk>) -> anyhow::Result<String> {
        let file_id = chunks[0].file_id.clone();
        
        // 按顺序处理文件块
        let mut data = Vec::new();
        for chunk in chunks {
            data.extend(chunk.data);
        }

        // 存储文件
        self.storage.store_file(&file_id, data).await?;

        Ok(file_id)
    }
}
```

### 7. 客户端实现

```rust
pub struct DistributedClient {
    client: NodeServiceClient<tonic::transport::Channel>,
}

impl DistributedClient {
    pub async fn connect(addr: &str) -> anyhow::Result<Self> {
        let channel = tonic::transport::Channel::from_shared(addr.to_string())?
            .connect()
            .await?;

        Ok(Self {
            client: NodeServiceClient::new(channel),
        })
    }

    pub async fn register(&mut self, node_id: &str, address: &str) -> anyhow::Result<RegisterResponse> {
        let request = RegisterRequest {
            node_id: node_id.to_string(),
            address: address.to_string(),
            capabilities: vec![],
            metadata: HashMap::new(),
        };

        let response = self.client
            .register(request)
            .await?;

        Ok(response.into_inner())
    }

    pub async fn stream_health_checks(&mut self, node_id: &str) -> anyhow::Result<impl Stream<Item = Result<HealthCheckResponse, Status>>> {
        let request = HealthCheckRequest {
            node_id: node_id.to_string(),
        };

        let response = self.client
            .health_check(request)
            .await?;

        Ok(response.into_inner())
    }

    pub async fn communicate(&mut self, messages: impl Stream<Item = Message>) -> anyhow::Result<impl Stream<Item = Result<Message, Status>>> {
        let response = self.client
            .communicate(Request::new(messages))
            .await?;

        Ok(response.into_inner())
    }

    pub async fn transfer_file(&mut self, file_path: &str) -> anyhow::Result<FileResponse> {
        let file = tokio::fs::File::open(file_path).await?;
        let mut reader = tokio::io::BufReader::new(file);
        let file_id = Uuid::new_v4().to_string();

        let stream = async_stream::stream! {
            let mut buffer = vec![0; 1024];
            let mut chunk_number = 0;

            loop {
                match reader.read(&mut buffer).await {
                    Ok(n) if n > 0 => {
                        yield FileChunk {
                            file_id: file_id.clone(),
                            data: buffer[..n].to_vec(),
                            chunk_number,
                            is_last: false,
                        };
                        chunk_number += 1;
                    }
                    _ => {
                        yield FileChunk {
                            file_id: file_id.clone(),
                            data: vec![],
                            chunk_number,
                            is_last: true,
                        };
                        break;
                    }
                }
            }
        };

        let response = self.client
            .transfer_file(Request::new(stream))
            .await?;

        Ok(response.into_inner())
    }
}
```

### 8. 服务器启动

```rust
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let addr = "[::1]:50051".parse()?;

    let node = DistributedNode::new(
        "node-1".to_string(),
        Arc::new(ClusterManager::new()),
        Arc::new(TaskManager::new(4)),
        Arc::new(FileManager::new()),
    );

    println!("Starting server on {}", addr);

    Server::builder()
        .add_service(NodeServiceServer::new(node))
        .serve(addr)
        .await?;

    Ok(())
}
```

### 9. 中间件实现

```rust
use tower::{Service, Layer};

#[derive(Clone)]
pub struct AuthenticationLayer {
    api_key: String,
}

impl AuthenticationLayer {
    pub fn new(api_key: &str) -> Self {
        Self {
            api_key: api_key.to_string(),
        }
    }
}

impl<S> Layer<S> for AuthenticationLayer {
    type Service = AuthenticationService<S>;

    fn layer(&self, service: S) -> Self::Service {
        AuthenticationService {
            inner: service,
            api_key: self.api_key.clone(),
        }
    }
}

#[derive(Clone)]
pub struct AuthenticationService<S> {
    inner: S,
    api_key: String,
}

impl<S> Service<Request<()>> for AuthenticationService<S>
where
    S: Service<Request<()>>,
{
    type Response = S::Response;
    type Error = S::Error;
    type Future = S::Future;

    fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        self.inner.poll_ready(cx)
    }

    fn call(&mut self, req: Request<()>) -> Self::Future {
        // 验证 API key
        if let Some(api_key) = req.metadata().get("x-api-key") {
            if api_key == self.api_key.as_bytes() {
                return self.inner.call(req);
            }
        }
        
        // 返回未授权错误
        future::ready(Err(Status::unauthenticated("Invalid API key")))
    }
}
```

### 10. 使用示例

```rust
async fn example() -> anyhow::Result<()> {
    // 创建客户端
    let mut client = DistributedClient::connect("http://[::1]:50051").await?;

    // 注册节点
    let register_response = client.register("client-1", "localhost:50052").await?;
    println!("Registered with cluster: {}", register_response.cluster_id);

    // 监控健康状态
    let mut health_stream = client.stream_health_checks("client-1").await?;
    tokio::spawn(async move {
        while let Some(health) = health_stream.next().await {
            match health {
                Ok(response) => println!("Health status: {:?}", response.status),
                Err(e) => eprintln!("Health check error: {}", e),
            }
        }
    });

    // 发送消息
    let messages = async_stream::stream! {
        yield Message {
            from_node: "client-1".to_string(),
            to_node: "node-1".to_string(),
            type_: MessageType::Request as i32,
            payload: b"Hello".to_vec(),
            timestamp: None,
        };
    };

    let mut response_stream = client.communicate(messages).await?;
    while let Some(response) = response_stream.next().await {
        match response {
            Ok(msg) => println!("Received message: {:?}", msg),
            Err(e) => eprintln!("Communication error: {}", e),
        }
    }

    // 传输文件
    let file_response = client.transfer_file("test.txt").await?;
    println!("File transfer result: {}", file_response.success);

    Ok(())
}
```

这个完整的示例展示了如何使用 Tonic 的所有主要特性来构建一个分布式系统，包括：

1. 双向流通信
2. 文件传输
3. 健康检查
4. 服务发现
5. 任务处理
6. 集群状态管理
7. 中间件支持
8. 认证机制
9. 错误处理
10. 指标收集

通过这种方式，您可以构建一个功能完整的分布式系统，支持各种复杂的用例和需求。
