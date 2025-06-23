# Rust 2024 + Tokio + Tonic 实现的分布式 gRPC 组合模式示例

下面是一个使用 Rust 2024 + Tokio + Tonic 实现的分布式 gRPC 组合模式示例：

## 目录

- [Rust 2024 + Tokio + Tonic 实现的分布式 gRPC 组合模式示例](#rust-2024--tokio--tonic-实现的分布式-grpc-组合模式示例)
  - [目录](#目录)
  - [1. 项目依赖配置](#1-项目依赖配置)
  - [2. Proto 定义](#2-proto-定义)
  - [3. 基础组件接口](#3-基础组件接口)
  - [4. 分布式节点实现](#4-分布式节点实现)
  - [5. gRPC 服务实现](#5-grpc-服务实现)
  - [6. 服务发现实现](#6-服务发现实现)
  - [7. 消息代理实现](#7-消息代理实现)
  - [8. 任务调度器实现](#8-任务调度器实现)
  - [9. 使用示例](#9-使用示例)
  - [10. 客户端示例](#10-客户端示例)

## 1. 项目依赖配置

```toml
[dependencies]
tokio = { version = "1.0", features = ["full"] }
tonic = "0.10"
prost = "0.12"
async-trait = "0.1"
futures = "0.3"
anyhow = "1.0"
tracing = "0.1"
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
uuid = { version = "1.0", features = ["v4"] }
dashmap = "5.5"
tower = "0.4"

[build-dependencies]
tonic-build = "0.10"
```

## 2. Proto 定义

```protobuf
// service.proto
syntax = "proto3";
package distributed;

service DistributedService {
    // 服务发现
    rpc Register (RegisterRequest) returns (RegisterResponse);
    rpc Discover (DiscoverRequest) returns (DiscoverResponse);
    
    // 节点通信
    rpc SendMessage (Message) returns (MessageResponse);
    rpc StreamMessages (stream Message) returns (stream Message);
    
    // 任务调度
    rpc SubmitTask (Task) returns (TaskResponse);
    rpc GetTaskStatus (TaskStatusRequest) returns (TaskStatus);
}

message RegisterRequest {
    string node_id = 1;
    string service_name = 2;
    string address = 3;
    map<string, string> metadata = 4;
}

message RegisterResponse {
    bool success = 1;
    string cluster_id = 2;
}

message DiscoverRequest {
    string service_name = 1;
}

message DiscoverResponse {
    repeated Node nodes = 1;
}

message Node {
    string node_id = 1;
    string address = 2;
    map<string, string> metadata = 3;
}

message Message {
    string from_node = 1;
    string to_node = 2;
    bytes payload = 3;
    string message_type = 4;
}

message MessageResponse {
    bool success = 1;
    string message = 2;
}

message Task {
    string task_id = 1;
    string task_type = 2;
    bytes payload = 3;
    map<string, string> metadata = 4;
}

message TaskResponse {
    string task_id = 1;
    bool accepted = 2;
}

message TaskStatusRequest {
    string task_id = 1;
}

message TaskStatus {
    string task_id = 1;
    string status = 2;
    bytes result = 3;
}
```

## 3. 基础组件接口

```rust
use async_trait::async_trait;
use std::sync::Arc;

#[async_trait]
pub trait Component: Send + Sync {
    async fn start(&self) -> anyhow::Result<()>;
    async fn stop(&self) -> anyhow::Result<()>;
    fn get_id(&self) -> &str;
}

#[async_trait]
pub trait ServiceDiscovery: Send + Sync {
    async fn register_service(&self, service: ServiceInfo) -> anyhow::Result<()>;
    async fn discover_service(&self, name: &str) -> anyhow::Result<Vec<ServiceInfo>>;
}

#[async_trait]
pub trait MessageBroker: Send + Sync {
    async fn publish(&self, topic: &str, message: Vec<u8>) -> anyhow::Result<()>;
    async fn subscribe(&self, topic: &str) -> anyhow::Result<tokio::sync::broadcast::Receiver<Vec<u8>>>;
}

#[async_trait]
pub trait TaskScheduler: Send + Sync {
    async fn submit_task(&self, task: Task) -> anyhow::Result<String>;
    async fn get_task_status(&self, task_id: &str) -> anyhow::Result<TaskStatus>;
}
```

## 4. 分布式节点实现

```rust
pub struct DistributedNode {
    id: String,
    address: String,
    components: Arc<DashMap<String, Box<dyn Component>>>,
    service_discovery: Arc<dyn ServiceDiscovery>,
    message_broker: Arc<dyn MessageBroker>,
    task_scheduler: Arc<dyn TaskScheduler>,
    grpc_server: Option<tonic::transport::Server>,
}

impl DistributedNode {
    pub async fn new(
        id: &str,
        address: &str,
        service_discovery: Arc<dyn ServiceDiscovery>,
        message_broker: Arc<dyn MessageBroker>,
        task_scheduler: Arc<dyn TaskScheduler>,
    ) -> anyhow::Result<Self> {
        Ok(Self {
            id: id.to_string(),
            address: address.to_string(),
            components: Arc::new(DashMap::new()),
            service_discovery,
            message_broker,
            task_scheduler,
            grpc_server: None,
        })
    }

    pub async fn start(&mut self) -> anyhow::Result<()> {
        // 启动 gRPC 服务器
        let service = DistributedServiceImpl {
            node_id: self.id.clone(),
            service_discovery: self.service_discovery.clone(),
            message_broker: self.message_broker.clone(),
            task_scheduler: self.task_scheduler.clone(),
        };

        let server = tonic::transport::Server::builder()
            .add_service(DistributedServiceServer::new(service))
            .serve(self.address.parse()?);

        self.grpc_server = Some(server);

        // 注册服务
        self.service_discovery.register_service(ServiceInfo {
            id: self.id.clone(),
            name: "distributed_node".to_string(),
            address: self.address.clone(),
            metadata: Default::default(),
        }).await?;

        // 启动所有组件
        for component in self.components.iter() {
            component.value().start().await?;
        }

        Ok(())
    }

    pub async fn stop(&self) -> anyhow::Result<()> {
        // 停止所有组件
        for component in self.components.iter() {
            component.value().stop().await?;
        }

        Ok(())
    }

    pub fn add_component(&self, component: Box<dyn Component>) {
        self.components.insert(component.get_id().to_string(), component);
    }
}
```

## 5. gRPC 服务实现

```rust
pub struct DistributedServiceImpl {
    node_id: String,
    service_discovery: Arc<dyn ServiceDiscovery>,
    message_broker: Arc<dyn MessageBroker>,
    task_scheduler: Arc<dyn TaskScheduler>,
}

#[tonic::async_trait]
impl DistributedService for DistributedServiceImpl {
    async fn register(
        &self,
        request: Request<RegisterRequest>,
    ) -> Result<Response<RegisterResponse>, Status> {
        let req = request.into_inner();
        
        self.service_discovery.register_service(ServiceInfo {
            id: req.node_id,
            name: req.service_name,
            address: req.address,
            metadata: req.metadata,
        }).await.map_err(|e| Status::internal(e.to_string()))?;

        Ok(Response::new(RegisterResponse {
            success: true,
            cluster_id: "cluster-1".to_string(),
        }))
    }

    async fn discover(
        &self,
        request: Request<DiscoverRequest>,
    ) -> Result<Response<DiscoverResponse>, Status> {
        let req = request.into_inner();
        
        let services = self.service_discovery
            .discover_service(&req.service_name)
            .await
            .map_err(|e| Status::internal(e.to_string()))?;

        let nodes = services.into_iter()
            .map(|s| Node {
                node_id: s.id,
                address: s.address,
                metadata: s.metadata,
            })
            .collect();

        Ok(Response::new(DiscoverResponse { nodes }))
    }

    async fn send_message(
        &self,
        request: Request<Message>,
    ) -> Result<Response<MessageResponse>, Status> {
        let msg = request.into_inner();
        
        self.message_broker
            .publish(&msg.to_node, msg.payload)
            .await
            .map_err(|e| Status::internal(e.to_string()))?;

        Ok(Response::new(MessageResponse {
            success: true,
            message: "Message sent".to_string(),
        }))
    }

    type StreamMessagesStream = Pin<Box<dyn Stream<Item = Result<Message, Status>> + Send + 'static>>;

    async fn stream_messages(
        &self,
        request: Request<tonic::Streaming<Message>>,
    ) -> Result<Response<Self::StreamMessagesStream>, Status> {
        let mut stream = request.into_inner();
        let message_broker = self.message_broker.clone();
        let node_id = self.node_id.clone();

        let output = async_stream::try_stream! {
            while let Some(msg) = stream.next().await {
                let msg = msg?;
                
                // 处理接收到的消息
                message_broker
                    .publish(&msg.to_node, msg.payload.clone())
                    .await
                    .map_err(|e| Status::internal(e.to_string()))?;

                // 发送响应消息
                yield Message {
                    from_node: node_id.clone(),
                    to_node: msg.from_node,
                    payload: msg.payload,
                    message_type: "response".to_string(),
                };
            }
        };

        Ok(Response::new(Box::pin(output)))
    }

    async fn submit_task(
        &self,
        request: Request<Task>,
    ) -> Result<Response<TaskResponse>, Status> {
        let task = request.into_inner();
        
        let task_id = self.task_scheduler
            .submit_task(task)
            .await
            .map_err(|e| Status::internal(e.to_string()))?;

        Ok(Response::new(TaskResponse {
            task_id,
            accepted: true,
        }))
    }

    async fn get_task_status(
        &self,
        request: Request<TaskStatusRequest>,
    ) -> Result<Response<TaskStatus>, Status> {
        let req = request.into_inner();
        
        let status = self.task_scheduler
            .get_task_status(&req.task_id)
            .await
            .map_err(|e| Status::internal(e.to_string()))?;

        Ok(Response::new(status))
    }
}
```

## 6. 服务发现实现

```rust
pub struct EtcdServiceDiscovery {
    client: etcd_client::Client,
    prefix: String,
}

impl EtcdServiceDiscovery {
    pub async fn new(endpoints: &[&str], prefix: &str) -> anyhow::Result<Self> {
        let client = etcd_client::Client::connect(endpoints).await?;
        
        Ok(Self {
            client,
            prefix: prefix.to_string(),
        })
    }

    fn service_key(&self, service: &ServiceInfo) -> String {
        format!("{}/{}/{}", self.prefix, service.name, service.id)
    }
}

#[async_trait]
impl ServiceDiscovery for EtcdServiceDiscovery {
    async fn register_service(&self, service: ServiceInfo) -> anyhow::Result<()> {
        let key = self.service_key(&service);
        let value = serde_json::to_string(&service)?;
        
        self.client
            .put(key, value, Some(etcd_client::PutOptions::new().with_lease(60)))
            .await?;
            
        Ok(())
    }

    async fn discover_service(&self, name: &str) -> anyhow::Result<Vec<ServiceInfo>> {
        let prefix = format!("{}/{}", self.prefix, name);
        let response = self.client.get(prefix, Some(etcd_client::GetOptions::new().with_prefix())).await?;
        
        let services = response.kvs().iter()
            .filter_map(|kv| serde_json::from_slice::<ServiceInfo>(kv.value()).ok())
            .collect();
            
        Ok(services)
    }
}
```

## 7. 消息代理实现

```rust
pub struct RedisBroker {
    client: redis::Client,
    subscribers: Arc<DashMap<String, broadcast::Sender<Vec<u8>>>>,
}

impl RedisBroker {
    pub async fn new(redis_url: &str) -> anyhow::Result<Self> {
        let client = redis::Client::open(redis_url)?;
        
        Ok(Self {
            client,
            subscribers: Arc::new(DashMap::new()),
        })
    }

    async fn start_subscriber(&self, topic: String) -> anyhow::Result<()> {
        let mut pubsub = self.client.get_async_connection().await?.into_pubsub();
        pubsub.subscribe(topic.clone()).await?;
        
        let subscribers = self.subscribers.clone();
        
        tokio::spawn(async move {
            while let Some(msg) = pubsub.on_message().next().await {
                if let Ok(payload) = msg.get_payload::<Vec<u8>>() {
                    if let Some(sender) = subscribers.get(&topic) {
                        let _ = sender.send(payload);
                    }
                }
            }
        });

        Ok(())
    }
}

#[async_trait]
impl MessageBroker for RedisBroker {
    async fn publish(&self, topic: &str, message: Vec<u8>) -> anyhow::Result<()> {
        let mut conn = self.client.get_async_connection().await?;
        conn.publish(topic, message).await?;
        Ok(())
    }

    async fn subscribe(&self, topic: &str) -> anyhow::Result<broadcast::Receiver<Vec<u8>>> {
        let (tx, rx) = broadcast::channel(100);
        
        self.subscribers.entry(topic.to_string())
            .or_insert_with(|| {
                let _ = self.start_subscriber(topic.to_string());
                tx
            });
            
        Ok(rx)
    }
}
```

## 8. 任务调度器实现

```rust
pub struct DistributedTaskScheduler {
    tasks: Arc<DashMap<String, TaskInfo>>,
    workers: Arc<DashMap<String, WorkerInfo>>,
    message_broker: Arc<dyn MessageBroker>,
}

impl DistributedTaskScheduler {
    pub fn new(message_broker: Arc<dyn MessageBroker>) -> Self {
        Self {
            tasks: Arc::new(DashMap::new()),
            workers: Arc::new(DashMap::new()),
            message_broker,
        }
    }

    async fn assign_task(&self, task: Task) -> anyhow::Result<String> {
        let task_id = Uuid::new_v4().to_string();
        
        // 选择合适的worker
        let worker = self.select_worker(&task)?;
        
        // 发送任务到worker
        self.message_broker
            .publish(&format!("worker/{}", worker.id), 
                    serde_json::to_vec(&task)?)
            .await?;
            
        // 记录任务信息
        self.tasks.insert(task_id.clone(), TaskInfo {
            id: task_id.clone(),
            worker_id: worker.id.clone(),
            status: TaskStatus::Pending,
            created_at: chrono::Utc::now(),
        });
        
        Ok(task_id)
    }

    fn select_worker(&self, task: &Task) -> anyhow::Result<WorkerInfo> {
        // 实现worker选择逻辑
        self.workers
            .iter()
            .find(|w| w.can_handle_task(task))
            .map(|w| w.clone())
            .ok_or_else(|| anyhow::anyhow!("No available worker"))
    }
}

#[async_trait]
impl TaskScheduler for DistributedTaskScheduler {
    async fn submit_task(&self, task: Task) -> anyhow::Result<String> {
        self.assign_task(task).await
    }

    async fn get_task_status(&self, task_id: &str) -> anyhow::Result<TaskStatus> {
        self.tasks
            .get(task_id)
            .map(|t| t.status.clone())
            .ok_or_else(|| anyhow::anyhow!("Task not found"))
    }
}
```

## 9. 使用示例

```rust
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 初始化服务发现
    let service_discovery = Arc::new(EtcdServiceDiscovery::new(
        &["localhost:2379"],
        "/services",
    ).await?);

    // 初始化消息代理
    let message_broker = Arc::new(RedisBroker::new(
        "redis://localhost:6379",
    ).await?);

    // 初始化任务调度器
    let task_scheduler = Arc::new(DistributedTaskScheduler::new(
        message_broker.clone(),
    ));

    // 创建分布式节点
    let mut node = DistributedNode::new(
        "node-1",
        "127.0.0.1:50051",
        service_discovery.clone(),
        message_broker.clone(),
        task_scheduler.clone(),
    ).await?;

    // 添加自定义组件
    node.add_component(Box::new(CustomComponent::new("custom-1")));

    // 启动节点
    node.start().await?;

    // 等待终止信号
    tokio::signal::ctrl_c().await?;

    // 停止节点
    node.stop().await?;

    Ok(())
}
```

## 10. 客户端示例

```rust
pub struct DistributedClient {
    client: DistributedServiceClient<tonic::transport::Channel>,
}

impl DistributedClient {
    pub async fn connect(addr: &str) -> anyhow::Result<Self> {
        let client = DistributedServiceClient::connect(addr.to_string()).await?;
        
        Ok(Self { client })
    }

    pub async fn submit_task(&mut self, task: Task) -> anyhow::Result<String> {
        let response = self.client
            .submit_task(task)
            .await?;
            
        Ok(response.into_inner().task_id)
    }

    pub async fn stream_messages(
        &mut self,
        messages: impl Stream<Item = Message>,
    ) -> anyhow::Result<impl Stream<Item = Result<Message, Status>>> {
        let response = self.client
            .stream_messages(Request::new(messages))
            .await?;
            
        Ok(response.into_inner())
    }
}

// 使用示例
async fn example_client() -> anyhow::Result<()> {
    let mut client = DistributedClient::connect("http://localhost:50051").await?;

    // 提交任务
    let task_id = client.submit_task(Task {
        task_type: "example".to_string(),
        payload: vec![],
        metadata: Default::default(),
    }).await?;

    // 流式消息处理
    let messages = async_stream::stream! {
        yield Message {
            from_node: "client".to_string(),
            to_node: "node-1".to_string(),
            payload: vec![],
            message_type: "request".to_string(),
        };
    };

    let mut response_stream = client.stream_messages(messages).await?;
    while let Some(message) = response_stream.next().await {
        println!("Received message: {:?}", message);
    }

    Ok(())
}
```

这个完整的示例展示了如何：

1. 使用 gRPC 实现分布式服务
2. 实现服务发现机制
3. 实现消息代理
4. 实现分布式任务调度
5. 使用组合模式组织组件
6. 处理流式通信
7. 实现客户端功能

通过这种方式，您可以构建一个完整的分布式系统，支持：

- 服务注册与发现
- 节点间通信
- 任务调度
- 流式处理
- 可扩展的组件架构

这个实现提供了良好的可扩展性和灵活性，可以根据需要添加更多功能和组件。
