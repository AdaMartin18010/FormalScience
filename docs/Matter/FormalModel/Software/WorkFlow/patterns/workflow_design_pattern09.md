# 复杂分布式系统架构设计与实现方案

## 📋 目录

- [1 一、整体架构设计](#1-一整体架构设计)
  - [1.1 系统架构概览](#11-系统架构概览)
  - [1.2 核心层次与组件](#12-核心层次与组件)
    - [2.2.1 应用层](#221-应用层)
    - [2.2.2 领域层](#222-领域层)
    - [2.2.3 基础设施层](#223-基础设施层)
- [2 二、子系统详细设计](#2-二子系统详细设计)
  - [2.1 命令处理子系统](#21-命令处理子系统)
    - [1.1.1 命令处理流程](#111-命令处理流程)
    - [1.1.2 代表性命令处理器实现](#112-代表性命令处理器实现)
  - [2.2 事件处理子系统](#22-事件处理子系统)
    - [2.2.1 事件总线实现](#221-事件总线实现)
    - [2.2.2 订单创建事件处理](#222-订单创建事件处理)
  - [2.3 工作流子系统](#23-工作流子系统)
    - [3.3.1 Temporal工作流集成](#331-temporal工作流集成)
    - [3.3.2 工作流活动实现](#332-工作流活动实现)
  - [2.4 外部系统集成子系统](#24-外部系统集成子系统)
    - [4.4.1 抽象服务客户端](#441-抽象服务客户端)
  - [2.5 外部系统集成子系统续](#25-外部系统集成子系统续)
    - [5.5.1 抽象服务客户端续](#551-抽象服务客户端续)
    - [5.5.2 外部系统适配器工厂](#552-外部系统适配器工厂)
  - [2.6 查询服务子系统](#26-查询服务子系统)
    - [6.6.1 CQRS查询层](#661-cqrs查询层)
    - [6.6.2 API端点](#662-api端点)
  - [2.7 监控与可观测性子系统](#27-监控与可观测性子系统)
    - [7.7.1 分布式追踪集成](#771-分布式追踪集成)
    - [7.7.2 指标监控实现](#772-指标监控实现)
  - [2.8 监控与可观测性子系统续](#28-监控与可观测性子系统续)
    - [8.8.1 指标监控实现续](#881-指标监控实现续)
  - [2.9 配置与服务发现子系统](#29-配置与服务发现子系统)
    - [9.9.1 动态配置管理](#991-动态配置管理)
    - [9.9.2 服务注册与发现](#992-服务注册与发现)
- [3 三、数据模型设计](#3-三数据模型设计)
  - [3.1 事件存储表结构](#31-事件存储表结构)
  - [3.2 读模型表结构](#32-读模型表结构)
- [4 四、部署架构](#4-四部署架构)
  - [4.1 容器化与服务编排](#41-容器化与服务编排)
- [5 四、部署架构续](#5-四部署架构续)
  - [5.1 容器化与服务编排续](#51-容器化与服务编排续)
  - [5.2 Prometheus配置](#52-prometheus配置)
  - [5.3 Kubernetes部署配置](#53-kubernetes部署配置)
- [6 五、系统启动与集成](#6-五系统启动与集成)
  - [6.1 应用启动序列](#61-应用启动序列)
  - [6.2 Dockerfile](#62-dockerfile)
- [7 六、总结与最佳实践](#7-六总结与最佳实践)
  - [7.1 架构设计关键点](#71-架构设计关键点)
  - [7.2 Rust实现优势](#72-rust实现优势)
  - [7.3 集成开源库最佳实践](#73-集成开源库最佳实践)
  - [7.4 最终架构特点](#74-最终架构特点)

---

## 1 一、整体架构设计

基于前面的分析,我们设计一个可满足您需求的分布式系统架构,采用领域驱动设计和微服务架构,结合事件驱动和CQRS模式。

### 1.1 系统架构概览

![系统架构图](架构设计)

```text
+-----------------------------------------------------+
|                   前端应用层                          |
+-----------------------------------------------------+
                        ↓
+-----------------------------------------------------+
|                 API网关 (actix-web)                  |
+-----------------------------------------------------+
            ↙          ↓           ↘
+---------------+ +---------------+ +---------------+
|  命令服务      | |   查询服务     | |   集成服务     |
| (处理写操作)   | | (处理读操作)   | | (外部系统集成)  |
+---------------+ +---------------+ +---------------+
      ↓    ↑                ↑               ↑   ↓
+---------------+           |               |   |
|  事件总线      |-----------|---------------|---|
| (rdkafka)     |                                   
+---------------+                               
      ↓                                    ↓   ↑
+---------------+                     +---------------+
|  工作流引擎    |                     |  外部系统适配器 |
| (temporal)    |                     | (tonic clients)|
+---------------+                     +---------------+
      ↓    ↑                                ↓   ↑
+---------------+ +---------------+ +---------------+
|  事件存储      | |   读模型存储   | |   集成存储     |
| (sqlx+Postgres)| | (sqlx+MongoDB) | | (redis-rs)    |
+---------------+ +---------------+ +---------------+
```

### 1.2 核心层次与组件

#### 2.2.1 应用层

- **API网关**: 使用actix-web实现,处理认证、授权、路由、限流
- **命令服务**: 处理写操作,验证、转换命令为领域事件
- **查询服务**: 处理读操作,从优化的读模型中获取数据
- **集成服务**: 管理与外部系统的交互

#### 2.2.2 领域层

- **聚合根**: 业务实体和规则的封装
- **领域事件**: 系统中发生的重要变化
- **工作流引擎**: 管理长时间运行的业务流程
- **领域服务**: 跨聚合根的业务逻辑

#### 2.2.3 基础设施层

- **事件总线**: 使用rdkafka实现的发布/订阅机制
- **事件存储**: 使用PostgreSQL存储领域事件
- **读模型存储**: 使用MongoDB存储优化的读模型
- **集成存储**: 使用Redis缓存集成数据

## 2 二、子系统详细设计

### 2.1 命令处理子系统

#### 1.1.1 命令处理流程

```rust
use tokio::sync::mpsc;
use serde::{Serialize, Deserialize};
use uuid::Uuid;
use chrono::{DateTime, Utc};
use tracing::{info, error, instrument};

/// 命令特质
pub trait Command: Send + Sync + 'static {
    /// 命令类型标识
    fn command_type(&self) -> &'static str;
    
    /// 命令唯一标识
    fn command_id(&self) -> Uuid;
    
    /// 用于追踪的相关ID
    fn correlation_id(&self) -> Option<String>;
}

/// 命令处理器特质
#[async_trait]
pub trait CommandHandler<C: Command>: Send + Sync + 'static {
    /// 处理命令
    async fn handle(&self, command: C) -> Result<Vec<DomainEvent>, CommandError>;
}

/// 命令总线
pub struct CommandBus {
    handlers: HashMap<&'static str, Box<dyn AnyCommandHandler>>,
    event_producer: Arc<EventProducer>,
}

#[async_trait]
pub trait AnyCommandHandler: Send + Sync {
    async fn handle_any(&self, command: Box<dyn Command>) -> Result<Vec<DomainEvent>, CommandError>;
}

impl CommandBus {
    pub fn new(event_producer: Arc<EventProducer>) -> Self {
        Self {
            handlers: HashMap::new(),
            event_producer,
        }
    }
    
    /// 注册命令处理器
    pub fn register<C, H>(&mut self, handler: H)
    where
        C: Command + 'static,
        H: CommandHandler<C> + 'static,
    {
        let type_id = TypeId::of::<C>();
        let handler_wrapper = CommandHandlerWrapper { handler };
        self.handlers.insert(type_id, Box::new(handler_wrapper));
    }
    
    /// 分派命令
    #[instrument(skip(self), fields(command_id = %command.command_id(), command_type = %command.command_type()))]
    pub async fn dispatch<C: Command>(&self, command: C) -> Result<Vec<DomainEvent>, CommandError> {
        info!("处理命令");
        
        let type_id = TypeId::of::<C>();
        
        let handler = self.handlers.get(&type_id)
            .ok_or_else(|| CommandError::HandlerNotFound(command.command_type().to_string()))?;
            
        // 处理命令
        let events = handler.handle_any(Box::new(command)).await?;
        
        // 发布事件
        for event in &events {
            self.event_producer.publish_event(event).await?;
        }
        
        Ok(events)
    }
}
```

#### 1.1.2 代表性命令处理器实现

```rust
use sqlx::{PgPool, postgres::PgQueryResult};
use uuid::Uuid;
use serde::{Serialize, Deserialize};

/// 创建订单命令
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CreateOrderCommand {
    pub command_id: Uuid,
    pub customer_id: String,
    pub items: Vec<OrderItem>,
    pub shipping_address: Address,
    pub correlation_id: Option<String>,
}

impl Command for CreateOrderCommand {
    fn command_type(&self) -> &'static str { "create_order" }
    fn command_id(&self) -> Uuid { self.command_id }
    fn correlation_id(&self) -> Option<String> { self.correlation_id.clone() }
}

/// 创建订单处理器
pub struct CreateOrderHandler {
    db_pool: PgPool,
    inventory_client: Arc<InventoryServiceClient>,
}

#[async_trait]
impl CommandHandler<CreateOrderCommand> for CreateOrderHandler {
    #[instrument(skip(self), fields(command_id = %command.command_id))]
    async fn handle(&self, command: CreateOrderCommand) -> Result<Vec<DomainEvent>, CommandError> {
        // 1. 验证库存可用性
        let inventory_check = self.inventory_client.check_availability(&command.items).await
            .map_err(|e| CommandError::ValidationError(format!("库存检查失败: {}", e)))?;
            
        if !inventory_check.all_available {
            return Err(CommandError::ValidationError(
                format!("部分商品库存不足: {:?}", inventory_check.unavailable_items)
            ));
        }
        
        // 2. 创建订单聚合根
        let order = Order::create(
            OrderId::new(),
            CustomerId::from(command.customer_id),
            command.items,
            command.shipping_address,
        )?;
        
        // 3. 将订单保存到事件存储
        let events = order.uncommitted_events();
        
        // 使用事务保存事件
        let mut tx = self.db_pool.begin().await
            .map_err(|e| CommandError::InfrastructureError(e.to_string()))?;
            
        for event in &events {
            sqlx::query(
                "INSERT INTO event_store (aggregate_id, aggregate_type, event_type, event_data, sequence, occurred_at)
                 VALUES ($1, $2, $3, $4, $5, $6)"
            )
            .bind(event.aggregate_id().to_string())
            .bind("order")
            .bind(event.event_type())
            .bind(serde_json::to_value(event).map_err(|e| CommandError::SerializationError(e.to_string()))?)
            .bind(event.sequence() as i32)
            .bind(event.occurred_at())
            .execute(&mut tx)
            .await
            .map_err(|e| CommandError::InfrastructureError(format!("事件保存失败: {}", e)))?;
        }
        
        tx.commit().await
            .map_err(|e| CommandError::InfrastructureError(format!("事务提交失败: {}", e)))?;
            
        info!(order_id = %order.id(), "订单创建成功");
        
        Ok(events)
    }
}
```

### 2.2 事件处理子系统

#### 2.2.1 事件总线实现

```rust
use rdkafka::producer::{FutureProducer, FutureRecord};
use rdkafka::config::ClientConfig;
use rdkafka::message::OwnedHeaders;
use std::time::Duration;

/// 领域事件特质
pub trait DomainEvent: Send + Sync + 'static {
    fn event_type(&self) -> &'static str;
    fn aggregate_id(&self) -> &str;
    fn sequence(&self) -> u64;
    fn occurred_at(&self) -> DateTime<Utc>;
}

/// 事件生产者
pub struct EventProducer {
    producer: FutureProducer,
    topic: String,
}

impl EventProducer {
    pub fn new(brokers: &str, topic: &str) -> Result<Self, rdkafka::error::KafkaError> {
        let producer = ClientConfig::new()
            .set("bootstrap.servers", brokers)
            .set("message.timeout.ms", "5000")
            .create()?;
            
        Ok(Self {
            producer,
            topic: topic.to_string(),
        })
    }
    
    #[instrument(skip(self, event), fields(event_type = %event.event_type(), aggregate_id = %event.aggregate_id()))]
    pub async fn publish_event<E: DomainEvent + Serialize>(&self, event: &E) -> Result<(), EventBusError> {
        let event_data = serde_json::to_string(event)
            .map_err(|e| EventBusError::SerializationError(e.to_string()))?;
            
        let headers = OwnedHeaders::new()
            .add("event_type", event.event_type())
            .add("aggregate_id", event.aggregate_id())
            .add("sequence", &event.sequence().to_string())
            .add("occurred_at", &event.occurred_at().to_rfc3339());
            
        let delivery_status = self.producer
            .send(
                FutureRecord::to(&self.topic)
                    .payload(&event_data)
                    .key(event.aggregate_id())
                    .headers(headers),
                Duration::from_secs(5),
            )
            .await
            .map_err(|(e, _)| EventBusError::PublishError(e.to_string()))?;
            
        info!(
            offset = delivery_status.0,
            partition = delivery_status.1,
            "事件已发布"
        );
        
        Ok(())
    }
}

/// 事件消费者
pub struct EventConsumer {
    consumer: StreamConsumer,
    event_handlers: HashMap<&'static str, Vec<Box<dyn AnyEventHandler>>>,
}

#[async_trait]
pub trait EventHandler<E: DomainEvent>: Send + Sync + 'static {
    async fn handle(&self, event: E) -> Result<(), EventHandlerError>;
}

#[async_trait]
pub trait AnyEventHandler: Send + Sync {
    async fn handle_any(&self, event_type: &str, event_data: &str) -> Result<(), EventHandlerError>;
}

impl EventConsumer {
    pub async fn start(
        &self,
        topics: &[&str],
        group_id: &str,
        brokers: &str,
    ) -> Result<(), EventConsumerError> {
        let consumer: StreamConsumer = ClientConfig::new()
            .set("group.id", group_id)
            .set("bootstrap.servers", brokers)
            .set("enable.auto.commit", "false")
            .set("auto.offset.reset", "earliest")
            .create()?
            .subscribe(topics)?;
            
        let mut message_stream = consumer.stream();
        
        while let Some(message) = message_stream.next().await {
            match message {
                Ok(msg) => {
                    let payload = match msg.payload_view::<str>() {
                        Some(Ok(s)) => s,
                        Some(Err(e)) => {
                            error!("消息解析失败: {:?}", e);
                            continue;
                        }
                        None => {
                            error!("空消息");
                            continue;
                        }
                    };
                    
                    let event_type = match msg.headers() {
                        Some(headers) => {
                            match headers.get(0) {
                                Some(header) if header.key == "event_type" => {
                                    match std::str::from_utf8(header.value.unwrap_or_default()) {
                                        Ok(s) => s,
                                        Err(_) => {
                                            error!("无法解析事件类型");
                                            continue;
                                        }
                                    }
                                }
                                _ => {
                                    error!("消息中缺少事件类型");
                                    continue;
                                }
                            }
                        }
                        None => {
                            error!("消息中缺少头信息");
                            continue;
                        }
                    };
                    
                    if let Some(handlers) = self.event_handlers.get(event_type) {
                        for handler in handlers {
                            if let Err(e) = handler.handle_any(event_type, payload).await {
                                error!(error = ?e, "事件处理失败");
                            }
                        }
                    }
                    
                    consumer.commit_message(&msg, CommitMode::Async).unwrap();
                }
                Err(e) => {
                    error!("消费消息错误: {:?}", e);
                }
            }
        }
        
        Ok(())
    }
}
```

#### 2.2.2 订单创建事件处理

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OrderCreatedEvent {
    pub event_id: Uuid,
    pub aggregate_id: String,
    pub sequence: u64,
    pub occurred_at: DateTime<Utc>,
    pub customer_id: String,
    pub order_items: Vec<OrderItem>,
    pub shipping_address: Address,
    pub order_status: OrderStatus,
}

impl DomainEvent for OrderCreatedEvent {
    fn event_type(&self) -> &'static str { "order_created" }
    fn aggregate_id(&self) -> &str { &self.aggregate_id }
    fn sequence(&self) -> u64 { self.sequence }
    fn occurred_at(&self) -> DateTime<Utc> { self.occurred_at }
}

/// 订单查询模型更新器
pub struct OrderReadModelUpdater {
    db_pool: sqlx::PgPool,
}

#[async_trait]
impl EventHandler<OrderCreatedEvent> for OrderReadModelUpdater {
    #[instrument(skip(self, event), fields(order_id = %event.aggregate_id))]
    async fn handle(&self, event: OrderCreatedEvent) -> Result<(), EventHandlerError> {
        // 更新订单查询模型
        let result = sqlx::query(
            "INSERT INTO order_view (
                id, customer_id, status, total_amount, item_count, shipping_address, created_at
            ) VALUES ($1, $2, $3, $4, $5, $6, $7)"
        )
        .bind(&event.aggregate_id)
        .bind(&event.customer_id)
        .bind(event.order_status.to_string())
        .bind(calculate_total_amount(&event.order_items))
        .bind(event.order_items.len() as i32)
        .bind(serde_json::to_value(&event.shipping_address).map_err(|e| EventHandlerError::SerializationError(e.to_string()))?)
        .bind(event.occurred_at)
        .execute(&self.db_pool)
        .await
        .map_err(|e| EventHandlerError::DatabaseError(e.to_string()))?;
        
        // 插入订单项
        for item in &event.order_items {
            sqlx::query(
                "INSERT INTO order_item_view (
                    order_id, product_id, quantity, unit_price
                ) VALUES ($1, $2, $3, $4)"
            )
            .bind(&event.aggregate_id)
            .bind(&item.product_id)
            .bind(item.quantity as i32)
            .bind(item.unit_price)
            .execute(&self.db_pool)
            .await
            .map_err(|e| EventHandlerError::DatabaseError(e.to_string()))?;
        }
        
        info!("已更新订单查询模型");
        Ok(())
    }
}

/// 工作流启动处理器
pub struct OrderWorkflowStarter {
    temporal_client: Arc<TemporalClient>,
}

#[async_trait]
impl EventHandler<OrderCreatedEvent> for OrderWorkflowStarter {
    #[instrument(skip(self, event), fields(order_id = %event.aggregate_id))]
    async fn handle(&self, event: OrderCreatedEvent) -> Result<(), EventHandlerError> {
        // 启动订单处理工作流
        let workflow_input = OrderProcessingWorkflowInput {
            order_id: event.aggregate_id.clone(),
            customer_id: event.customer_id.clone(),
        };
        
        let workflow_id = format!("order-processing-{}", event.aggregate_id);
        
        self.temporal_client.start_workflow(
            "OrderProcessingWorkflow",
            workflow_input,
            &workflow_id,
            &WorkflowOptions {
                task_queue: "order-processing".to_string(),
                workflow_execution_timeout: Some(Duration::from_secs(86400)), // 24小时
                ..Default::default()
            },
        ).await.map_err(|e| EventHandlerError::WorkflowError(e.to_string()))?;
        
        info!(workflow_id = %workflow_id, "已启动订单处理工作流");
        Ok(())
    }
}

/// 库存预留处理器
pub struct InventoryReserver {
    inventory_client: Arc<InventoryServiceClient>,
}

#[async_trait]
impl EventHandler<OrderCreatedEvent> for InventoryReserver {
    #[instrument(skip(self, event), fields(order_id = %event.aggregate_id))]
    async fn handle(&self, event: OrderCreatedEvent) -> Result<(), EventHandlerError> {
        // 预留库存
        let reserve_request = ReserveInventoryRequest {
            order_id: event.aggregate_id.clone(),
            items: event.order_items.iter().map(|item| InventoryItem {
                product_id: item.product_id.clone(),
                quantity: item.quantity,
            }).collect(),
        };
        
        match self.inventory_client.reserve_inventory(reserve_request).await {
            Ok(_) => {
                info!("库存预留成功");
                Ok(())
            },
            Err(e) => {
                error!(error = %e, "库存预留失败");
                Err(EventHandlerError::ExternalServiceError(format!("库存预留失败: {}", e)))
            }
        }
    }
}
```

### 2.3 工作流子系统

#### 3.3.1 Temporal工作流集成

```rust
use temporal_sdk::{WfContext, WfExitValue, WorkflowResult, ActivityOptions};
use temporal_sdk_core_protos::coresdk::workflow_commands::workflow_command::Variant;
use std::time::Duration;
use serde::{Serialize, Deserialize};
use uuid::Uuid;

/// 订单处理工作流输入
#[derive(Clone, Serialize, Deserialize)]
pub struct OrderProcessingWorkflowInput {
    pub order_id: String,
    pub customer_id: String,
}

/// 订单处理工作流
#[temporal_sdk::workflow]
pub async fn order_processing_workflow(ctx: WfContext, input: OrderProcessingWorkflowInput) -> WorkflowResult<String> {
    // 设置工作流超时
    ctx.set_workflow_timeout(std::time::Duration::from_hours(24));
    
    // 1. 验证订单
    let validate_result = ctx.activity("validate_order")
        .options(ActivityOptions {
            start_to_close_timeout: Some(Duration::from_secs(30)),
            retry_policy: Some(RetryPolicy {
                initial_interval: Duration::from_secs(1),
                backoff_coefficient: 2.0,
                maximum_interval: Duration::from_secs(100),
                maximum_attempts: 3,
                ..Default::default()
            }),
            ..Default::default()
        })
        .args(input.order_id.clone())
        .run::<ValidateOrderResult>()
        .await?;
        
    if !validate_result.is_valid {
        return Ok(WfExitValue::Normal(format!("订单 {} 验证失败: {}", input.order_id, validate_result.reason.unwrap_or_default())));
    }
    
    // 2. 处理支付
    let payment_result = ctx.activity("process_payment")
        .options(ActivityOptions {
            start_to_close_timeout: Some(Duration::from_secs(60)),
            retry_policy: Some(RetryPolicy {
                initial_interval: Duration::from_secs(1),
                backoff_coefficient: 2.0,
                maximum_interval: Duration::from_secs(100),
                maximum_attempts: 5,
                non_retryable_error_types: vec!["PaymentDeclined".to_string()],
                ..Default::default()
            }),
            ..Default::default()
        })
        .args(ProcessPaymentInput {
            order_id: input.order_id.clone(),
            customer_id: input.customer_id.clone(),
        })
        .run::<ProcessPaymentResult>()
        .await?;
        
    if payment_result.status != "completed" {
        // 支付失败,释放库存
        ctx.activity("release_inventory")
            .args(input.order_id.clone())
            .run::<()>()
            .await?;
            
        return Ok(WfExitValue::Normal(format!("订单 {} 支付失败: {}", 
            input.order_id, 
            payment_result.failure_reason.unwrap_or_default()
        )));
    }
    
    // 3. 创建配送单
    let shipment_result = ctx.activity("create_shipment")
        .args(CreateShipmentInput {
            order_id: input.order_id.clone(),
        })
        .run::<CreateShipmentResult>()
        .await?;
        
    // 4. 发送订单确认通知
    ctx.activity("send_order_confirmation")
        .args(SendOrderConfirmationInput {
            order_id: input.order_id.clone(),
            customer_id: input.customer_id.clone(),
            shipment_id: shipment_result.shipment_id,
            estimated_delivery: shipment_result.estimated_delivery,
        })
        .run::<()>()
        .await?;
        
    Ok(WfExitValue::Normal(format!("订单 {} 处理完成", input.order_id)))
}
```

#### 3.3.2 工作流活动实现

```rust
use temporal_sdk::{ActivityContext, ActivityResult};
use serde::{Serialize, Deserialize};
use chrono::{DateTime, Utc};
use uuid::Uuid;
use sqlx::PgPool;

/// 验证订单活动
#[derive(Serialize, Deserialize)]
pub struct ValidateOrderResult {
    pub is_valid: bool,
    pub reason: Option<String>,
}

#[temporal_sdk::activity]
pub async fn validate_order(ctx: ActivityContext, order_id: String) -> ActivityResult<ValidateOrderResult> {
    let tracer = global::tracer("validate_order");
    let span = tracer.start_with_context("validate_order", &ctx);
    
    let state = ctx.state();
    let db_pool = state.db_pool.clone();
    
    // 验证订单是否存在
    let order = sqlx::query_as::<_, Order>(
        "SELECT id, customer_id, status FROM orders WHERE id = $1"
    )
    .bind(&order_id)
    .fetch_optional(&db_pool)
    .await
    .map_err(|e| anyhow::anyhow!("数据库错误: {}", e))?;
    
    if let Some(order) = order {
        if order.status == "created" {
            Ok(ValidateOrderResult {
                is_valid: true,
                reason: None,
            })
        } else {
            Ok(ValidateOrderResult {
                is_valid: false,
                reason: Some(format!("订单状态无效: {}", order.status)),
            })
        }
    } else {
        Ok(ValidateOrderResult {
            is_valid: false,
            reason: Some("订单不存在".to_string()),
        })
    }
}

/// 处理支付输入
#[derive(Serialize, Deserialize)]
pub struct ProcessPaymentInput {
    pub order_id: String,
    pub customer_id: String,
}

/// 处理支付结果
#[derive(Serialize, Deserialize)]
pub struct ProcessPaymentResult {
    pub status: String,
    pub transaction_id: Option<String>,
    pub failure_reason: Option<String>,
}

#[temporal_sdk::activity]
pub async fn process_payment(ctx: ActivityContext, input: ProcessPaymentInput) -> ActivityResult<ProcessPaymentResult> {
    let state = ctx.state();
    let payment_service = state.payment_service.clone();
    
    // 获取订单金额
    let order_amount = sqlx::query_scalar::<_, f64>(
        "SELECT total_amount FROM order_view WHERE id = $1"
    )
    .bind(&input.order_id)
    .fetch_one(&state.db_pool)
    .await
    .map_err(|e| anyhow::anyhow!("获取订单金额失败: {}", e))?;
    
    // 处理支付
    let payment_request = PaymentRequest {
        order_id: input.order_id.clone(),
        customer_id: input.customer_id.clone(),
        amount: order_amount,
        currency: "CNY".to_string(),
        idempotency_key: Uuid::new_v4().to_string(),
    };
    
    match payment_service.process_payment(payment_request).await {
        Ok(response) => {
            // 更新订单支付状态
            sqlx::query(
                "INSERT INTO order_payment (order_id, transaction_id, status, amount, processed_at)
                 VALUES ($1, $2, $3, $4, $5)"
            )
            .bind(&input.order_id)
            .bind(&response.transaction_id)
            .bind(&response.status)
            .bind(order_amount)
            .bind(Utc::now())
            .execute(&state.db_pool)
            .await
            .map_err(|e| anyhow::anyhow!("保存支付记录失败: {}", e))?;
            
            Ok(ProcessPaymentResult {
                status: response.status,
                transaction_id: Some(response.transaction_id),
                failure_reason: response.failure_reason,
            })
        },
        Err(e) => {
            // 记录支付错误
            sqlx::query(
                "INSERT INTO order_payment (order_id, status, amount, failure_reason, processed_at)
                 VALUES ($1, $2, $3, $4, $5)"
            )
            .bind(&input.order_id)
            .bind("failed")
            .bind(order_amount)
            .bind(e.to_string())
            .bind(Utc::now())
            .execute(&state.db_pool)
            .await
            .map_err(|e| anyhow::anyhow!("保存支付记录失败: {}", e))?;
            
            Ok(ProcessPaymentResult {
                status: "failed".to_string(),
                transaction_id: None,
                failure_reason: Some(e.to_string()),
            })
        }
    }
}
```

### 2.4 外部系统集成子系统

#### 4.4.1 抽象服务客户端

```rust
use async_trait::async_trait;
use serde::{Serialize, Deserialize};
use std::time::Duration;
use tonic::transport::{Channel, Endpoint};
use tracing::{info, error, instrument};
use resilient::{CircuitBreaker, CircuitBreakerConfig};

/// 库存服务客户端特质
#[async_trait]
pub trait InventoryService: Send + Sync + 'static {
    /// 检查库存可用性
    async fn check_availability(&self, items: &
# 复杂分布式系统架构设计与实现方案（续）

### 2.5 外部系统集成子系统续

#### 5.5.1 抽象服务客户端续

```rust
use async_trait::async_trait;
use serde::{Serialize, Deserialize};
use std::time::Duration;
use tonic::transport::{Channel, Endpoint};
use tracing::{info, error, instrument};
use resilient::{CircuitBreaker, CircuitBreakerConfig};

/// 库存服务客户端特质
#[async_trait]
pub trait InventoryService: Send + Sync + 'static {
    /// 检查库存可用性
    async fn check_availability(&self, items: &[OrderItem]) -> Result<InventoryCheckResult, ServiceError>;
    
    /// 预留库存
    async fn reserve_inventory(&self, request: ReserveInventoryRequest) -> Result<ReserveInventoryResponse, ServiceError>;
    
    /// 释放库存
    async fn release_inventory(&self, order_id: &str) -> Result<(), ServiceError>;
}

/// 库存检查结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InventoryCheckResult {
    pub all_available: bool,
    pub unavailable_items: Vec<UnavailableItem>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UnavailableItem {
    pub product_id: String,
    pub requested_quantity: u32,
    pub available_quantity: u32,
}

/// 预留库存请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReserveInventoryRequest {
    pub order_id: String,
    pub items: Vec<InventoryItem>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InventoryItem {
    pub product_id: String,
    pub quantity: u32,
}

/// 预留库存响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReserveInventoryResponse {
    pub reservation_id: String,
    pub status: String,
    pub reserved_at: DateTime<Utc>,
}

/// gRPC库存服务客户端实现
pub struct GrpcInventoryServiceClient {
    inner_client: inventory_proto::inventory_client::InventoryClient<Channel>,
    circuit_breaker: CircuitBreaker,
}

impl GrpcInventoryServiceClient {
    pub async fn new(service_url: &str) -> Result<Self, ServiceError> {
        let channel = Endpoint::from_shared(service_url.to_string())?
            .timeout(Duration::from_secs(5))
            .connect()
            .await?;
            
        let inner_client = inventory_proto::inventory_client::InventoryClient::new(channel);
        
        let breaker_config = CircuitBreakerConfig {
            failure_threshold: 5,
            success_threshold: 2,
            open_duration: Duration::from_secs(30),
            ..Default::default()
        };
        
        let circuit_breaker = CircuitBreaker::new("inventory_service", breaker_config);
        
        Ok(Self {
            inner_client,
            circuit_breaker,
        })
    }
}

#[async_trait]
impl InventoryService for GrpcInventoryServiceClient {
    #[instrument(skip(self, items), fields(items_count = items.len()))]
    async fn check_availability(&self, items: &[OrderItem]) -> Result<InventoryCheckResult, ServiceError> {
        // 使用断路器执行请求
        self.circuit_breaker.execute(|| async {
            let request = inventory_proto::CheckAvailabilityRequest {
                items: items.iter().map(|item| inventory_proto::InventoryItem {
                    product_id: item.product_id.clone(),
                    quantity: item.quantity,
                }).collect(),
            };
            
            let response = self.inner_client.clone().check_availability(request).await?;
            let result = response.into_inner();
            
            Ok(InventoryCheckResult {
                all_available: result.all_available,
                unavailable_items: result.unavailable_items.into_iter().map(|item| UnavailableItem {
                    product_id: item.product_id,
                    requested_quantity: item.requested_quantity,
                    available_quantity: item.available_quantity,
                }).collect(),
            })
        }).await.map_err(|e| match e {
            resilient::Error::CircuitOpen => ServiceError::ServiceUnavailable("库存服务暂时不可用".to_string()),
            resilient::Error::OperationError(inner) => inner,
        })
    }
    
    #[instrument(skip(self, request), fields(order_id = %request.order_id, items_count = request.items.len()))]
    async fn reserve_inventory(&self, request: ReserveInventoryRequest) -> Result<ReserveInventoryResponse, ServiceError> {
        self.circuit_breaker.execute(|| async {
            let proto_request = inventory_proto::ReserveInventoryRequest {
                order_id: request.order_id.clone(),
                items: request.items.iter().map(|item| inventory_proto::InventoryItem {
                    product_id: item.product_id.clone(),
                    quantity: item.quantity,
                }).collect(),
            };
            
            let response = self.inner_client.clone().reserve_inventory(proto_request).await?;
            let result = response.into_inner();
            
            let reserved_at = DateTime::<Utc>::from_str(&result.reserved_at)
                .map_err(|e| ServiceError::ParsingError(format!("日期解析错误: {}", e)))?;
                
            Ok(ReserveInventoryResponse {
                reservation_id: result.reservation_id,
                status: result.status,
                reserved_at,
            })
        }).await.map_err(|e| match e {
            resilient::Error::CircuitOpen => ServiceError::ServiceUnavailable("库存服务暂时不可用".to_string()),
            resilient::Error::OperationError(inner) => inner,
        })
    }
    
    #[instrument(skip(self), fields(order_id = %order_id))]
    async fn release_inventory(&self, order_id: &str) -> Result<(), ServiceError> {
        self.circuit_breaker.execute(|| async {
            let request = inventory_proto::ReleaseInventoryRequest {
                order_id: order_id.to_string(),
            };
            
            let _response = self.inner_client.clone().release_inventory(request).await?;
            Ok(())
        }).await.map_err(|e| match e {
            resilient::Error::CircuitOpen => ServiceError::ServiceUnavailable("库存服务暂时不可用".to_string()),
            resilient::Error::OperationError(inner) => inner,
        })
    }
}
```

#### 5.5.2 外部系统适配器工厂

```rust
use std::sync::Arc;
use tokio::sync::RwLock;

/// 外部服务工厂
pub struct ExternalServiceFactory {
    config: Arc<ServiceConfig>,
    service_registry: Arc<ServiceRegistry>,
    inventory_client: RwLock<Option<Arc<dyn InventoryService>>>,
    payment_client: RwLock<Option<Arc<dyn PaymentService>>>,
    shipping_client: RwLock<Option<Arc<dyn ShippingService>>>,
    notification_client: RwLock<Option<Arc<dyn NotificationService>>>,
}

impl ExternalServiceFactory {
    pub fn new(config: ServiceConfig, service_registry: Arc<ServiceRegistry>) -> Self {
        Self {
            config: Arc::new(config),
            service_registry,
            inventory_client: RwLock::new(None),
            payment_client: RwLock::new(None),
            shipping_client: RwLock::new(None),
            notification_client: RwLock::new(None),
        }
    }
    
    /// 获取库存服务客户端
    pub async fn get_inventory_service(&self) -> Arc<dyn InventoryService> {
        let mut client = self.inventory_client.write().await;
        
        if let Some(ref c) = *client {
            return c.clone();
        }
        
        // 从服务注册表获取服务地址
        let service_url = match self.service_registry.get_service_url("inventory-service").await {
            Ok(url) => url,
            Err(_) => self.config.inventory_service_fallback_url.clone(),
        };
        
        // 创建新客户端
        let new_client: Arc<dyn InventoryService> = match self.config.inventory_service_type.as_str() {
            "grpc" => Arc::new(GrpcInventoryServiceClient::new(&service_url).await
                .expect("无法创建库存服务客户端")),
            "rest" => Arc::new(RestInventoryServiceClient::new(&service_url)
                .expect("无法创建库存服务客户端")),
            _ => panic!("不支持的库存服务类型: {}", self.config.inventory_service_type),
        };
        
        *client = Some(new_client.clone());
        new_client
    }
    
    /// 获取支付服务客户端
    pub async fn get_payment_service(&self) -> Arc<dyn PaymentService> {
        let mut client = self.payment_client.write().await;
        
        if let Some(ref c) = *client {
            return c.clone();
        }
        
        // 从服务注册表获取服务地址
        let service_url = match self.service_registry.get_service_url("payment-service").await {
            Ok(url) => url,
            Err(_) => self.config.payment_service_fallback_url.clone(),
        };
        
        // 创建新客户端
        let new_client: Arc<dyn PaymentService> = match self.config.payment_service_type.as_str() {
            "grpc" => Arc::new(GrpcPaymentServiceClient::new(&service_url).await
                .expect("无法创建支付服务客户端")),
            "rest" => Arc::new(RestPaymentServiceClient::new(&service_url)
                .expect("无法创建支付服务客户端")),
            _ => panic!("不支持的支付服务类型: {}", self.config.payment_service_type),
        };
        
        *client = Some(new_client.clone());
        new_client
    }
    
    // 其他服务的获取方法类似...
}
```

### 2.6 查询服务子系统

#### 6.6.1 CQRS查询层

```rust
use actix_web::{web, HttpResponse, Responder};
use sqlx::PgPool;
use serde::{Serialize, Deserialize};
use tracing::{info, error, instrument};
use redis::AsyncCommands;

/// 订单查询服务
pub struct OrderQueryService {
    db_pool: PgPool,
    redis_client: redis::Client,
    metrics: Arc<Metrics>,
}

impl OrderQueryService {
    pub fn new(db_pool: PgPool, redis_client: redis::Client, metrics: Arc<Metrics>) -> Self {
        Self {
            db_pool,
            redis_client,
            metrics,
        }
    }
    
    /// 获取订单详情
    #[instrument(skip(self), fields(order_id = %order_id))]
    pub async fn get_order(&self, order_id: &str) -> Result<Option<OrderDetailsDto>, QueryError> {
        let timer = self.metrics.start_timer("order_query_get_order");
        
        // 尝试从缓存获取
        let mut redis_conn = self.redis_client.get_async_connection().await
            .map_err(|e| QueryError::CacheError(e.to_string()))?;
            
        let cache_key = format!("order:{}", order_id);
        
        if let Ok(cached_data) = redis_conn.get::<_, String>(&cache_key).await {
            info!("从缓存获取订单");
            self.metrics.increment_counter("order_query_cache_hit");
            
            return serde_json::from_str(&cached_data)
                .map(Some)
                .map_err(|e| QueryError::DeserializationError(e.to_string()));
        }
        
        self.metrics.increment_counter("order_query_cache_miss");
        
        // 从数据库获取订单基本信息
        let order = sqlx::query_as::<_, OrderDetails>(
            r#"
            SELECT 
                o.id, o.customer_id, o.status, o.total_amount, o.created_at,
                c.first_name, c.last_name, c.email,
                a.street, a.city, a.state, a.country, a.postal_code
            FROM 
                order_view o
                LEFT JOIN customer c ON o.customer_id = c.id
                LEFT JOIN address a ON o.shipping_address_id = a.id
            WHERE 
                o.id = $1
            "#
        )
        .bind(order_id)
        .fetch_optional(&self.db_pool)
        .await
        .map_err(|e| QueryError::DatabaseError(e.to_string()))?;
        
        if let Some(order) = order {
            // 获取订单项
            let items = sqlx::query_as::<_, OrderItemDto>(
                "SELECT product_id, name, quantity, unit_price FROM order_item_view WHERE order_id = $1"
            )
            .bind(order_id)
            .fetch_all(&self.db_pool)
            .await
            .map_err(|e| QueryError::DatabaseError(e.to_string()))?;
            
            // 获取支付信息
            let payment = sqlx::query_as::<_, PaymentInfoDto>(
                "SELECT transaction_id, status, amount, processed_at FROM order_payment WHERE order_id = $1"
            )
            .bind(order_id)
            .fetch_optional(&self.db_pool)
            .await
            .map_err(|e| QueryError::DatabaseError(e.to_string()))?;
            
            // 获取配送信息
            let shipment = sqlx::query_as::<_, ShipmentInfoDto>(
                "SELECT shipment_id, carrier, tracking_number, status, estimated_delivery FROM order_shipment WHERE order_id = $1"
            )
            .bind(order_id)
            .fetch_optional(&self.db_pool)
            .await
            .map_err(|e| QueryError::DatabaseError(e.to_string()))?;
            
            let result = OrderDetailsDto {
                id: order.id,
                customer: CustomerDto {
                    id: order.customer_id,
                    first_name: order.first_name,
                    last_name: order.last_name,
                    email: order.email,
                },
                items,
                shipping_address: AddressDto {
                    street: order.street,
                    city: order.city,
                    state: order.state,
                    country: order.country,
                    postal_code: order.postal_code,
                },
                payment,
                shipment,
                status: order.status,
                total_amount: order.total_amount,
                created_at: order.created_at,
            };
            
            // 缓存结果
            if let Ok(json) = serde_json::to_string(&result) {
                let _: Result<(), _> = redis_conn.set_ex(&cache_key, json, 300).await; // 5分钟过期
            }
            
            info!("成功获取订单详情");
            timer.observe_duration();
            
            Ok(Some(result))
        } else {
            timer.observe_duration();
            Ok(None)
        }
    }
    
    /// 获取客户订单列表
    #[instrument(skip(self), fields(customer_id = %customer_id))]
    pub async fn get_customer_orders(
        &self, 
        customer_id: &str,
        page: i64,
        page_size: i64
    ) -> Result<CustomerOrdersResult, QueryError> {
        let offset = (page - 1) * page_size;
        
        // 获取总订单数
        let total_count: i64 = sqlx::query_scalar(
            "SELECT COUNT(*) FROM order_view WHERE customer_id = $1"
        )
        .bind(customer_id)
        .fetch_one(&self.db_pool)
        .await
        .map_err(|e| QueryError::DatabaseError(e.to_string()))?;
        
        // 获取分页订单列表
        let orders = sqlx::query_as::<_, CustomerOrderDto>(
            r#"
            SELECT 
                id, status, total_amount, created_at,
                (SELECT COUNT(*) FROM order_item_view WHERE order_id = order_view.id) as item_count
            FROM 
                order_view 
            WHERE 
                customer_id = $1
            ORDER BY 
                created_at DESC
            LIMIT $2 OFFSET $3
            "#
        )
        .bind(customer_id)
        .bind(page_size)
        .bind(offset)
        .fetch_all(&self.db_pool)
        .await
        .map_err(|e| QueryError::DatabaseError(e.to_string()))?;
        
        Ok(CustomerOrdersResult {
            customer_id: customer_id.to_string(),
            orders,
            page,
            page_size,
            total_count,
            total_pages: (total_count + page_size - 1) / page_size,
        })
    }
    
    /// 搜索订单
    #[instrument(skip(self), fields(query = %query))]
    pub async fn search_orders(&self, query: &str, page: i64, page_size: i64) -> Result<OrderSearchResult, QueryError> {
        let offset = (page - 1) * page_size;
        
        // 使用全文检索搜索订单
        let search_query = format!("%{}%", query);
        
        // 获取匹配订单总数
        let total_count: i64 = sqlx::query_scalar(
            r#"
            SELECT COUNT(*) FROM order_view o
            LEFT JOIN customer c ON o.customer_id = c.id
            WHERE 
                o.id::text ILIKE $1 OR
                c.email ILIKE $1 OR
                c.first_name ILIKE $1 OR
                c.last_name ILIKE $1
            "#
        )
        .bind(&search_query)
        .fetch_one(&self.db_pool)
        .await
        .map_err(|e| QueryError::DatabaseError(e.to_string()))?;
        
        // 获取分页搜索结果
        let orders = sqlx::query_as::<_, SearchOrderDto>(
            r#"
            SELECT 
                o.id, o.status, o.total_amount, o.created_at,
                c.id as customer_id, c.first_name, c.last_name, c.email
            FROM 
                order_view o
                LEFT JOIN customer c ON o.customer_id = c.id
            WHERE 
                o.id::text ILIKE $1 OR
                c.email ILIKE $1 OR
                c.first_name ILIKE $1 OR
                c.last_name ILIKE $1
            ORDER BY
                o.created_at DESC
            LIMIT $2 OFFSET $3
            "#
        )
        .bind(&search_query)
        .bind(page_size)
        .bind(offset)
        .fetch_all(&self.db_pool)
        .await
        .map_err(|e| QueryError::DatabaseError(e.to_string()))?;
        
        Ok(OrderSearchResult {
            query: query.to_string(),
            orders,
            page,
            page_size,
            total_count,
            total_pages: (total_count + page_size - 1) / page_size,
        })
    }
}
```

#### 6.6.2 API端点

```rust
use actix_web::{web, HttpResponse, Responder, get, post};
use serde::{Serialize, Deserialize};

/// 订单控制器
pub struct OrderController {
    query_service: Arc<OrderQueryService>,
    command_bus: Arc<CommandBus>,
}

impl OrderController {
    pub fn new(query_service: Arc<OrderQueryService>, command_bus: Arc<CommandBus>) -> Self {
        Self {
            query_service,
            command_bus,
        }
    }
}

/// 注册API路由
pub fn register_routes(config: &mut web::ServiceConfig, controller: Arc<OrderController>) {
    config.service(
        web::scope("/api/v1/orders")
            .route("", web::post().to(create_order))
            .route("/{id}", web::get().to(get_order))
            .route("/{id}/cancel", web::post().to(cancel_order))
            .route("/customer/{customer_id}", web::get().to(get_customer_orders))
            .route("/search", web::get().to(search_orders))
    );
}

/// 创建订单请求
#[derive(Serialize, Deserialize)]
struct CreateOrderRequest {
    customer_id: String,
    items: Vec<OrderItemRequest>,
    shipping_address: AddressRequest,
}

/// 创建订单端点
#[instrument(skip(req, data), fields(customer_id = %req.customer_id))]
async fn create_order(
    req: web::Json<CreateOrderRequest>,
    data: web::Data<Arc<OrderController>>,
) -> impl Responder {
    let command = CreateOrderCommand {
        command_id: Uuid::new_v4(),
        customer_id: req.customer_id.clone(),
        items: req.items.iter().map(|item| OrderItem {
            product_id: item.product_id.clone(),
            quantity: item.quantity,
            unit_price: item.unit_price,
        }).collect(),
        shipping_address: Address {
            street: req.shipping_address.street.clone(),
            city: req.shipping_address.city.clone(),
            state: req.shipping_address.state.clone(),
            country: req.shipping_address.country.clone(),
            postal_code: req.shipping_address.postal_code.clone(),
        },
        correlation_id: None,
    };
    
    match data.command_bus.dispatch(command).await {
        Ok(events) => {
            // 从事件中提取订单ID
            if let Some(event) = events.iter().find(|e| e.event_type() == "order_created") {
                if let Ok(created_event) = serde_json::from_value::<OrderCreatedEvent>(serde_json::to_value(event).unwrap()) {
                    return HttpResponse::Created().json(json!({
                        "order_id": created_event.aggregate_id,
                        "status": "created",
                        "message": "订单创建成功"
                    }));
                }
            }
            
            HttpResponse::InternalServerError().json(json!({
                "error": "处理订单创建失败"
            }))
        },
        Err(e) => {
            error!(error = %e, "订单创建失败");
            
            let status_code = match e {
                CommandError::ValidationError(_) => StatusCode::BAD_REQUEST,
                CommandError::NotFound(_) => StatusCode::NOT_FOUND,
                CommandError::Unauthorized(_) => StatusCode::UNAUTHORIZED,
                _ => StatusCode::INTERNAL_SERVER_ERROR,
            };
            
            HttpResponse::build(status_code).json(json!({
                "error": e.to_string()
            }))
        }
    }
}

/// 获取订单端点
#[instrument(skip(data), fields(order_id = %id))]
async fn get_order(
    id: web::Path<String>,
    data: web::Data<Arc<OrderController>>,
) -> impl Responder {
    match data.query_service.get_order(&id).await {
        Ok(Some(order)) => HttpResponse::Ok().json(order),
        Ok(None) => HttpResponse::NotFound().json(json!({
            "error": "订单不存在"
        })),
        Err(e) => {
            error!(error = %e, "获取订单失败");
            HttpResponse::InternalServerError().json(json!({
                "error": "获取订单失败",
                "details": e.to_string()
            }))
        }
    }
}
```

### 2.7 监控与可观测性子系统

#### 7.7.1 分布式追踪集成

```rust
use opentelemetry::{global, sdk::propagation::TraceContextPropagator};
use opentelemetry::sdk::trace::{self, IdGenerator, Sampler};
use opentelemetry::sdk::Resource;
use opentelemetry_jaeger::{Propagator, new_pipeline};
use opentelemetry::KeyValue;
use tracing_opentelemetry::OpenTelemetrySpanExt;
use tracing_subscriber::{layer::SubscriberExt, Registry};
use tracing_subscriber::layer::Layer;

/// 初始化追踪系统
pub fn init_tracer(service_name: &str, jaeger_endpoint: &str) -> Result<(), Box<dyn Error>> {
    // 设置全局传播器
    global::set_text_map_propagator(TraceContextPropagator::new());
    
    // 创建Jaeger导出器
    let tracer = new_pipeline()
        .with_service_name(service_name)
        .with_collector_endpoint(jaeger_endpoint)
        .with_trace_config(
            trace::config()
                .with_sampler(Sampler::AlwaysOn)
                .with_id_generator(IdGenerator::default())
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", service_name.to_string()),
                    KeyValue::new("service.version", env!("CARGO_PKG_VERSION").to_string()),
                    KeyValue::new("deployment.environment", std::env::var("ENVIRONMENT").unwrap_or_else(|_| "development".to_string())),
                ]))
        )
        .install_batch(opentelemetry::runtime::Tokio)?;
    
    // 创建OpenTelemetry tracing层
    let telemetry = tracing_opentelemetry::layer().with_tracer(tracer);
    
    // 创建格式化日志层
    let fmt_layer = tracing_subscriber::fmt::layer()
        .with_ansi(true)
        .with_target(true);
    
    // 创建EnvFilter层
    let filter_layer = tracing_subscriber::EnvFilter::try_from_default_env()
        .or_else(|_| tracing_subscriber::EnvFilter::try_new("info"))?;
    
    // 注册订阅者
    Registry::default()
        .with(filter_layer)
        .with(fmt_layer)
        .with(telemetry)
        .init();
    
    Ok(())
}

/// 提取请求上下文
pub fn extract_tracing_context(req: &HttpRequest) -> tracing::Span {
    let parent_cx = global::get_text_map_propagator(|propagator| {
        propagator.extract(&RequestHeaderCarrier(req.headers()))
    });
    
    tracing::span!(
        tracing::Level::INFO, 
        "http_request",
        method = %req.method(),
        uri = %req.uri(),
        trace_id = tracing::field::Empty,
        span_id = tracing::field::Empty
    ).with_subscriber(move |id, _| {
        id.with_current(|current| {
            current.record("trace_id", &tracing::field::display(parent_cx.span().span_context().trace_id()));
            current.record("span_id", &tracing::field::display(parent_cx.span().span_context().span_id()));
        })
    })
}

/// HTTP请求头载体
struct RequestHeaderCarrier<'a>(&'a HeaderMap);

impl<'a> Extractor for RequestHeaderCarrier<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.0.get(key).and_then(|v| v.to_str().ok())
    }
    
    fn keys(&self) -> Vec<&str> {
        self.0.keys().map(|k| k.as_str()).collect()
    }
}
```

#### 7.7.2 指标监控实现

```rust
use metrics::{counter, gauge, histogram};
use metrics_exporter_prometheus::{PrometheusBuilder, PrometheusHandle};
use std::time::{Duration, Instant};
use tokio::time::interval;
use std::sync::Arc;

/// 应用指标
pub struct Metrics {
    prometheus_handle: PrometheusHandle,
}

impl Metrics {
    pub fn new() -> Self {
        let builder = PrometheusBuilder::new();
        let handle = builder
            .install()
            .expect("无法安装Prometheus导出器");
            
        Self {
            prometheus_handle: handle,
        }
    }
    
    /// 获取Prometheus指标导出点
    pub fn get_prometheus_handler(&self) -> PrometheusHandle {
        self.prometheus_handle.clone()
    }
    
    /// 递增计数器
    pub fn increment_counter(&self, name: &str) {
        counter!(name, 1);
    }
    
    /// 递增带标签的计数器
    pub fn increment_counter_with_labels(&self, name: &str, labels: &[(&str, &str)]) {
        let labels: Vec<(String, String)> = labels.iter()
            .map(|(k, v)| (k.to_string(), v.to_string()))
            .collect();
            
        counter!(name, 1, &labels);
    }
    
    /// 记录数值
    pub fn set_gauge(&self, name: &str, value: f64) {
        gauge!(name, value);
    }
    
    /// 记录直方图数据
# 复杂分布式系统架构设计与实现方案（续）

### 2.8 监控与可观测性子系统续

#### 8.8.1 指标监控实现续

```rust
use metrics::{counter, gauge, histogram};
use metrics_exporter_prometheus::{PrometheusBuilder, PrometheusHandle};
use std::time::{Duration, Instant};
use tokio::time::interval;
use std::sync::Arc;

/// 应用指标
pub struct Metrics {
    prometheus_handle: PrometheusHandle,
}

impl Metrics {
    pub fn new() -> Self {
        let builder = PrometheusBuilder::new();
        let handle = builder
            .install()
            .expect("无法安装Prometheus导出器");
            
        Self {
            prometheus_handle: handle,
        }
    }
    
    /// 获取Prometheus指标导出点
    pub fn get_prometheus_handler(&self) -> PrometheusHandle {
        self.prometheus_handle.clone()
    }
    
    /// 递增计数器
    pub fn increment_counter(&self, name: &str) {
        counter!(name, 1);
    }
    
    /// 递增带标签的计数器
    pub fn increment_counter_with_labels(&self, name: &str, labels: &[(&str, &str)]) {
        let labels: Vec<(String, String)> = labels.iter()
            .map(|(k, v)| (k.to_string(), v.to_string()))
            .collect();
            
        counter!(name, 1, &labels);
    }
    
    /// 记录数值
    pub fn set_gauge(&self, name: &str, value: f64) {
        gauge!(name, value);
    }
    
    /// 记录直方图数据
    pub fn record_histogram(&self, name: &str, value: f64) {
        histogram!(name, value);
    }
    
    /// 开始计时器
    pub fn start_timer(&self, name: &str) -> OperationTimer {
        OperationTimer {
            name: name.to_string(),
            start: Instant::now(),
        }
    }
    
    /// 启动系统指标收集
    pub async fn start_system_metrics_collector(&self) -> tokio::task::JoinHandle<()> {
        let metrics_interval = Duration::from_secs(15);
        
        tokio::spawn(async move {
            let mut interval = interval(metrics_interval);
            
            // 这里可以使用系统库如sysinfo收集系统指标
            // 这里以简单模拟为例
            loop {
                interval.tick().await;
                
                // 收集系统指标
                gauge!("system.memory.used_mb", 1024.0);
                gauge!("system.cpu.usage_percent", 45.0);
                gauge!("system.disk.free_gb", 100.0);
            }
        })
    }
}

/// 操作计时器
pub struct OperationTimer {
    name: String,
    start: Instant,
}

impl OperationTimer {
    pub fn observe_duration(&self) {
        let duration = self.start.elapsed();
        histogram!(&self.name, duration.as_secs_f64());
    }
}

impl Drop for OperationTimer {
    fn drop(&mut self) {
        self.observe_duration();
    }
}

/// 健康检查服务
pub struct HealthCheckService {
    db_pool: PgPool,
    redis_client: redis::Client,
    kafka_producer: Arc<EventProducer>,
}

impl HealthCheckService {
    pub fn new(
        db_pool: PgPool,
        redis_client: redis::Client,
        kafka_producer: Arc<EventProducer>,
    ) -> Self {
        Self {
            db_pool,
            redis_client,
            kafka_producer,
        }
    }
    
    /// 检查所有依赖健康状态
    pub async fn check_health(&self) -> HealthStatus {
        let db_check = self.check_database().await;
        let redis_check = self.check_redis().await;
        let kafka_check = self.check_kafka().await;
        
        let status = if db_check.status == "up" 
                       && redis_check.status == "up" 
                       && kafka_check.status == "up" {
            "up"
        } else {
            "down"
        };
        
        HealthStatus {
            status: status.to_string(),
            components: vec![
                db_check,
                redis_check,
                kafka_check,
            ],
            timestamp: Utc::now(),
        }
    }
    
    async fn check_database(&self) -> ComponentHealth {
        let start = Instant::now();
        
        match sqlx::query("SELECT 1").execute(&self.db_pool).await {
            Ok(_) => ComponentHealth {
                name: "database".to_string(),
                status: "up".to_string(),
                details: None,
                response_time_ms: start.elapsed().as_millis() as u64,
            },
            Err(e) => ComponentHealth {
                name: "database".to_string(),
                status: "down".to_string(),
                details: Some(format!("数据库连接失败: {}", e)),
                response_time_ms: start.elapsed().as_millis() as u64,
            },
        }
    }
    
    async fn check_redis(&self) -> ComponentHealth {
        let start = Instant::now();
        
        match self.redis_client.get_async_connection().await {
            Ok(mut conn) => {
                match conn.ping::<String>().await {
                    Ok(_) => ComponentHealth {
                        name: "redis".to_string(),
                        status: "up".to_string(),
                        details: None,
                        response_time_ms: start.elapsed().as_millis() as u64,
                    },
                    Err(e) => ComponentHealth {
                        name: "redis".to_string(),
                        status: "down".to_string(),
                        details: Some(format!("Redis ping失败: {}", e)),
                        response_time_ms: start.elapsed().as_millis() as u64,
                    },
                }
            },
            Err(e) => ComponentHealth {
                name: "redis".to_string(),
                status: "down".to_string(),
                details: Some(format!("Redis连接失败: {}", e)),
                response_time_ms: start.elapsed().as_millis() as u64,
            },
        }
    }
    
    async fn check_kafka(&self) -> ComponentHealth {
        let start = Instant::now();
        
        // 简单的kafka健康检查
        match self.kafka_producer.check_connectivity().await {
            Ok(_) => ComponentHealth {
                name: "kafka".to_string(),
                status: "up".to_string(),
                details: None,
                response_time_ms: start.elapsed().as_millis() as u64,
            },
            Err(e) => ComponentHealth {
                name: "kafka".to_string(),
                status: "down".to_string(),
                details: Some(format!("Kafka连接失败: {}", e)),
                response_time_ms: start.elapsed().as_millis() as u64,
            },
        }
    }
}

/// 健康状态
#[derive(Serialize)]
struct HealthStatus {
    status: String,
    components: Vec<ComponentHealth>,
    timestamp: DateTime<Utc>,
}

/// 组件健康状态
#[derive(Serialize)]
struct ComponentHealth {
    name: String,
    status: String,
    details: Option<String>,
    response_time_ms: u64,
}
```

### 2.9 配置与服务发现子系统

#### 9.9.1 动态配置管理

```rust
use config::{Config, ConfigError, Environment, File};
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use tokio::sync::watch;
use tokio::time::{Duration, interval};
use tracing::{info, error};

/// 应用配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AppConfig {
    pub server: ServerConfig,
    pub database: DatabaseConfig,
    pub redis: RedisConfig,
    pub kafka: KafkaConfig,
    pub temporal: TemporalConfig,
    pub tracing: TracingConfig,
    pub external_services: ExternalServicesConfig,
    pub circuit_breakers: CircuitBreakersConfig,
    pub cache: CacheConfig,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServerConfig {
    pub host: String,
    pub port: u16,
    pub workers: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DatabaseConfig {
    pub url: String,
    pub max_connections: u32,
    pub min_connections: u32,
    pub max_lifetime: Duration,
    pub idle_timeout: Duration,
}

// 其他具体配置部分省略...

/// 配置管理器
pub struct ConfigManager {
    current_config: Arc<AppConfig>,
    config_sender: watch::Sender<Arc<AppConfig>>,
    config_receiver: watch::Receiver<Arc<AppConfig>>,
    config_source: Box<dyn ConfigSource>,
}

impl ConfigManager {
    /// 从文件创建配置
    pub fn from_file(config_path: &str) -> Result<Self, ConfigError> {
        let config = Self::load_config_from_file(config_path)?;
        let (tx, rx) = watch::channel(Arc::new(config.clone()));
        
        let config_source: Box<dyn ConfigSource> = if config_path.ends_with(".json") {
            Box::new(JsonFileConfigSource::new(config_path.to_string()))
        } else {
            Box::new(TomlFileConfigSource::new(config_path.to_string()))
        };
        
        Ok(Self {
            current_config: Arc::new(config),
            config_sender: tx,
            config_receiver: rx,
            config_source,
        })
    }
    
    /// 从Consul创建配置
    pub fn from_consul(consul_url: &str, app_name: &str) -> Result<Self, ConfigError> {
        let consul_source = ConsulConfigSource::new(consul_url.to_string(), app_name.to_string());
        let config = consul_source.load_config().map_err(|e| {
            ConfigError::Foreign(Box::new(e))
        })?;
        
        let (tx, rx) = watch::channel(Arc::new(config.clone()));
        
        Ok(Self {
            current_config: Arc::new(config),
            config_sender: tx,
            config_receiver: rx,
            config_source: Box::new(consul_source),
        })
    }
    
    /// 加载配置文件
    fn load_config_from_file(config_path: &str) -> Result<AppConfig, ConfigError> {
        let builder = Config::builder()
            .add_source(File::with_name(config_path))
            .add_source(Environment::with_prefix("APP").separator("__"));
            
        let config = builder.build()?;
        config.try_deserialize()
    }
    
    /// 获取当前配置
    pub fn get_config(&self) -> Arc<AppConfig> {
        self.current_config.clone()
    }
    
    /// 获取配置观察器
    pub fn get_config_watcher(&self) -> watch::Receiver<Arc<AppConfig>> {
        self.config_receiver.clone()
    }
    
    /// 启动配置监听
    pub async fn start_config_watch(&self, refresh_interval: Duration) -> tokio::task::JoinHandle<()> {
        let config_source = self.config_source.clone_box();
        let sender = self.config_sender.clone();
        let mut current_config = self.current_config.clone();
        
        tokio::spawn(async move {
            let mut interval = interval(refresh_interval);
            
            loop {
                interval.tick().await;
                
                match config_source.load_config() {
                    Ok(new_config) => {
                        if !config_equals(&current_config, &Arc::new(new_config.clone())) {
                            info!("检测到配置变更,更新配置");
                            
                            let new_config_arc = Arc::new(new_config);
                            current_config = new_config_arc.clone();
                            
                            if let Err(e) = sender.send(new_config_arc) {
                                error!("发送配置更新失败: {:?}", e);
                            }
                        }
                    },
                    Err(e) => {
                        error!("加载配置失败: {:?}", e);
                    }
                }
            }
        })
    }
}

/// 比较配置是否相等
fn config_equals(a: &Arc<AppConfig>, b: &Arc<AppConfig>) -> bool {
    let a_json = serde_json::to_string(a).unwrap_or_default();
    let b_json = serde_json::to_string(b).unwrap_or_default();
    a_json == b_json
}

/// 配置源特质
#[async_trait]
pub trait ConfigSource: Send + Sync {
    fn load_config(&self) -> Result<AppConfig, Box<dyn std::error::Error>>;
    fn clone_box(&self) -> Box<dyn ConfigSource>;
}

/// JSON文件配置源
pub struct JsonFileConfigSource {
    file_path: String,
}

impl JsonFileConfigSource {
    pub fn new(file_path: String) -> Self {
        Self { file_path }
    }
}

impl ConfigSource for JsonFileConfigSource {
    fn load_config(&self) -> Result<AppConfig, Box<dyn std::error::Error>> {
        let content = std::fs::read_to_string(&self.file_path)?;
        let config: AppConfig = serde_json::from_str(&content)?;
        Ok(config)
    }
    
    fn clone_box(&self) -> Box<dyn ConfigSource> {
        Box::new(Self {
            file_path: self.file_path.clone(),
        })
    }
}

/// Consul配置源
pub struct ConsulConfigSource {
    consul_url: String,
    app_name: String,
}

impl ConsulConfigSource {
    pub fn new(consul_url: String, app_name: String) -> Self {
        Self { consul_url, app_name }
    }
}

impl ConfigSource for ConsulConfigSource {
    fn load_config(&self) -> Result<AppConfig, Box<dyn std::error::Error>> {
        // 创建Consul客户端
        let client = consul_rs::Client::new(&self.consul_url)?;
        
        // 获取配置
        let (_, data) = client.kv().get(&format!("config/{}", self.app_name)).map_err(|e| {
            format!("从Consul获取配置失败: {}", e)
        })?.ok_or_else(|| {
            "Consul中不存在配置".to_string()
        })?;
        
        // 解析配置
        let config: AppConfig = serde_json::from_slice(&data)?;
        Ok(config)
    }
    
    fn clone_box(&self) -> Box<dyn ConfigSource> {
        Box::new(Self {
            consul_url: self.consul_url.clone(),
            app_name: self.app_name.clone(),
        })
    }
}
```

#### 9.9.2 服务注册与发现

```rust
use consul_rs::{Client, Config, RegisterServiceRequest, ServiceEntry};
use std::sync::Arc;
use tokio::sync::RwLock;
use tokio::time::{Duration, interval};
use resilient::CircuitBreaker;
use rand::{thread_rng, seq::SliceRandom};
use serde::{Serialize, Deserialize};
use uuid::Uuid;
use std::collections::HashMap;
use std::net::SocketAddr;
use tracing::{info, error, warn};

/// 服务注册管理器
pub struct ServiceRegistration {
    consul_client: Client,
    service_id: String,
    service_name: String,
    host: String,
    port: u16,
    health_check_path: String,
    health_check_interval: String,
}

impl ServiceRegistration {
    pub fn new(
        consul_url: &str,
        service_name: &str,
        host: &str,
        port: u16,
        health_check_path: &str,
        health_check_interval: &str,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        let consul_client = Client::new(consul_url)?;
        
        let service_id = format!("{}-{}", service_name, Uuid::new_v4());
        
        Ok(Self {
            consul_client,
            service_id,
            service_name: service_name.to_string(),
            host: host.to_string(),
            port,
            health_check_path: health_check_path.to_string(),
            health_check_interval: health_check_interval.to_string(),
        })
    }
    
    /// 注册服务
    pub async fn register(&self) -> Result<(), Box<dyn std::error::Error>> {
        let check_url = format!("http://{}:{}{}", self.host, self.port, self.health_check_path);
        
        let request = RegisterServiceRequest {
            id: Some(self.service_id.clone()),
            name: self.service_name.clone(),
            address: Some(self.host.clone()),
            port: Some(self.port),
            tags: Some(vec!["rust".to_string(), "v1".to_string()]),
            check: Some(consul_rs::CheckInfo {
                http: Some(check_url),
                interval: Some(self.health_check_interval.clone()),
                timeout: Some("5s".to_string()),
                ..Default::default()
            }),
            ..Default::default()
        };
        
        self.consul_client.agent().register_service_with_request(request).await?;
        
        info!("服务已注册到Consul: id={}, name={}", self.service_id, self.service_name);
        Ok(())
    }
    
    /// 注销服务
    pub async fn deregister(&self) -> Result<(), Box<dyn std::error::Error>> {
        self.consul_client.agent().deregister_service(&self.service_id).await?;
        info!("服务已从Consul注销: id={}", self.service_id);
        Ok(())
    }
}

/// 服务发现管理器
pub struct ServiceDiscovery {
    consul_client: Client,
    service_cache: RwLock<HashMap<String, ServiceCacheEntry>>,
    circuit_breaker: Arc<CircuitBreaker>,
}

struct ServiceCacheEntry {
    services: Vec<ServiceInfo>,
    last_updated: chrono::DateTime<chrono::Utc>,
}

#[derive(Clone, Debug)]
pub struct ServiceInfo {
    pub id: String,
    pub service_name: String,
    pub address: String,
    pub port: u16,
    pub tags: Vec<String>,
    pub healthy: bool,
}

impl ServiceDiscovery {
    pub fn new(consul_url: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let consul_client = Client::new(consul_url)?;
        
        let circuit_breaker = Arc::new(CircuitBreaker::new(
            "consul_client",
            resilient::CircuitBreakerConfig {
                failure_threshold: 5,
                success_threshold: 2,
                open_duration: Duration::from_secs(30),
                ..Default::default()
            }
        ));
        
        Ok(Self {
            consul_client,
            service_cache: RwLock::new(HashMap::new()),
            circuit_breaker,
        })
    }
    
    /// 发现服务
    pub async fn discover_service(&self, service_name: &str) -> Result<Vec<ServiceInfo>, ServiceDiscoveryError> {
        // 先检查缓存
        {
            let cache = self.service_cache.read().await;
            if let Some(entry) = cache.get(service_name) {
                // 如果缓存未过期,直接使用
                if entry.last_updated + chrono::Duration::seconds(30) > chrono::Utc::now() {
                    return Ok(entry.services.clone());
                }
            }
        }
        
        // 使用断路器调用Consul
        let services = self.circuit_breaker.execute(|| async {
            let services = self.consul_client.health().service(service_name, None, true).await?;
            
            let service_infos = services.into_iter().map(|s| {
                ServiceInfo {
                    id: s.service.id,
                    service_name: s.service.service,
                    address: s.service.address.unwrap_or_else(|| "127.0.0.1".to_string()),
                    port: s.service.port.unwrap_or(80),
                    tags: s.service.tags.unwrap_or_default(),
                    healthy: s.checks.iter().all(|c| c.status == "passing"),
                }
            }).collect::<Vec<_>>();
            
            Ok::<Vec<ServiceInfo>, Box<dyn std::error::Error>>(service_infos)
        }).await.map_err(|e| match e {
            resilient::Error::CircuitOpen => ServiceDiscoveryError::ServiceUnavailable("服务发现暂时不可用".to_string()),
            resilient::Error::OperationError(inner) => ServiceDiscoveryError::ConsulError(inner.to_string()),
        })?;
        
        // 更新缓存
        {
            let mut cache = self.service_cache.write().await;
            cache.insert(service_name.to_string(), ServiceCacheEntry {
                services: services.clone(),
                last_updated: chrono::Utc::now(),
            });
        }
        
        if services.is_empty() {
            return Err(ServiceDiscoveryError::ServiceNotFound(service_name.to_string()));
        }
        
        Ok(services)
    }
    
    /// 获取服务URL(使用随机负载均衡)
    pub async fn get_service_url(&self, service_name: &str) -> Result<String, ServiceDiscoveryError> {
        let services = self.discover_service(service_name).await?;
        
        // 过滤出健康的服务
        let healthy_services: Vec<_> = services.into_iter()
            .filter(|s| s.healthy)
            .collect();
            
        if healthy_services.is_empty() {
            return Err(ServiceDiscoveryError::NoHealthyService(service_name.to_string()));
        }
        
        // 随机选择一个健康服务
        let mut rng = thread_rng();
        let service = healthy_services.choose(&mut rng)
            .ok_or_else(|| ServiceDiscoveryError::NoHealthyService(service_name.to_string()))?;
            
        let scheme = if service.tags.contains(&"secure".to_string()) { "https" } else { "http" };
        let url = format!("{}://{}:{}", scheme, service.address, service.port);
        
        Ok(url)
    }
    
    /// 启动缓存刷新任务
    pub async fn start_cache_refresh(&self, refresh_interval: Duration) -> tokio::task::JoinHandle<()> {
        let service_discovery = Arc::new(self.clone());
        
        tokio::spawn(async move {
            let mut interval = interval(refresh_interval);
            
            loop {
                interval.tick().await;
                
                let services_to_refresh = {
                    let cache = service_discovery.service_cache.read().await;
                    cache.keys().cloned().collect::<Vec<_>>()
                };
                
                for service_name in services_to_refresh {
                    if let Err(e) = service_discovery.discover_service(&service_name).await {
                        warn!("刷新服务 {} 缓存失败: {:?}", service_name, e);
                    }
                }
            }
        })
    }
}

impl Clone for ServiceDiscovery {
    fn clone(&self) -> Self {
        Self {
            consul_client: self.consul_client.clone(),
            service_cache: RwLock::new(HashMap::new()),
            circuit_breaker: self.circuit_breaker.clone(),
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum ServiceDiscoveryError {
    #[error("服务 {0} 未找到")]
    ServiceNotFound(String),
    
    #[error("服务 {0} 没有健康实例")]
    NoHealthyService(String),
    
    #[error("Consul错误: {0}")]
    ConsulError(String),
    
    #[error("服务发现暂时不可用: {0}")]
    ServiceUnavailable(String),
}
```

## 3 三、数据模型设计

### 3.1 事件存储表结构

```sql
-- 事件存储表
CREATE TABLE event_store (
    id SERIAL PRIMARY KEY,
    aggregate_id VARCHAR(50) NOT NULL,
    aggregate_type VARCHAR(50) NOT NULL,
    event_type VARCHAR(100) NOT NULL,
    event_data JSONB NOT NULL,
    sequence INTEGER NOT NULL,
    occurred_at TIMESTAMP WITH TIME ZONE NOT NULL,
    metadata JSONB,
    created_at TIMESTAMP WITH TIME ZONE NOT NULL DEFAULT NOW()
);

-- 索引
CREATE INDEX idx_event_store_aggregate_id ON event_store(aggregate_id);
CREATE INDEX idx_event_store_aggregate_type ON event_store(aggregate_type);
CREATE INDEX idx_event_store_event_type ON event_store(event_type);
CREATE INDEX idx_event_store_occurred_at ON event_store(occurred_at);

-- 聚合快照表
CREATE TABLE aggregate_snapshots (
    id SERIAL PRIMARY KEY,
    aggregate_id VARCHAR(50) NOT NULL,
    aggregate_type VARCHAR(50) NOT NULL,
    version INTEGER NOT NULL,
    state JSONB NOT NULL,
    created_at TIMESTAMP WITH TIME ZONE NOT NULL DEFAULT NOW(),
    UNIQUE(aggregate_id, aggregate_type, version)
);
```

### 3.2 读模型表结构

```sql
-- 订单视图表
CREATE TABLE order_view (
    id VARCHAR(50) PRIMARY KEY,
    customer_id VARCHAR(50) NOT NULL,
    status VARCHAR(20) NOT NULL,
    total_amount DECIMAL(12, 2) NOT NULL,
    item_count INTEGER NOT NULL,
    shipping_address_id VARCHAR(50),
    created_at TIMESTAMP WITH TIME ZONE NOT NULL,
    updated_at TIMESTAMP WITH TIME ZONE NOT NULL DEFAULT NOW()
);

-- 订单项视图表
CREATE TABLE order_item_view (
    id SERIAL PRIMARY KEY,
    order_id VARCHAR(50) NOT NULL REFERENCES order_view(id),
    product_id VARCHAR(50) NOT NULL,
    name VARCHAR(200) NOT NULL,
    quantity INTEGER NOT NULL,
    unit_price DECIMAL(12, 2) NOT NULL,
    UNIQUE(order_id, product_id)
);

-- 支付信息表
CREATE TABLE order_payment (
    id SERIAL PRIMARY KEY,
    order_id VARCHAR(50) NOT NULL REFERENCES order_view(id),
    transaction_id VARCHAR(100),
    status VARCHAR(20) NOT NULL,
    amount DECIMAL(12, 2) NOT NULL,
    failure_reason TEXT,
    processed_at TIMESTAMP WITH TIME ZONE NOT NULL
);

-- 配送信息表
CREATE TABLE order_shipment (
    id SERIAL PRIMARY KEY,
    order_id VARCHAR(50) NOT NULL REFERENCES order_view(id),
    shipment_id VARCHAR(100) NOT NULL,
    carrier VARCHAR(50) NOT NULL,
    tracking_number VARCHAR(100),
    status VARCHAR(20) NOT NULL,
    estimated_delivery TIMESTAMP WITH TIME ZONE,
    created_at TIMESTAMP WITH TIME ZONE NOT NULL DEFAULT NOW()
);

-- 索引
CREATE INDEX idx_order_view_customer_id ON order_view(customer_id);
CREATE INDEX idx_order_view_status ON order_view(status);
CREATE INDEX idx_order_view_created_at ON order_view(created_at);
CREATE INDEX idx_order_payment_status ON order_payment(status);
CREATE INDEX idx_order_shipment_status ON order_shipment(status);
```

## 4 四、部署架构

### 4.1 容器化与服务编排

以下是使用Docker Compose定义的服务部署配置:

```yaml
version: '3.8'

services:
  # 应用服务
  order-service:
    build:
      context: .
      dockerfile: Dockerfile
    image: order-service:latest
    environment:
      - RUST_LOG=info
      - APP__DATABASE__URL=postgres://postgres:password@postgres:5432/orderdb
      - APP__REDIS__URL=redis://redis:6379
      - APP__KAFKA__BROKERS=kafka:9092
      - APP__TEMPORAL__URL=temporal:7233
      - APP__CONSUL__URL=http://consul:8500
    ports:
      - "8080:8080"
    depends_on:
      - postgres
      - redis
      - kafka
      - temporal
      - consul
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:8080/health"]
      interval: 30s
      timeout: 10s
      retries: 3
      start_period: 40s
    deploy:
      replicas: 2
      update_config:
        parallelism: 1
        delay: 10s
      restart_policy:
        condition: on-failure
        
  # 数据库
  postgres:
    image: postgres:14-alpine
    environment:
      - POSTGRES_PASSWORD=password
      - POSTGRES_DB=orderdb
    volumes:
      - postgres-data:/var/lib/postgresql/data
      - ./init-db.sql:/docker-entrypoint-initdb.d/init-db.sql
    ports:
      - "5432:5432"
  
  # Redis缓存
  redis:
    image: redis:6-alpine
    ports:
      
# 复杂分布式系统架构设计与实现方案（续）

## 5 四、部署架构续

### 5.1 容器化与服务编排续

```yaml
version: '3.8'

services:
  # 应用服务
  order-service:
    build:
      context: .
      dockerfile: Dockerfile
    image: order-service:latest
    environment:
      - RUST_LOG=info
      - APP__DATABASE__URL=postgres://postgres:password@postgres:5432/orderdb
      - APP__REDIS__URL=redis://redis:6379
      - APP__KAFKA__BROKERS=kafka:9092
      - APP__TEMPORAL__URL=temporal:7233
      - APP__CONSUL__URL=http://consul:8500
    ports:
      - "8080:8080"
    depends_on:
      - postgres
      - redis
      - kafka
      - temporal
      - consul
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:8080/health"]
      interval: 30s
      timeout: 10s
      retries: 3
      start_period: 40s
    deploy:
      replicas: 2
      update_config:
        parallelism: 1
        delay: 10s
      restart_policy:
        condition: on-failure
        
  # 数据库
  postgres:
    image: postgres:14-alpine
    environment:
      - POSTGRES_PASSWORD=password
      - POSTGRES_DB=orderdb
    volumes:
      - postgres-data:/var/lib/postgresql/data
      - ./init-db.sql:/docker-entrypoint-initdb.d/init-db.sql
    ports:
      - "5432:5432"
  
  # Redis缓存
  redis:
    image: redis:6-alpine
    ports:
      - "6379:6379"
    volumes:
      - redis-data:/data
    command: redis-server --appendonly yes
      
  # Kafka消息队列
  zookeeper:
    image: confluentinc/cp-zookeeper:7.2.1
    environment:
      ZOOKEEPER_CLIENT_PORT: 2181
    volumes:
      - zookeeper-data:/var/lib/zookeeper/data
      
  kafka:
    image: confluentinc/cp-kafka:7.2.1
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
      
  # Temporal工作流引擎
  temporal:
    image: temporalio/auto-setup:1.16.2
    environment:
      - DB=postgresql
      - DB_PORT=5432
      - POSTGRES_USER=postgres
      - POSTGRES_PWD=password
      - POSTGRES_SEEDS=postgres
    ports:
      - "7233:7233"
    depends_on:
      - postgres
      
  temporal-web:
    image: temporalio/web:1.15.0
    environment:
      - TEMPORAL_GRPC_ENDPOINT=temporal:7233
    ports:
      - "8088:8088"
    depends_on:
      - temporal
      
  # Consul服务发现
  consul:
    image: hashicorp/consul:1.12.3
    ports:
      - "8500:8500"
    volumes:
      - consul-data:/consul/data
    command: agent -server -bootstrap-expect=1 -ui -client=0.0.0.0
      
  # Jaeger分布式追踪
  jaeger:
    image: jaegertracing/all-in-one:1.36
    ports:
      - "16686:16686"  # UI
      - "14268:14268"  # Collector HTTP
      
  # Prometheus监控
  prometheus:
    image: prom/prometheus:v2.36.1
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml
      - prometheus-data:/prometheus
    ports:
      - "9090:9090"
    command:
      - '--config.file=/etc/prometheus/prometheus.yml'
      - '--storage.tsdb.path=/prometheus'
      - '--web.console.libraries=/usr/share/prometheus/console_libraries'
      - '--web.console.templates=/usr/share/prometheus/consoles'
      
  # Grafana可视化
  grafana:
    image: grafana/grafana:9.0.4
    ports:
      - "3000:3000"
    volumes:
      - grafana-data:/var/lib/grafana
      - ./grafana-dashboards:/etc/grafana/provisioning/dashboards
      - ./grafana-datasources:/etc/grafana/provisioning/datasources
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=admin
      - GF_USERS_ALLOW_SIGN_UP=false
    depends_on:
      - prometheus

volumes:
  postgres-data:
  redis-data:
  zookeeper-data:
  kafka-data:
  consul-data:
  prometheus-data:
  grafana-data:
```

### 5.2 Prometheus配置

```yaml
# prometheus.yml
global:
  scrape_interval: 15s
  evaluation_interval: 15s

scrape_configs:
  - job_name: 'order-service'
    consul_sd_configs:
      - server: 'consul:8500'
        services: ['order-service']
    metrics_path: /metrics
    
  - job_name: 'temporal'
    static_configs:
      - targets: ['temporal:9090']
        
  - job_name: 'node-exporter'
    static_configs:
      - targets: ['node-exporter:9100']

  - job_name: 'prometheus'
    static_configs:
      - targets: ['localhost:9090']
```

### 5.3 Kubernetes部署配置

```yaml
# order-service-deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: order-service
  labels:
    app: order-service
spec:
  replicas: 3
  selector:
    matchLabels:
      app: order-service
  strategy:
    type: RollingUpdate
    rollingUpdate:
      maxSurge: 1
      maxUnavailable: 0
  template:
    metadata:
      labels:
        app: order-service
      annotations:
        prometheus.io/scrape: "true"
        prometheus.io/path: "/metrics"
        prometheus.io/port: "8080"
    spec:
      containers:
      - name: order-service
        image: order-service:latest
        imagePullPolicy: Always
        ports:
        - containerPort: 8080
        env:
        - name: RUST_LOG
          value: "info"
        - name: APP__SERVER__PORT
          value: "8080"
        - name: APP__DATABASE__URL
          valueFrom:
            secretKeyRef:
              name: order-service-secrets
              key: database-url
        - name: APP__REDIS__URL
          valueFrom:
            secretKeyRef:
              name: order-service-secrets
              key: redis-url
        - name: APP__KAFKA__BROKERS
          value: "kafka-headless.kafka.svc.cluster.local:9092"
        - name: APP__TEMPORAL__URL
          value: "temporal-frontend.temporal.svc.cluster.local:7233"
        - name: APP__CONSUL__URL
          value: "http://consul-server.consul.svc.cluster.local:8500"
        resources:
          limits:
            cpu: "1"
            memory: "1Gi"
          requests:
            cpu: "500m"
            memory: "512Mi"
        readinessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 20
          periodSeconds: 10
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 30
          periodSeconds: 20
      securityContext:
        runAsNonRoot: true
        runAsUser: 10001
        fsGroup: 10001
      terminationGracePeriodSeconds: 60

---
# order-service-service.yaml
apiVersion: v1
kind: Service
metadata:
  name: order-service
  labels:
    app: order-service
spec:
  selector:
    app: order-service
  ports:
  - port: 80
    targetPort: 8080
    protocol: TCP
  type: ClusterIP

---
# order-service-hpa.yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: order-service
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: order-service
  minReplicas: 2
  maxReplicas: 10
  metrics:
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
  - type: Resource
    resource:
      name: memory
      target:
        type: Utilization
        averageUtilization: 80
```

## 6 五、系统启动与集成

### 6.1 应用启动序列

```rust
use std::sync::Arc;
use actix_web::{web, App, HttpServer, middleware};
use sqlx::postgres::PgPoolOptions;
use rdkafka::config::ClientConfig;
use opentelemetry::global;

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    // 1. 加载配置
    let config_manager = ConfigManager::from_file("config/config.toml")
        .expect("无法加载配置");
    let config = config_manager.get_config();
    
    // 2. 初始化日志和追踪
    init_tracer(&config.tracing.service_name, &config.tracing.jaeger_endpoint)
        .expect("无法初始化分布式追踪");
    
    tracing::info!("应用启动中...");
    
    // 3. 创建数据库连接池
    let db_pool = PgPoolOptions::new()
        .max_connections(config.database.max_connections)
        .min_connections(config.database.min_connections)
        .max_lifetime(config.database.max_lifetime)
        .idle_timeout(config.database.idle_timeout)
        .connect(&config.database.url)
        .await
        .expect("无法连接到数据库");
        
    // 执行迁移
    sqlx::migrate!("./migrations")
        .run(&db_pool)
        .await
        .expect("无法执行数据库迁移");
    
    // 4. 创建Redis客户端
    let redis_client = redis::Client::open(config.redis.url.as_str())
        .expect("无法创建Redis客户端");
        
    // 5. 创建Kafka生产者
    let kafka_producer = EventProducer::new(
        &config.kafka.brokers,
        &config.kafka.topic,
    ).expect("无法创建Kafka生产者");
    let kafka_producer = Arc::new(kafka_producer);
    
    // 6. 设置服务注册
    let service_registration = ServiceRegistration::new(
        &config.consul.url,
        &config.server.service_name,
        &config.server.host,
        config.server.port,
        "/health",
        "15s",
    ).expect("无法创建服务注册");
    
    service_registration.register().await
        .expect("无法注册服务");
        
    // 注册关闭钩子,确保服务优雅退出
    let service_registration_clone = service_registration.clone();
    ctrlc::set_handler(move || {
        let registration = service_registration_clone.clone();
        tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap()
            .block_on(async {
                tracing::info!("接收到终止信号,正在注销服务...");
                if let Err(e) = registration.deregister().await {
                    tracing::error!("注销服务失败: {:?}", e);
                }
                std::process::exit(0);
            });
    }).expect("无法设置Ctrl-C处理器");
    
    // 7. 创建服务发现
    let service_discovery = Arc::new(ServiceDiscovery::new(&config.consul.url)
        .expect("无法创建服务发现"));
        
    // 启动缓存刷新任务
    service_discovery.clone().start_cache_refresh(std::time::Duration::from_secs(60)).await;
    
    // 8. 创建外部服务工厂
    let external_service_factory = Arc::new(ExternalServiceFactory::new(
        config.external_services.clone(),
        service_discovery.clone(),
    ));
    
    // 9. 初始化命令总线
    let command_bus = Arc::new(CommandBus::new(kafka_producer.clone()));
    
    // 注册命令处理器
    let mut command_handlers = CommandHandlerRegistry::new();
    
    let create_order_handler = CreateOrderHandler::new(
        db_pool.clone(),
        external_service_factory.clone(),
    );
    command_handlers.register_handler(Box::new(create_order_handler));
    
    let cancel_order_handler = CancelOrderHandler::new(
        db_pool.clone(),
        external_service_factory.clone(),
    );
    command_handlers.register_handler(Box::new(cancel_order_handler));
    
    // 将处理器注册到命令总线
    command_bus.register_handlers(command_handlers).await;
    
    // 10. 初始化事件消费者
    let event_consumer = EventConsumer::new();
    
    // 注册事件处理器
    let order_read_model_updater = OrderReadModelUpdater::new(db_pool.clone());
    event_consumer.register_handler("order_created", Box::new(order_read_model_updater));
    
    let order_workflow_starter = OrderWorkflowStarter::new(
        TemporalClientFactory::new_client(&config.temporal.url)
            .await
            .expect("无法创建Temporal客户端")
    );
    event_consumer.register_handler("order_created", Box::new(order_workflow_starter));
    
    let inventory_reserver = InventoryReserver::new(
        external_service_factory.clone(),
    );
    event_consumer.register_handler("order_created", Box::new(inventory_reserver));
    
    // 启动事件消费
    let event_consumer_clone = event_consumer.clone();
    tokio::spawn(async move {
        if let Err(e) = event_consumer_clone.start(
            &["orders"],
            "order-service-group",
            &config.kafka.brokers,
        ).await {
            tracing::error!("事件消费者启动失败: {:?}", e);
        }
    });
    
    // 11. 初始化查询服务
    let metrics = Arc::new(Metrics::new());
    
    let order_query_service = Arc::new(OrderQueryService::new(
        db_pool.clone(),
        redis_client.clone(),
        metrics.clone(),
    ));
    
    // 12. 启动指标收集
    metrics.start_system_metrics_collector().await;
    
    // 13. 创建API控制器
    let order_controller = Arc::new(OrderController::new(
        order_query_service.clone(),
        command_bus.clone(),
    ));
    
    // 14. 创建健康检查服务
    let health_check_service = Arc::new(HealthCheckService::new(
        db_pool.clone(),
        redis_client.clone(),
        kafka_producer.clone(),
    ));
    
    // 15. 启动HTTP服务器
    tracing::info!("启动HTTP服务器在 {}:{}", config.server.host, config.server.port);
    
    HttpServer::new(move || {
        App::new()
            // 中间件
            .wrap(middleware::Logger::default())
            .wrap(middleware::Compress::default())
            .wrap(middleware::NormalizePath::trim())
            .wrap(TracingMiddleware)
            .wrap(ErrorHandlerMiddleware)
            .wrap(RequestMetricsMiddleware::new(metrics.clone()))
            
            // 应用状态
            .app_data(web::Data::new(order_controller.clone()))
            .app_data(web::Data::new(health_check_service.clone()))
            .app_data(web::Data::new(config.clone()))
            
            // 路由
            .configure(|cfg| register_routes(cfg, order_controller.clone()))
            
            // 健康检查
            .route("/health", web::get().to(health_check))
            
            // 指标端点
            .route("/metrics", web::get().to(metrics_handler))
    })
    .workers(config.server.workers)
    .bind(format!("{}:{}", config.server.host, config.server.port))?
    .run()
    .await
}

/// 健康检查处理器
async fn health_check(
    service: web::Data<Arc<HealthCheckService>>,
) -> impl Responder {
    match service.check_health().await {
        health_status if health_status.status == "up" => {
            HttpResponse::Ok().json(health_status)
        },
        health_status => {
            HttpResponse::ServiceUnavailable().json(health_status)
        }
    }
}

/// 指标端点处理器
async fn metrics_handler(
    metrics: web::Data<Arc<Metrics>>,
) -> impl Responder {
    let handle = metrics.get_prometheus_handler();
    HttpResponse::Ok()
        .content_type("text/plain")
        .body(handle.render())
}
```

### 6.2 Dockerfile

```dockerfile
FROM rust:1.62 as builder

# 创建新的空项目
WORKDIR /usr/src/app
RUN USER=root cargo new --bin order-service
WORKDIR /usr/src/app/order-service

# 复制项目清单
COPY Cargo.toml Cargo.lock ./

# 构建依赖项
RUN cargo build --release
RUN rm src/*.rs

# 复制源代码
COPY src ./src
COPY migrations ./migrations
COPY config ./config

# 构建应用
RUN cargo build --release

# 运行阶段
FROM debian:bullseye-slim

# 安装依赖
RUN apt-get update && apt-get install -y ca-certificates && rm -rf /var/lib/apt/lists/*

# 设置用户
RUN groupadd -r appuser && useradd -r -g appuser appuser

# 创建工作目录
WORKDIR /app

# 复制二进制文件和配置
COPY --from=builder /usr/src/app/order-service/target/release/order-service /app/
COPY --from=builder /usr/src/app/order-service/config /app/config
COPY --from=builder /usr/src/app/order-service/migrations /app/migrations

# 设置权限
RUN chown -R appuser:appuser /app
USER appuser

# 暴露端口
EXPOSE 8080

# 启动命令
CMD ["/app/order-service"]
```

## 7 六、总结与最佳实践

### 7.1 架构设计关键点

1. **领域驱动设计(DDD)**: 通过明确的限界上下文分离业务关注点,聚合根确保业务规则完整性

2. **事件驱动架构(EDA)**: 使用事件总线(Kafka)实现松耦合,提高系统弹性和扩展性

3. **命令查询责任分离(CQRS)**: 分离读写模型,优化查询性能并简化复杂业务逻辑

4. **事件溯源**: 保存所有领域事件,实现完整的系统状态审计和重建能力

5. **微服务架构**: 根据业务能力划分服务边界,实现独立部署和扩展

6. **工作流引擎**: 使用Temporal管理长时间运行的业务流程,提供持久性和故障恢复

### 7.2 Rust实现优势

1. **类型系统安全**: 利用Rust类型系统在编译时捕获错误,增强系统可靠性

2. **零成本抽象**: 实现高级抽象而不牺牲性能

3. **内存安全**: 无需垃圾回收即可保证内存安全,提高系统一致性和可预测性

4. **并发安全**: 通过所有权模型在编译时防止数据竞争和其他并发问题

5. **高效资源利用**: 低内存占用和CPU使用率,支持高吞吐量处理

### 7.3 集成开源库最佳实践

1. **分层抽象**: 使用抽象层封装第三方库,降低耦合并简化替换

   ```rust
   // 示例: 抽象数据库访问层
   #[async_trait]
   pub trait OrderRepository: Send + Sync {
       async fn save(&self, order: &Order) -> Result<(), RepositoryError>;
       async fn find_by_id(&self, id: &str) -> Result<Option<Order>, RepositoryError>;
       async fn find_by_customer(&self, customer_id: &str, limit: i64, offset: i64) -> Result<Vec<Order>, RepositoryError>;
   }
   
   // 具体实现使用sqlx
   pub struct PgOrderRepository {
       pool: PgPool,
   }
   
   #[async_trait]
   impl OrderRepository for PgOrderRepository {
       // 具体实现...
   }
   ```

2. **自动重连与断路器**: 对外部依赖应用断路器模式,防止级联故障

   ```rust
   // 示例: 对外部服务调用使用断路器
   async fn call_external_service(&self, request: &Request) -> Result<Response, ServiceError> {
       self.circuit_breaker.execute(|| async {
           self.client.send_request(request).await
       }).await.map_err(|e| match e {
           resilient::Error::CircuitOpen => ServiceError::ServiceUnavailable("服务暂时不可用".to_string()),
           resilient::Error::OperationError(inner) => inner,
       })
   }
   ```

3. **结合缓存提高性能**: 对频繁访问数据使用多级缓存策略

   ```rust
   // 示例: 缓存查询结果
   async fn get_cached_data(&self, key: &str) -> Result<Data, CacheError> {
       // 1. 尝试从本地缓存获取
       if let Some(data) = self.local_cache.get(key).await {
           return Ok(data);
       }

       // 2. 尝试从Redis获取
       let mut redis_conn = self.redis_client.get_async_connection().await?;
       if let Ok(data_string) = redis_conn.get::<_, String>(key).await {
           let data = serde_json::from_str(&data_string)?;
           self.local_cache.insert(key.to_string(), data.clone()).await;
           return Ok(data);
       }

       // 3. 从数据库获取
       let data = self.db_repository.get_data(key).await?;
       
       // 4. 更新缓存
       let data_string = serde_json::to_string(&data)?;
       let _: Result<(), _> = redis_conn.set_ex(key, data_string, 300).await;
       self.local_cache.insert(key.to_string(), data.clone()).await;
       
       Ok(data)
   }
   ```

4. **分布式追踪一致性**: 确保跨服务传递追踪上下文

   ```rust
   // 示例: 在服务调用中传递追踪上下文
   async fn call_service(&self, req: Request) -> Result<Response, Error> {
       let current_context = global::get_text_map_propagator(|propagator| {
           propagator.extract(&RequestHeaderCarrier(req.headers()))
       });
       
       let mut new_request = create_downstream_request(&req);
       global::get_text_map_propagator(|propagator| {
           propagator.inject_context(&current_context, &mut HeaderInjector(new_request.headers_mut()))
       });
       
       self.client.call(new_request).await
   }
   ```

### 7.4 最终架构特点

1. **高可靠性**: 通过断路器、重试、降级等弹性模式应对故障

2. **高可扩展性**: 事件驱动架构支持系统水平扩展

3. **可观测性**: 完整的日志、指标和分布式追踪

4. **一致性保证**: 通过事件溯源和Saga模式确保分布式一致性

5. **动态配置**: 支持在运行时调整系统参数和策略

6. **维护性**: 清晰的分层架构和依赖反转原则使系统易于理解和维护

通过以上设计和实现,系统能够满足您描述的复杂业务流程、长时间运行操作、高可靠性、多级分布式系统、动态策略调整、合规性和审计需求以及复杂异常处理等要求。
同时,利用Rust的类型系统和安全保证,为系统提供额外的可靠性和性能优势。
