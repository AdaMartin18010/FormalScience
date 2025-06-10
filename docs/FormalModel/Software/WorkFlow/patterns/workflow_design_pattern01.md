# Rust 工作流架构全面梳理

## 目录

- [Rust 工作流架构全面梳理](#rust-工作流架构全面梳理)
  - [目录](#目录)
  - [核心理论基础](#核心理论基础)
    - [1. 工作流模型与理论](#1-工作流模型与理论)
    - [2. 分布式系统理论](#2-分布式系统理论)
    - [3. 领域驱动设计](#3-领域驱动设计)
  - [架构设计层面](#架构设计层面)
    - [1. 分层架构](#1-分层架构)
    - [2. 六边形架构（端口与适配器）](#2-六边形架构端口与适配器)
    - [3. 事件驱动架构](#3-事件驱动架构)
  - [技术层面实现](#技术层面实现)
    - [1. 类型系统与所有权模型](#1-类型系统与所有权模型)
    - [2. 并发与异步处理](#2-并发与异步处理)
    - [3. 错误处理与恢复](#3-错误处理与恢复)
    - [4. 持久化与事件溯源](#4-持久化与事件溯源)
    - [5. 分布式协调](#5-分布式协调)
  - [最终综合架构](#最终综合架构)
    - [1. 多层架构图](#1-多层架构图)
    - [2. 核心组件交互图](#2-核心组件交互图)
    - [3. 核心API设计](#3-核心api设计)
  - [工作流执行实现详解](#工作流执行实现详解)
    - [1. 工作流引擎核心](#1-工作流引擎核心)
    - [2. 活动执行与协调](#2-活动执行与协调)
    - [3. 事件溯源与持久化](#3-事件溯源与持久化)
  - [数据流与业务集成](#数据流与业务集成)
    - [1. 数据转换与映射](#1-数据转换与映射)
    - [2. 企业业务流程集成](#2-企业业务流程集成)
    - [3. IoT设备集成](#3-iot设备集成)
  - [工作流监控与运维](#工作流监控与运维)
    - [1. 指标收集与监控](#1-指标收集与监控)
    - [2. 工作流可视化与管理](#2-工作流可视化与管理)
  - [工作流版本管理与迁移](#工作流版本管理与迁移)
  - [安全与权限模型](#安全与权限模型)
  - [整合与应用示例](#整合与应用示例)
  - [总结](#总结)

## 核心理论基础

### 1. 工作流模型与理论

工作流系统的基础理论主要来自以下几个领域：

1. **Petri网理论**：提供了对并发系统建模的数学基础
2. **π演算**：为分布式通信系统提供形式化描述
3. **时序逻辑**：用于描述系统中事件发生的时间顺序
4. **事件代数**：提供处理事件序列的数学框架

在我们的架构中，需要整合这些理论，建立一个形式化的工作流模型，包括：

```rust
/// 工作流网络定义
pub struct WorkflowNet {
    /// 工作流的所有节点
    pub nodes: Vec<WorkflowNode>,
    /// 节点间的转换关系
    pub transitions: Vec<Transition>,
    /// 初始标记（初始状态）
    pub initial_marking: Marking,
    /// 最终标记（最终状态）
    pub final_marking: Marking,
}

/// 工作流节点类型
pub enum WorkflowNodeType {
    /// 活动节点（执行具体任务）
    Activity,
    /// 条件节点（包含状态）
    Condition,
    /// 事件节点（处理外部事件）
    Event,
}

/// 工作流转换
pub struct Transition {
    /// 源节点ID
    pub source_id: String,
    /// 目标节点ID
    pub target_id: String,
    /// 转换条件表达式
    pub condition: Option<String>,
    /// 转换权重
    pub weight: u32,
}

/// 系统标记（状态）
pub struct Marking {
    /// 每个条件节点的标记数量
    pub tokens: HashMap<String, u32>,
}
```

### 2. 分布式系统理论

分布式工作流系统需要考虑以下核心理论：

1. **CAP理论**：在一致性、可用性和分区容忍性之间做出权衡
2. **CRDT**：用于分布式数据的冲突解决
3. **事件溯源**：通过事件序列重建系统状态
4. **最终一致性**：在分布式环境中保持数据一致性

架构中相应的设计：

```rust
/// 分布式一致性策略
pub enum ConsistencyStrategy {
    /// 强一致性（线性一致性）
    Strong,
    /// 因果一致性
    Causal,
    /// 最终一致性
    Eventual,
    /// 会话一致性
    Session,
}

/// 分布式系统配置
pub struct DistributedConfig {
    /// 一致性策略
    pub consistency_strategy: ConsistencyStrategy,
    /// 节点间通信超时
    pub communication_timeout: Duration,
    /// 是否启用领导者选举
    pub leader_election_enabled: bool,
    /// 心跳间隔
    pub heartbeat_interval: Duration,
    /// 失败检测阈值
    pub failure_detection_threshold: u32,
}
```

### 3. 领域驱动设计

工作流架构需要融合企业业务流程和IoT领域的特性，领域驱动设计提供了有效的方法：

1. **界限上下文**：分离不同领域的模型和语言
2. **聚合根**：确保领域对象的一致性
3. **领域事件**：捕获领域中的重要变化
4. **值对象与实体**：区分身份和值的领域概念

架构中相应的设计：

```rust
/// 领域模型
pub mod domain {
    pub mod enterprise {
        /// 企业业务流程上下文
        pub struct BusinessProcessContext {
            pub rules: Vec<BusinessRule>,
            pub documents: Vec<BusinessDocument>,
            pub approvals: Vec<Approval>,
        }
    }
    
    pub mod iot {
        /// IoT设备上下文
        pub struct DeviceContext {
            pub devices: Vec<Device>,
            pub sensors: Vec<Sensor>,
            pub telemetry: Vec<TelemetryData>,
        }
    }
    
    /// 共享内核
    pub mod shared {
        /// 领域事件
        pub struct DomainEvent {
            pub id: String,
            pub event_type: String,
            pub timestamp: DateTime<Utc>,
            pub payload: Value,
            pub metadata: HashMap<String, String>,
        }
    }
}
```

## 架构设计层面

### 1. 分层架构

工作流系统架构采用严格的分层设计，确保关注点分离：

```text
┌─────────────────────────────────┐
│       表示层 (Presentation)     │ ← REST API, GraphQL, CLI, UI
├─────────────────────────────────┤
│      应用层 (Application)       │ ← 工作流引擎、协调器
├─────────────────────────────────┤
│       领域层 (Domain)           │ ← 工作流模型、规则、活动
├─────────────────────────────────┤
│    基础设施层 (Infrastructure)   │ ← 持久化、消息队列、事件总线
└─────────────────────────────────┘
```

每层的核心职责：

1. **表示层**：提供用户接口和API
2. **应用层**：协调工作流执行，管理事务和会话
3. **领域层**：封装业务规则和工作流逻辑
4. **基础设施层**：提供技术能力支持

### 2. 六边形架构（端口与适配器）

为了更好地支持不同领域的集成需求，我们采用六边形架构：

```rust
/// 核心领域端口
pub trait WorkflowDomainPort {
    fn execute_activity(&self, context: &mut WorkflowContext, activity_id: &str) -> Result<(), Error>;
    fn evaluate_condition(&self, context: &WorkflowContext, condition: &str) -> Result<bool, Error>;
    fn process_event(&self, context: &mut WorkflowContext, event: &DomainEvent) -> Result<(), Error>;
}

/// 持久化端口
pub trait PersistencePort {
    fn save_workflow(&self, workflow: &Workflow) -> Result<(), Error>;
    fn load_workflow(&self, id: &str) -> Result<Workflow, Error>;
    fn save_event(&self, event: &DomainEvent) -> Result<(), Error>;
    fn load_events(&self, workflow_id: &str, from_sequence: u64) -> Result<Vec<DomainEvent>, Error>;
}

/// 通知端口
pub trait NotificationPort {
    fn send_notification(&self, recipient: &str, message: &NotificationMessage) -> Result<(), Error>;
}

/// IoT设备适配器
pub struct IoTDeviceAdapter {
    // 实现细节...
}

impl DevicePort for IoTDeviceAdapter {
    // 实现DevicePort接口...
}

/// SAP企业系统适配器
pub struct SapSystemAdapter {
    // 实现细节...
}

impl EnterpriseSystemPort for SapSystemAdapter {
    // 实现EnterpriseSystemPort接口...
}
```

### 3. 事件驱动架构

采用事件驱动架构提高系统的可扩展性和响应能力：

```rust
/// 事件总线
pub trait EventBus: Send + Sync {
    fn publish(&self, topic: &str, event: &DomainEvent) -> Result<(), Error>;
    fn subscribe(&self, topic: &str, handler: Box<dyn Fn(&DomainEvent) + Send + Sync>) -> Result<SubscriptionId, Error>;
    fn unsubscribe(&self, subscription_id: &SubscriptionId) -> Result<(), Error>;
}

/// 事件处理器注册
pub struct EventHandlerRegistry {
    handlers: HashMap<String, Vec<Box<dyn EventHandler>>>,
}

pub trait EventHandler: Send + Sync {
    fn event_type(&self) -> &str;
    fn handle(&self, event: &DomainEvent, context: &mut EventContext) -> Result<(), Error>;
}

/// 工作流事件监听器
pub struct WorkflowEventListener {
    event_bus: Arc<dyn EventBus>,
    workflow_engine: Arc<WorkflowEngine>,
    subscription_ids: Vec<SubscriptionId>,
}

impl WorkflowEventListener {
    pub fn new(event_bus: Arc<dyn EventBus>, workflow_engine: Arc<WorkflowEngine>) -> Self {
        let mut listener = Self {
            event_bus,
            workflow_engine,
            subscription_ids: Vec::new(),
        };
        
        listener.register_handlers();
        listener
    }
    
    fn register_handlers(&mut self) {
        // 注册工作流相关事件处理器
        let workflow_engine = self.workflow_engine.clone();
        let subscription_id = self.event_bus.subscribe(
            "workflow.events", 
            Box::new(move |event| {
                match event.event_type.as_str() {
                    "workflow.started" => {
                        // 处理工作流启动事件...
                    },
                    "activity.completed" => {
                        // 处理活动完成事件...
                    },
                    "workflow.suspended" => {
                        // 处理工作流暂停事件...
                    },
                    // 其他事件类型...
                    _ => {}
                }
            })
        ).unwrap();
        
        self.subscription_ids.push(subscription_id);
    }
}
```

## 技术层面实现

### 1. 类型系统与所有权模型

利用Rust的类型系统和所有权模型确保系统安全性：

```rust
/// 工作流上下文，使用借用检查器确保安全访问
pub struct WorkflowContext {
    // 不可变状态
    pub id: String,
    pub definition_id: String,
    pub created_at: DateTime<Utc>,
    
    // 可变状态，通过内部可变性安全共享
    state: RefCell<WorkflowState>,
    data: RefCell<HashMap<String, Value>>,
    
    // 历史记录，只能追加
    execution_history: RefCell<Vec<ExecutionRecord>>,
}

impl WorkflowContext {
    /// 安全地修改状态
    pub fn transition_to(&self, new_state: WorkflowState) -> Result<(), Error> {
        let mut state = self.state.borrow_mut();
        
        // 验证状态转换是否有效
        match *state {
            WorkflowState::Pending => {
                if new_state != WorkflowState::Running && new_state != WorkflowState::Cancelled {
                    return Err(Error::InvalidStateTransition);
                }
            },
            // 其他状态转换规则...
            _ => {}
        }
        
        // 执行转换
        *state = new_state;
        Ok(())
    }
    
    /// 记录执行历史
    pub fn record_execution(&self, activity_id: &str, result: ExecutionResult) {
        let mut history = self.execution_history.borrow_mut();
        history.push(ExecutionRecord {
            activity_id: activity_id.to_string(),
            timestamp: Utc::now(),
            result,
        });
    }
}
```

### 2. 并发与异步处理

充分利用Rust的`async`/`await`特性处理并发：

```rust
/// 异步工作流执行器
pub struct AsyncWorkflowExecutor {
    engine: Arc<WorkflowEngine>,
    task_pool: TaskPool,
}

impl AsyncWorkflowExecutor {
    /// 异步执行工作流
    pub async fn execute_workflow(&self, 
                                 workflow_id: &str, 
                                 initial_data: HashMap<String, Value>) -> Result<(), Error> {
        // 创建工作流上下文
        let context = self.engine.create_context(workflow_id, initial_data)?;
        
        // 获取起始节点
        let start_node = self.engine.get_start_node(workflow_id)?;
        
        // 执行工作流
        self.execute_node(&context, &start_node).await
    }
    
    /// 异步执行节点
    async fn execute_node(&self, context: &WorkflowContext, node_id: &str) -> Result<(), Error> {
        let node = self.engine.get_node(node_id)?;
        
        match node.node_type {
            NodeType::Activity => {
                // 执行活动
                self.execute_activity(context, node_id).await?;
                
                // 找到下一个节点
                let next_nodes = self.engine.get_next_nodes(node_id, context)?;
                
                // 执行下一个节点
                for next_node in next_nodes {
                    self.execute_node(context, &next_node).await?;
                }
            },
            NodeType::Parallel => {
                // 获取并行分支
                let branches = self.engine.get_parallel_branches(node_id)?;
                
                // 并行执行所有分支
                let mut tasks = Vec::new();
                for branch in branches {
                    let context = context.clone();
                    let executor = self.clone();
                    tasks.push(self.task_pool.spawn(async move {
                        executor.execute_node(&context, &branch).await
                    }));
                }
                
                // 等待所有分支完成
                let results = futures::future::join_all(tasks).await;
                
                // 处理结果
                for result in results {
                    if let Err(e) = result {
                        // 处理错误...
                        return Err(e);
                    }
                }
            },
            // 其他节点类型...
            _ => {}
        }
        
        Ok(())
    }
}
```

### 3. 错误处理与恢复

设计强大的错误处理机制：

```rust
/// 工作流错误类型
#[derive(Debug, thiserror::Error)]
pub enum WorkflowError {
    #[error("活动执行失败: {0}")]
    ActivityExecution(String, #[source] Option<Box<dyn std::error::Error + Send + Sync>>),
    
    #[error("持久化错误: {0}")]
    Persistence(String, #[source] Option<Box<dyn std::error::Error + Send + Sync>>),
    
    #[error("状态错误: {0}")]
    State(String),
    
    #[error("超时: {0}")]
    Timeout(String),
    
    #[error("未找到: {0}")]
    NotFound(String),
    
    #[error("权限错误: {0}")]
    Authorization(String),
    
    #[error("配置错误: {0}")]
    Configuration(String),
    
    #[error("外部系统错误: {service}:{message}")]
    ExternalSystem {
        service: String,
        message: String,
        #[source]
        source: Option<Box<dyn std::error::Error + Send + Sync>>,
    },
}

/// 错误恢复策略
pub enum RecoveryStrategy {
    /// 立即重试
    RetryImmediate {
        max_attempts: u32,
    },
    
    /// 带退避的重试
    RetryWithBackoff {
        max_attempts: u32,
        initial_delay: Duration,
        backoff_factor: f64,
        max_delay: Duration,
    },
    
    /// 补偿事务
    Compensate {
        compensation_activity: String,
    },
    
    /// 跳过失败活动
    Skip,
    
    /// 失败整个工作流
    FailWorkflow,
    
    /// 手动干预
    ManualIntervention {
        notification_recipients: Vec<String>,
    },
}

/// 恢复管理器
pub struct RecoveryManager {
    strategies: HashMap<String, RecoveryStrategy>,
    default_strategy: RecoveryStrategy,
}

impl RecoveryManager {
    /// 处理错误并尝试恢复
    pub async fn handle_error(&self, 
                             context: &WorkflowContext, 
                             activity_id: &str, 
                             error: &WorkflowError) -> Result<RecoveryAction, WorkflowError> {
        // 记录错误
        log::error!("Activity {} failed: {}", activity_id, error);
        
        // 获取恢复策略
        let strategy = self.strategies.get(activity_id)
            .unwrap_or(&self.default_strategy);
        
        // 应用恢复策略
        match strategy {
            RecoveryStrategy::RetryImmediate { max_attempts } => {
                let attempts = context.get_retry_count(activity_id);
                if attempts < *max_attempts {
                    return Ok(RecoveryAction::Retry { delay: None });
                } else {
                    return Ok(RecoveryAction::Fail);
                }
            },
            RecoveryStrategy::RetryWithBackoff { max_attempts, initial_delay, backoff_factor, max_delay } => {
                let attempts = context.get_retry_count(activity_id);
                if attempts < *max_attempts {
                    let delay = initial_delay.as_millis() as f64 * backoff_factor.powi(attempts as i32);
                    let delay = Duration::from_millis(delay.min(max_delay.as_millis() as f64) as u64);
                    return Ok(RecoveryAction::Retry { delay: Some(delay) });
                } else {
                    return Ok(RecoveryAction::Fail);
                }
            },
            // 其他策略...
            _ => Ok(RecoveryAction::Fail),
        }
    }
}
```

### 4. 持久化与事件溯源

实现坚固的持久化机制：

```rust
/// 事件溯源仓库
pub struct EventSourcedRepository<T> {
    event_store: Box<dyn EventStore>,
    entity_type: PhantomData<T>,
}

impl<T: AggregateRoot> EventSourcedRepository<T> {
    /// 保存聚合根
    pub async fn save(&self, aggregate: &T) -> Result<(), Error> {
        // 获取未提交事件
        let events = aggregate.uncommitted_events();
        
        if events.is_empty() {
            return Ok(());
        }
        
        // 获取流ID
        let stream_id = format!("{}-{}", T::AGGREGATE_TYPE, aggregate.id());
        
        // 获取当前版本
        let expected_version = aggregate.version();
        
        // 附加事件
        self.event_store.append_events(&stream_id, events, expected_version).await?;
        
        // 标记事件为已提交
        aggregate.mark_events_as_committed();
        
        Ok(())
    }
    
    /// 加载聚合根
    pub async fn load(&self, id: &str) -> Result<T, Error> {
        // 获取流ID
        let stream_id = format!("{}-{}", T::AGGREGATE_TYPE, id);
        
        // 加载事件
        let events = self.event_store.read_events(&stream_id, 0, u64::MAX).await?;
        
        if events.is_empty() {
            return Err(Error::NotFound(format!("找不到ID为{}的{}", id, T::AGGREGATE_TYPE)));
        }
        
        // 重建聚合根
        let mut aggregate = T::new(id);
        aggregate.apply_events(events);
        
        Ok(aggregate)
    }
}

/// 快照存储
pub trait SnapshotStore: Send + Sync {
    async fn save_snapshot<T: Serialize + Send + Sync>(&self, 
                                                     aggregate_type: &str,
                                                     aggregate_id: &str, 
                                                     snapshot: &T, 
                                                     version: u64) -> Result<(), Error>;
                                                    
    async fn load_latest_snapshot<T: DeserializeOwned>(&self,
                                                     aggregate_type: &str,
                                                     aggregate_id: &str) -> Result<Option<(T, u64)>, Error>;
}

/// 混合存储仓库（事件溯源+快照）
pub struct HybridRepository<T> {
    event_store: Box<dyn EventStore>,
    snapshot_store: Box<dyn SnapshotStore>,
    entity_type: PhantomData<T>,
    snapshot_frequency: u64,
}

impl<T: AggregateRoot + Serialize + DeserializeOwned> HybridRepository<T> {
    /// 加载聚合根（优先使用快照）
    pub async fn load(&self, id: &str) -> Result<T, Error> {
        // 尝试加载快照
        let snapshot_result = self.snapshot_store.load_latest_snapshot::<T>(
            T::AGGREGATE_TYPE, id
        ).await?;
        
        if let Some((snapshot, snapshot_version)) = snapshot_result {
            // 找到快照，只加载更新的事件
            let stream_id = format!("{}-{}", T::AGGREGATE_TYPE, id);
            let events = self.event_store.read_events(&stream_id, snapshot_version + 1, u64::MAX).await?;
            
            // 应用事件到快照
            let mut aggregate = snapshot;
            aggregate.apply_events(events);
            
            return Ok(aggregate);
        }
        
        // 没有快照，从头加载所有事件
        let stream_id = format!("{}-{}", T::AGGREGATE_TYPE, id);
        let events = self.event_store.read_events(&stream_id, 0, u64::MAX).await?;
        
        if events.is_empty() {
            return Err(Error::NotFound(format!("找不到ID为{}的{}", id, T::AGGREGATE_TYPE)));
        }
        
        // 重建聚合根
        let mut aggregate = T::new(id);
        aggregate.apply_events(events);
        
        Ok(aggregate)
    }
    
    /// 保存聚合根（定期创建快照）
    pub async fn save(&self, aggregate: &T) -> Result<(), Error> {
        // 获取未提交事件
        let events = aggregate.uncommitted_events();
        
        if events.is_empty() {
            return Ok(());
        }
        
        // 获取流ID
        let stream_id = format!("{}-{}", T::AGGREGATE_TYPE, aggregate.id());
        
        // 获取当前版本
        let expected_version = aggregate.version();
        
        // 附加事件
        self.event_store.append_events(&stream_id, events, expected_version).await?;
        
        // 检查是否需要创建快照
        if aggregate.version() % self.snapshot_frequency == 0 {
            self.snapshot_store.save_snapshot(
                T::AGGREGATE_TYPE,
                aggregate.id(),
                aggregate,
                aggregate.version()
            ).await?;
        }
        
        // 标记事件为已提交
        aggregate.mark_events_as_committed();
        
        Ok(())
    }
}
```

### 5. 分布式协调

实现分布式系统中的协调和一致性：

```rust
/// 分布式锁管理器
pub struct DistributedLockManager {
    redis_client: redis::Client,
    lock_ttl: Duration,
    retry_count: u32,
    retry_delay: Duration,
}

impl DistributedLockManager {
    /// 获取分布式锁
    pub async fn acquire_lock(&self, resource: &str, owner: &str) -> Result<DistributedLock, Error> {
        let mut conn = self.redis_client.get_async_connection().await?;
        let key = format!("lock:{}", resource);
        
        for attempt in 0..self.retry_count {
            // 尝试使用SETNX设置锁
            let result: bool = redis::cmd("SET")
                .arg(&key)
                .arg(owner)
                .arg("NX")
                .arg("PX")
                .arg(self.lock_ttl.as_millis() as usize)
                .query_async(&mut conn)
                .await?;
            
            if result {
                // 成功获取锁
                return Ok(DistributedLock {
                    resource: resource.to_string(),
                    owner: owner.to_string(),
                    ttl: self.lock_ttl,
                    lock_manager: self,
                });
            }
            
            // 如果是最后一次尝试，则返回错误
            if attempt == self.retry_count - 1 {
                return Err(Error::LockAcquisition(format!("无法获取资源'{}'的锁", resource)));
            }
            
            // 等待后重试
            tokio::time::sleep(self.retry_delay).await;
        }
        
        Err(Error::LockAcquisition(format!("无法获取资源'{}'的锁", resource)))
    }
    
    /// 释放分布式锁
    pub async fn release_lock(&self, resource: &str, owner: &str) -> Result<bool, Error> {
        let mut conn = self.redis_client.get_async_connection().await?;
        let key = format!("lock:{}", resource);
        
        // 使用Lua脚本确保只释放自己的锁
        let script = r"
            if redis.call('get', KEYS[1]) == ARGV[1] then
                return redis.call('del', KEYS[1])
            else
                return 0
            end
        ";
        
        let result: i32 = redis::Script::new(script)
            .key(&key)
            .arg(owner)
            .invoke_async(&mut conn)
            .await?;
        
        Ok(result == 1)
    }
}

/// 分布式锁
pub struct DistributedLock<'a> {
    resource: String,
    owner: String,
    ttl: Duration,
    lock_manager: &'a DistributedLockManager,
}

impl<'a> DistributedLock<'a> {
    /// 延长锁的生命周期
    pub async fn extend(&self) -> Result<(), Error> {
        let mut conn = self.lock_manager.redis_client.get_async_connection().await?;
        let key = format!("lock:{}", self.resource);
        
        // 使用Lua脚本延长锁
        let script = r"
            if redis.call('get', KEYS[1]) == ARGV[1] then
                return redis.call('pexpire', KEYS[1], ARGV[2])
            else
                return 0
            end
        ";
        
        let result: i32 = redis::Script::new(script)
            .key(&key)
            .arg(&self.owner)
            .arg(self.ttl.as_millis() as usize)
            .invoke_async(&mut conn)
            .await?;
        
        if result == 1 {
            Ok(())
        } else {
            Err(Error::LockExtension(format!("无法延长资源'{}'的锁", self.resource)))
        }
    }
}

impl<'a> Drop for DistributedLock<'a> {
    fn drop(&mut self) {
        // 创建一个运行时来执行异步释放操作
        let rt = tokio::runtime::Runtime::new().unwrap();
        rt.block_on(async {
            if let Err(e) = self.lock_manager.release_lock(&self.resource, &self.owner).await {
                log::error!("释放锁时出错: {}", e);
            }
        });
    }
}
```

## 最终综合架构

综合以上所有方面，我们提出一个完整的Rust工作流架构：

### 1. 多层架构图

```text
┌─────────────────────────────────────────────────────────────────┐
│                          表示层 (Presentation)                     │
│  ┌───────────┐ ┌───────────┐ ┌───────────┐ ┌───────────────────┐ │
│  │  REST API  │ │  GraphQL  │ │    CLI    │ │ Web 可视化设计器   │ │
│  └───────────┘ └───────────┘ └───────────┘ └───────────────────┘ │
├─────────────────────────────────────────────────────────────────┤
│                          应用层 (Application)                     │
│  ┌───────────┐ ┌───────────┐ ┌───────────┐ ┌───────────────────┐ │
│  │ 工作流引擎  │ │ 执行协调器 │ │ 安全管理器 │ │   监控与遥测     │ │
│  └───────────┘ └───────────┘ └───────────┘ └───────────────────┘ │
├─────────────────────────────────────────────────────────────────┤
│                          领域层 (Domain)                          │
│  ┌───────────┐ ┌───────────┐ ┌───────────┐ ┌───────────────────┐ │
│  │ 工作流模型  │ │ 活动实现   │ │ 业务规则   │ │   领域服务      │ │
│  └───────────┘ └───────────┘ └───────────┘ └───────────────────┘ │
├─────────────────────────────────────────────────────────────────┤
│                       基础设施层 (Infrastructure)                  │
│  ┌───────────┐ ┌───────────┐ ┌───────────┐ ┌───────────────────┐ │
│  │ 持久化存储  │ │ 事件总线   │ │ 分布式锁  │ │   外部系统集成    │ │
│  └───────────┘ └───────────┘ └───────────┘ └───────────────────┘ │
└─────────────────────────────────────────────────────────────────┘
```

### 2. 核心组件交互图

```text
┌─────────────┐    定义    ┌─────────────┐
│ 工作流定义器  │◄─────────►│  工作流模型  │
└─────────────┘            └──────┬──────┘
                                  │
                                  │ 创建实例
                                  ▼
┌─────────────┐    执行    ┌─────────────┐    调用    ┌─────────────┐
│ 工作流引擎   │◄─────────►│  工作流实例   │◄─────────►│    活动     │
└──────┬──────┘            └──────┬──────┘            └──────┬──────┘
       │                          │                          │
       │ 协调                      │ 管理                     │ 访问
       ▼                          ▼                          ▼
┌─────────────┐    通知    ┌─────────────┐    集成    ┌─────────────┐
│  事件总线    │◄─────────►│  持久化存储   │◄─────────►│  外部系统   │
└─────────────┘            └─────────────┘            └─────────────┘
```

### 3. 核心API设计

```rust
/// 工作流系统API
pub mod workflow_api {
    /// 工作流定义相关API
    pub mod definition {
        /// 创建工作流定义
        pub async fn create_workflow_definition(
            definition: WorkflowDefinition,
        ) -> Result<WorkflowDefinitionId, Error>;
        
        /// 更新工作流定义
        pub async fn update_workflow_definition(
            id: WorkflowDefinitionId,
            definition: WorkflowDefinition,
        ) -> Result<(), Error>;
        
        /// 获取工作流定义
        pub async fn get_workflow_definition(
            id: WorkflowDefinitionId,
        ) -> Result<WorkflowDefinition, Error>;
        
        /// 删除工作流定义
        pub async fn delete_workflow_definition(
            id: WorkflowDefinitionId,
        ) -> Result<(), Error>;
        
        /// 验证工作流定义
        pub async fn validate_workflow_definition(
            definition: &WorkflowDefinition,
        ) -> Result<ValidationResult, Error>;
    }
    
    /// 工作流实例相关API
    pub mod instance {
        /// 创建工作流实例
        pub async fn create_workflow_instance(
            definition_id: WorkflowDefinitionId,
            initial_data: HashMap<String, Value>,
        ) -> Result<WorkflowInstanceId, Error>;
        
        /// 获取工作流实例状态
        pub async fn get_workflow_instance(
            id: WorkflowInstanceId,
        ) -> Result<WorkflowInstance, Error>;
        
        /// 暂停工作流实例
        pub async fn suspend_workflow_instance(
            id: WorkflowInstanceId,
        ) -> Result<(), Error>;
        
        /// 恢复工作流实例
        pub async fn resume_workflow_instance(
            id: WorkflowInstanceId,
        ) -> Result<(), Error>;
        
        /// 终止工作流实例
        pub async fn terminate_workflow_instance(
            id: WorkflowInstanceId,
            reason: String,
        ) -> Result<(), Error>;
    }
    
    /// 活动相关API
    pub mod activity {
        /// 注册活动类型
        pub async fn register_activity_type(
            activity_type: ActivityTypeDefinition,
        ) -> Result<(), Error>;
        
        /// 获取活动类型
        pub async fn get_activity_type(
            type_name: &str,
        ) -> Result<ActivityTypeDefinition, Error>;
        
        /// 获取活动执行历史
        pub async fn get_activity_execution_history(
            workflow_instance_id: WorkflowInstanceId,
            activity_id: &str,
        ) -> Result<Vec<ActivityExecution>, Error>;
    }
    
    /// 监控相关API
    pub mod monitoring {
        /// 订阅工作流事件
        pub async fn subscribe_to_workflow_events(
            event_types: Vec<String>,
            callback_url: &str,
        ) -> Result<SubscriptionId, Error>;
        
        /// 获取工作流统计信息
        pub async fn get_workflow_statistics(
            time_range: TimeRange,
            filters: HashMap<String, String>,
        ) -> Result<WorkflowStatistics, Error>;
        
        /// 获取系统健康状态
        pub async fn get_system_health() -> Result<SystemHealth, Error>;
    }
}
```

## 工作流执行实现详解

### 1. 工作流引擎核心

```rust
/// 工作流引擎 - 系统核心组件
pub struct WorkflowEngine {
    definition_repository: Arc<dyn WorkflowDefinitionRepository>,
    instance_repository: Arc<dyn WorkflowInstanceRepository>,
    activity_registry: Arc<ActivityRegistry>,
    event_bus: Arc<dyn EventBus>,
    lock_manager: Arc<dyn LockManager>,
    execution_coordinator: Arc<ExecutionCoordinator>,
    recovery_manager: Arc<RecoveryManager>,
    security_manager: Option<Arc<SecurityManager>>,
}

impl WorkflowEngine {
    /// 创建新的工作流引擎
    pub fn new(
        definition_repository: Arc<dyn WorkflowDefinitionRepository>,
        instance_repository: Arc<dyn WorkflowInstanceRepository>,
        activity_registry: Arc<ActivityRegistry>,
        event_bus: Arc<dyn EventBus>,
        lock_manager: Arc<dyn LockManager>,
        recovery_manager: Arc<RecoveryManager>,
    ) -> Self {
        let execution_coordinator = Arc::new(ExecutionCoordinator::new(
            activity_registry.clone(),
            event_bus.clone(),
            lock_manager.clone(),
        ));
        
        Self {
            definition_repository,
            instance_repository,
            activity_registry,
            event_bus,
            lock_manager,
            execution_coordinator,
            recovery_manager,
            security_manager: None,
        }
    }
    
    /// 设置安全管理器
    pub fn with_security_manager(mut self, security_manager: Arc<SecurityManager>) -> Self {
        self.security_manager = Some(security_manager);
        self
    }
    
    /// 创建工作流实例
    pub async fn create_workflow_instance(
        &self,
        definition_id: &str,
        initial_data: HashMap<String, Value>,
        user_context: Option<&UserContext>,
    ) -> Result<WorkflowInstance, WorkflowError> {
        // 1. 检查权限
        if let Some(user) = user_context {
            if let Some(security) = &self.security_manager {
                let resource = WorkflowResource {
                    resource_type: ResourceType::WorkflowDefinition,
                    resource_id: definition_id.to_string(),
                    owner_id: None,
                };
                
                security.check_permission(user, Permission::Execute, &resource).await?;
            }
        }
        
        // 2. 加载工作流定义
        let definition = self.definition_repository.get_definition(definition_id).await?;
        
        // 3. 验证定义
        if !definition.is_valid() {
            return Err(WorkflowError::InvalidDefinition(
                format!("工作流定义 {} 无效", definition_id)
            ));
        }
        
        // 4. 创建实例ID
        let instance_id = Uuid::new_v4().to_string();
        
        // 5. 创建工作流上下文
        let context = WorkflowContext {
            instance_id: instance_id.clone(),
            definition_id: definition_id.to_string(),
            state: WorkflowState::Created,
            data: initial_data,
            created_at: Utc::now(),
            created_by: user_context.map(|u| u.user_id.clone()),
            execution_path: Vec::new(),
            error_stack: Vec::new(),
            metadata: HashMap::new(),
        };
        
        // 6. 创建工作流实例
        let instance = WorkflowInstance {
            id: instance_id.clone(),
            definition_id: definition_id.to_string(),
            state: WorkflowState::Created,
            context,
            version: 0,
        };
        
        // 7. 保存工作流实例
        self.instance_repository.save_instance(&instance).await?;
        
        // 8. 发布工作流创建事件
        self.event_bus.publish(
            "workflow.created",
            &WorkflowEvent {
                id: Uuid::new_v4().to_string(),
                workflow_instance_id: instance_id.clone(),
                event_type: "workflow.created".to_string(),
                timestamp: Utc::now(),
                data: json!({
                    "definition_id": definition_id,
                    "instance_id": instance_id,
                }),
                user_id: user_context.map(|u| u.user_id.clone()),
            }
        ).await?;
        
        Ok(instance)
    }
    
    /// 启动工作流实例
    pub async fn start_workflow_instance(
        &self,
        instance_id: &str,
        user_context: Option<&UserContext>,
    ) -> Result<(), WorkflowError> {
        // 1. 检查权限
        if let Some(user) = user_context {
            if let Some(security) = &self.security_manager {
                let resource = WorkflowResource {
                    resource_type: ResourceType::WorkflowInstance,
                    resource_id: instance_id.to_string(),
                    owner_id: None,
                };
                
                security.check_permission(user, Permission::Execute, &resource).await?;
            }
        }
        
        // 2. 获取工作流实例锁
        let lock = self.lock_manager.acquire_lock(
            &format!("workflow:instance:{}", instance_id),
            "workflow_engine",
            Duration::from_secs(30)
        ).await?;
        
        // 3. 加载工作流实例
        let mut instance = self.instance_repository.get_instance(instance_id).await?;
        
        // 4. 检查工作流状态
        if instance.state != WorkflowState::Created {
            return Err(WorkflowError::InvalidState(
                format!("工作流实例 {} 状态为 {:?}，无法启动", instance_id, instance.state)
            ));
        }
        
        // 5. 加载工作流定义
        let definition = self.definition_repository
            .get_definition(&instance.definition_id)
            .await?;
        
        // 6. 更新工作流状态
        instance.state = WorkflowState::Running;
        instance.context.state = WorkflowState::Running;
        
        // 7. 保存工作流实例
        self.instance_repository.save_instance(&instance).await?;
        
        // 8. 发布工作流启动事件
        self.event_bus.publish(
            "workflow.started",
            &WorkflowEvent {
                id: Uuid::new_v4().to_string(),
                workflow_instance_id: instance_id.to_string(),
                event_type: "workflow.started".to_string(),
                timestamp: Utc::now(),
                data: json!({
                    "definition_id": instance.definition_id,
                    "instance_id": instance_id,
                }),
                user_id: user_context.map(|u| u.user_id.clone()),
            }
        ).await?;
        
        // 9. 获取起始节点
        let start_node_id = definition.get_start_node_id()?;
        
        // 10. 执行工作流
        let execution_future = self.execution_coordinator.execute_node(
            &instance,
            &definition,
            start_node_id,
        );
        
        // 11. 释放锁并异步执行
        drop(lock);
        tokio::spawn(async move {
            if let Err(e) = execution_future.await {
                log::error!("执行工作流 {} 时发生错误: {}", instance_id, e);
            }
        });
        
        Ok(())
    }
    
    // 其他工作流管理方法...
}
```

### 2. 活动执行与协调

```rust
/// 执行协调器 - 负责执行工作流活动和控制流
pub struct ExecutionCoordinator {
    activity_registry: Arc<ActivityRegistry>,
    event_bus: Arc<dyn EventBus>,
    lock_manager: Arc<dyn LockManager>,
}

impl ExecutionCoordinator {
    /// 执行工作流节点
    pub async fn execute_node(
        &self,
        instance: &WorkflowInstance,
        definition: &WorkflowDefinition,
        node_id: &str,
    ) -> Result<(), WorkflowError> {
        // 1. 获取节点定义
        let node = definition.get_node(node_id)?;
        
        // 2. 根据节点类型执行不同逻辑
        match node.node_type {
            NodeType::Activity => {
                self.execute_activity(instance, definition, node_id).await?;
            },
            NodeType::Gateway => {
                self.execute_gateway(instance, definition, node_id).await?;
            },
            NodeType::Event => {
                self.execute_event(instance, definition, node_id).await?;
            },
            NodeType::SubWorkflow => {
                self.execute_sub_workflow(instance, definition, node_id).await?;
            },
        }
        
        Ok(())
    }
    
    /// 执行活动节点
    async fn execute_activity(
        &self,
        instance: &WorkflowInstance,
        definition: &WorkflowDefinition,
        node_id: &str,
    ) -> Result<(), WorkflowError> {
        // 1. 获取活动定义
        let activity_def = definition.get_activity(node_id)?;
        
        // 2. 获取活动执行器
        let activity_executor = self.activity_registry.get_executor(&activity_def.activity_type)?;
        
        // 3. 创建活动执行上下文
        let activity_context = ActivityContext {
            workflow_instance_id: instance.id.clone(),
            activity_id: node_id.to_string(),
            activity_type: activity_def.activity_type.clone(),
            input: activity_def.input.clone(),
            workflow_data: instance.context.data.clone(),
        };
        
        // 4. 获取活动执行锁
        let lock_key = format!("workflow:activity:{}:{}", instance.id, node_id);
        let lock = self.lock_manager.acquire_lock(&lock_key, "executor", Duration::from_secs(60)).await?;
        
        // 5. 发布活动开始事件
        self.event_bus.publish(
            "activity.started",
            &WorkflowEvent {
                id: Uuid::new_v4().to_string(),
                workflow_instance_id: instance.id.clone(),
                event_type: "activity.started".to_string(),
                timestamp: Utc::now(),
                data: json!({
                    "activity_id": node_id,
                    "activity_type": activity_def.activity_type,
                }),
                user_id: None,
            }
        ).await?;
        
        // 6. 执行活动
        let result = activity_executor.execute(&activity_context).await;
        
        // 7. 处理执行结果
        match result {
            Ok(output) => {
                // 8. 发布活动完成事件
                self.event_bus.publish(
                    "activity.completed",
                    &WorkflowEvent {
                        id: Uuid::new_v4().to_string(),
                        workflow_instance_id: instance.id.clone(),
                        event_type: "activity.completed".to_string(),
                        timestamp: Utc::now(),
                        data: json!({
                            "activity_id": node_id,
                            "activity_type": activity_def.activity_type,
                            "output": output,
                        }),
                        user_id: None,
                    }
                ).await?;
                
                // 9. 更新工作流数据
                // 注：这里需要先获取工作流实例锁，更新状态和数据
                
                // 10. 获取后继节点
                let next_nodes = definition.get_outgoing_nodes(node_id)?;
                
                // 11. 释放活动锁
                drop(lock);
                
                // 12. 执行后继节点
                for next_node in next_nodes {
                    self.execute_node(instance, definition, &next_node).await?;
                }
                
                Ok(())
            },
            Err(e) => {
                // 处理活动执行错误
                self.handle_activity_error(instance, definition, node_id, &e).await
            }
        }
    }
    
    /// 处理活动执行错误
    async fn handle_activity_error(
        &self,
        instance: &WorkflowInstance,
        definition: &WorkflowDefinition,
        node_id: &str,
        error: &WorkflowError,
    ) -> Result<(), WorkflowError> {
        // 1. 获取活动定义
        let activity_def = definition.get_activity(node_id)?;
        
        // 2. 发布活动失败事件
        self.event_bus.publish(
            "activity.failed",
            &WorkflowEvent {
                id: Uuid::new_v4().to_string(),
                workflow_instance_id: instance.id.clone(),
                event_type: "activity.failed".to_string(),
                timestamp: Utc::now(),
                data: json!({
                    "activity_id": node_id,
                    "activity_type": activity_def.activity_type,
                    "error": error.to_string(),
                }),
                user_id: None,
            }
        ).await?;
        
        // 3. 获取错误处理策略
        let error_handler = activity_def.error_handler.clone().unwrap_or_default();
        
        // 4. 根据错误处理策略执行
        match error_handler.strategy {
            ErrorStrategy::Retry { max_attempts, backoff } => {
                // 实现重试逻辑
                let attempts = self.get_retry_count(instance, node_id).await?;
                if attempts < max_attempts {
                    // 计算重试延迟
                    let delay = match backoff {
                        BackoffStrategy::Fixed(duration) => duration,
                        BackoffStrategy::Exponential { initial, factor, max } => {
                            let calculated = initial * factor.powi(attempts as i32);
                            if calculated > max { max } else { calculated }
                        }
                    };
                    
                    // 安排重试
                    tokio::time::sleep(delay).await;
                    self.increment_retry_count(instance, node_id).await?;
                    return self.execute_activity(instance, definition, node_id).await;
                } else {
                    // 重试次数用尽，检查是否有后备路径
                    if let Some(fallback_path) = error_handler.fallback_path.clone() {
                        return self.execute_node(instance, definition, &fallback_path).await;
                    } else {
                        // 无后备路径，视为工作流失败
                        return self.handle_workflow_failure(instance, error).await;
                    }
                }
            },
            ErrorStrategy::Compensate { activity_id } => {
                // 执行补偿活动
                self.execute_node(instance, definition, &activity_id).await?;
                
                // 然后处理失败流程
                if let Some(fallback_path) = error_handler.fallback_path.clone() {
                    return self.execute_node(instance, definition, &fallback_path).await;
                } else {
                    return self.handle_workflow_failure(instance, error).await;
                }
            },
            ErrorStrategy::Continue => {
                // 忽略错误，继续执行后续节点
                let next_nodes = definition.get_outgoing_nodes(node_id)?;
                for next_node in next_nodes {
                    self.execute_node(instance, definition, &next_node).await?;
                }
                Ok(())
            },
            ErrorStrategy::Fail => {
                // 直接失败
                self.handle_workflow_failure(instance, error).await
            }
        }
    }
    
    /// 处理工作流失败
    async fn handle_workflow_failure(
        &self,
        instance: &WorkflowInstance,
        error: &WorkflowError,
    ) -> Result<(), WorkflowError> {
        // 1. 获取工作流实例锁
        let lock_key = format!("workflow:instance:{}", instance.id);
        let _lock = self.lock_manager.acquire_lock(&lock_key, "executor", Duration::from_secs(30)).await?;
        
        // 2. 发布工作流失败事件
        self.event_bus.publish(
            "workflow.failed",
            &WorkflowEvent {
                id: Uuid::new_v4().to_string(),
                workflow_instance_id: instance.id.clone(),
                event_type: "workflow.failed".to_string(),
                timestamp: Utc::now(),
                data: json!({
                    "error": error.to_string(),
                }),
                user_id: None,
            }
        ).await?;
        
        // 3. 更新工作流状态为失败
        // 注：这里需要先获取最新工作流实例，更新状态
        
        // 返回原始错误
        Err(error.clone())
    }
    
    // 其他执行方法（网关、事件、子工作流等）...
}
```

### 3. 事件溯源与持久化

```rust
/// 事件溯源工作流实例仓库
pub struct EventSourcedWorkflowRepository {
    event_store: Arc<dyn EventStore>,
    snapshot_store: Arc<dyn SnapshotStore>,
    snapshot_frequency: u32,
}

impl EventSourcedWorkflowRepository {
    /// 创建新的事件溯源仓库
    pub fn new(
        event_store: Arc<dyn EventStore>,
        snapshot_store: Arc<dyn SnapshotStore>,
        snapshot_frequency: u32,
    ) -> Self {
        Self {
            event_store,
            snapshot_store,
            snapshot_frequency,
        }
    }
}

impl WorkflowInstanceRepository for EventSourcedWorkflowRepository {
    /// 保存工作流实例
    async fn save_instance(&self, instance: &WorkflowInstance) -> Result<(), WorkflowError> {
        // 1. 获取工作流的事件流ID
        let stream_id = format!("workflow:{}", instance.id);
        
        // 2. 创建工作流实例事件
        let event = WorkflowInstanceEvent {
            workflow_id: instance.id.clone(),
            event_type: "workflow.state_changed".to_string(),
            state: instance.state.clone(),
            data: instance.context.data.clone(),
            metadata: instance.context.metadata.clone(),
            timestamp: Utc::now(),
            version: instance.version + 1,
        };
        
        // 3. 序列化事件
        let event_data = serde_json::to_value(&event)
            .map_err(|e| WorkflowError::Serialization(e.to_string()))?;
        
        // 4. 将事件附加到事件流
        self.event_store.append_to_stream(
            &stream_id,
            instance.version,
            vec![EventData {
                event_type: "WorkflowInstanceEvent".to_string(),
                data: event_data,
                metadata: json!({}),
            }]
        ).await?;
        
        // 5. 检查是否需要创建快照
        if instance.version % self.snapshot_frequency as u64 == 0 {
            self.snapshot_store.save_snapshot(
                &instance.id,
                serde_json::to_value(instance)
                    .map_err(|e| WorkflowError::Serialization(e.to_string()))?,
                instance.version,
            ).await?;
        }
        
        Ok(())
    }
    
    /// 加载工作流实例
    async fn get_instance(&self, instance_id: &str) -> Result<WorkflowInstance, WorkflowError> {
        // 1. 尝试从快照存储加载最新快照
        let snapshot_result = self.snapshot_store.get_latest_snapshot(instance_id).await?;
        
        if let Some((snapshot_data, snapshot_version)) = snapshot_result {
            // 2. 从快照恢复工作流实例
            let mut instance: WorkflowInstance = serde_json::from_value(snapshot_data)
                .map_err(|e| WorkflowError::Deserialization(e.to_string()))?;
            
            // 3. 获取快照之后的所有事件
            let stream_id = format!("workflow:{}", instance_id);
            let events = self.event_store.read_stream_events(&stream_id, snapshot_version + 1, u64::MAX).await?;
            
            // 4. 依次应用事件
            for event_data in events {
                if event_data.event_type == "WorkflowInstanceEvent" {
                    let workflow_event: WorkflowInstanceEvent = serde_json::from_value(event_data.data)
                        .map_err(|e| WorkflowError::Deserialization(e.to_string()))?;
                    
                    // 应用事件到工作流实例
                    instance.state = workflow_event.state;
                    instance.context.data = workflow_event.data;
                    instance.context.metadata = workflow_event.metadata;
                    instance.version = workflow_event.version;
                }
            }
            
            Ok(instance)
        } else {
            // 5. 没有快照，从头开始读取所有事件
            let stream_id = format!("workflow:{}", instance_id);
            let events = self.event_store.read_stream_events(&stream_id, 0, u64::MAX).await?;
            
            if events.is_empty() {
                return Err(WorkflowError::NotFound(format!("找不到工作流实例: {}", instance_id)));
            }
            
            // 6. 从事件重建工作流实例
            let mut instance = WorkflowInstance {
                id: instance_id.to_string(),
                definition_id: "".to_string(),
                state: WorkflowState::Created,
                context: WorkflowContext {
                    instance_id: instance_id.to_string(),
                    definition_id: "".to_string(),
                    state: WorkflowState::Created,
                    data: HashMap::new(),
                    create
# Rust工作流架构全面梳理（续）

## 事件溯源与持久化（续）

```rust
/// 事件溯源工作流实例仓库（续）
impl WorkflowInstanceRepository for EventSourcedWorkflowRepository {
    /// 加载工作流实例（续）
    async fn get_instance(&self, instance_id: &str) -> Result<WorkflowInstance, WorkflowError> {
        // 前面部分代码...
        
        // 6. 从事件重建工作流实例
        let mut instance = WorkflowInstance {
            id: instance_id.to_string(),
            definition_id: "".to_string(),
            state: WorkflowState::Created,
            context: WorkflowContext {
                instance_id: instance_id.to_string(),
                definition_id: "".to_string(),
                state: WorkflowState::Created,
                data: HashMap::new(),
                created_at: Utc::now(),
                created_by: None,
                execution_path: Vec::new(),
                error_stack: Vec::new(),
                metadata: HashMap::new(),
            },
            version: 0,
        };
        
        // 7. 依次应用事件
        for event_data in events {
            if event_data.event_type == "WorkflowInstanceEvent" {
                let workflow_event: WorkflowInstanceEvent = serde_json::from_value(event_data.data)
                    .map_err(|e| WorkflowError::Deserialization(e.to_string()))?;
                
                // 更新工作流实例的基本信息
                if instance.definition_id.is_empty() {
                    if let Some(definition_id) = workflow_event.metadata.get("definition_id") {
                        instance.definition_id = definition_id.as_str()
                            .ok_or_else(|| WorkflowError::InvalidData("definition_id".into()))?
                            .to_string();
                        instance.context.definition_id = instance.definition_id.clone();
                    }
                }
                
                if let Some(created_at) = workflow_event.metadata.get("created_at") {
                    if let Ok(timestamp) = DateTime::parse_from_rfc3339(
                        created_at.as_str()
                            .ok_or_else(|| WorkflowError::InvalidData("created_at".into()))?
                    ) {
                        instance.context.created_at = timestamp.with_timezone(&Utc);
                    }
                }
                
                if let Some(created_by) = workflow_event.metadata.get("created_by") {
                    instance.context.created_by = created_by.as_str().map(|s| s.to_string());
                }
                
                // 应用事件到工作流实例
                instance.state = workflow_event.state;
                instance.context.state = workflow_event.state.clone();
                instance.context.data = workflow_event.data;
                instance.context.metadata = workflow_event.metadata;
                instance.version = workflow_event.version;
                
                // 处理特殊事件类型
                if let Some(event_name) = workflow_event.metadata.get("event_name") {
                    match event_name.as_str() {
                        Some("node_executed") => {
                            if let Some(node_id) = workflow_event.metadata.get("node_id") {
                                if let Some(id) = node_id.as_str() {
                                    instance.context.execution_path.push(id.to_string());
                                }
                            }
                        },
                        Some("error_occurred") => {
                            if let Some(error) = workflow_event.metadata.get("error") {
                                if let Some(err) = error.as_str() {
                                    instance.context.error_stack.push(err.to_string());
                                }
                            }
                        },
                        _ => {}
                    }
                }
            }
        }
        
        // 8. 验证工作流实例
        if instance.definition_id.is_empty() {
            return Err(WorkflowError::InvalidData("找不到工作流定义ID".into()));
        }
        
        Ok(instance)
    }
    
    /// 删除工作流实例
    async fn delete_instance(&self, instance_id: &str) -> Result<(), WorkflowError> {
        // 软删除：添加删除事件
        let stream_id = format!("workflow:{}", instance_id);
        
        // 先检查实例是否存在
        let stream_info = self.event_store.get_stream_info(&stream_id).await?;
        if stream_info.is_none() {
            return Err(WorkflowError::NotFound(format!("找不到工作流实例: {}", instance_id)));
        }
        
        // 获取当前版本
        let current_version = stream_info.unwrap().last_event_number;
        
        // 创建删除事件
        let delete_event = WorkflowInstanceEvent {
            workflow_id: instance_id.to_string(),
            event_type: "workflow.deleted".to_string(),
            state: WorkflowState::Deleted,
            data: HashMap::new(),
            metadata: json!({
                "deleted_at": Utc::now().to_rfc3339(),
            }),
            timestamp: Utc::now(),
            version: current_version + 1,
        };
        
        // 序列化事件
        let event_data = serde_json::to_value(&delete_event)
            .map_err(|e| WorkflowError::Serialization(e.to_string()))?;
        
        // 附加删除事件
        self.event_store.append_to_stream(
            &stream_id,
            current_version,
            vec![EventData {
                event_type: "WorkflowInstanceEvent".to_string(),
                data: event_data,
                metadata: json!({"final": true}),
            }]
        ).await?;
        
        // 删除快照
        self.snapshot_store.delete_snapshots(instance_id).await?;
        
        Ok(())
    }
    
    /// 查询工作流实例
    async fn query_instances(&self, query: &WorkflowQuery) -> Result<Vec<WorkflowInstance>, WorkflowError> {
        // 实现查询功能...
        // 这里需要根据具体的事件存储实现来支持查询
        // 可以考虑使用投影(projection)来构建查询视图
        
        // 示例：假设有一个查询API
        let mut instances = Vec::new();
        
        // 构建查询条件
        let mut conditions = Vec::new();
        
        if let Some(definition_id) = &query.definition_id {
            conditions.push(format!("definition_id = '{}'", definition_id));
        }
        
        if let Some(state) = &query.state {
            conditions.push(format!("state = '{:?}'", state));
        }
        
        if let Some(from) = &query.created_after {
            conditions.push(format!("created_at >= '{}'", from.to_rfc3339()));
        }
        
        if let Some(to) = &query.created_before {
            conditions.push(format!("created_at <= '{}'", to.to_rfc3339()));
        }
        
        // 执行查询
        let query_string = conditions.join(" AND ");
        let results = self.event_store.query_streams(&query_string, query.limit).await?;
        
        // 对于每个结果，加载完整实例
        for stream_id in results {
            if let Some(instance_id) = stream_id.strip_prefix("workflow:") {
                match self.get_instance(instance_id).await {
                    Ok(instance) => {
                        // 检查是否已被删除
                        if instance.state != WorkflowState::Deleted {
                            instances.push(instance);
                        }
                    },
                    Err(e) => {
                        log::warn!("加载工作流实例 {} 时出错: {}", instance_id, e);
                    }
                }
            }
        }
        
        Ok(instances)
    }
}
```

## 数据流与业务集成

### 1. 数据转换与映射

```rust
/// 数据转换器 - 处理数据流的转换逻辑
pub trait DataTransformer: Send + Sync {
    /// 转换器类型名称
    fn type_name(&self) -> &str;
    
    /// 执行数据转换
    fn transform(&self, input: &Value) -> Result<Value, WorkflowError>;
    
    /// 验证输入数据
    fn validate_input(&self, input: &Value) -> Result<(), WorkflowError> {
        Ok(())
    }
}

/// JSON路径提取器 - 从JSON中提取数据
pub struct JsonPathExtractor {
    path_expressions: HashMap<String, String>,
}

impl DataTransformer for JsonPathExtractor {
    fn type_name(&self) -> &str {
        "json_path_extractor"
    }
    
    fn transform(&self, input: &Value) -> Result<Value, WorkflowError> {
        self.validate_input(input)?;
        
        let mut result = json!({});
        
        for (output_field, path_expr) in &self.path_expressions {
            let selector = jsonpath::selector(input, path_expr)
                .map_err(|e| WorkflowError::DataTransformation(
                    format!("无效的JSON路径表达式 '{}': {}", path_expr, e)
                ))?;
            
            if let Some(value) = selector.first() {
                result[output_field] = value.clone();
            } else {
                // 路径未找到任何值，设置为null
                result[output_field] = Value::Null;
            }
        }
        
        Ok(result)
    }
    
    fn validate_input(&self, input: &Value) -> Result<(), WorkflowError> {
        if !input.is_object() && !input.is_array() {
            return Err(WorkflowError::InvalidInput(
                "JSON路径提取器需要对象或数组输入".into()
            ));
        }
        
        Ok(())
    }
}

/// 模板渲染器 - 使用模板和数据生成输出
pub struct TemplateRenderer {
    template: String,
    engine: TemplateEngine,
}

enum TemplateEngine {
    Handlebars(handlebars::Handlebars<'static>),
    Tera(tera::Tera),
}

impl DataTransformer for TemplateRenderer {
    fn type_name(&self) -> &str {
        "template_renderer"
    }
    
    fn transform(&self, input: &Value) -> Result<Value, WorkflowError> {
        self.validate_input(input)?;
        
        // 渲染模板
        let rendered = match &self.engine {
            TemplateEngine::Handlebars(hbs) => {
                hbs.render_template(&self.template, input)
                    .map_err(|e| WorkflowError::DataTransformation(
                        format!("模板渲染失败: {}", e)
                    ))?
            },
            TemplateEngine::Tera(tera) => {
                let context = match input {
                    Value::Object(map) => {
                        let mut context = tera::Context::new();
                        for (k, v) in map {
                            context.insert(k, v);
                        }
                        context
                    },
                    _ => {
                        let mut context = tera::Context::new();
                        context.insert("data", input);
                        context
                    }
                };
                
                tera.render_str(&self.template, &context)
                    .map_err(|e| WorkflowError::DataTransformation(
                        format!("模板渲染失败: {}", e)
                    ))?
            }
        };
        
        // 尝试解析为JSON，如果失败则作为字符串返回
        match serde_json::from_str::<Value>(&rendered) {
            Ok(json_value) => Ok(json_value),
            Err(_) => Ok(Value::String(rendered)),
        }
    }
}

/// 数据映射器 - 将源数据映射到目标结构
pub struct DataMapper {
    mappings: Vec<FieldMapping>,
}

struct FieldMapping {
    source_path: String,
    target_path: String,
    transform: Option<TransformFunction>,
}

enum TransformFunction {
    ToUpper,
    ToLower,
    NumberFormat(String),
    DateFormat { source_format: String, target_format: String },
    Custom(Box<dyn Fn(&Value) -> Result<Value, WorkflowError> + Send + Sync>),
}

impl DataTransformer for DataMapper {
    fn type_name(&self) -> &str {
        "data_mapper"
    }
    
    fn transform(&self, input: &Value) -> Result<Value, WorkflowError> {
        self.validate_input(input)?;
        
        let mut result = json!({});
        
        for mapping in &self.mappings {
            // 提取源值
            let source_selector = jsonpath::selector(input, &mapping.source_path)
                .map_err(|e| WorkflowError::DataTransformation(
                    format!("无效的源路径表达式 '{}': {}", mapping.source_path, e)
                ))?;
            
            if let Some(source_value) = source_selector.first() {
                // 应用转换函数
                let transformed_value = if let Some(transform) = &mapping.transform {
                    match transform {
                        TransformFunction::ToUpper => {
                            if let Some(s) = source_value.as_str() {
                                Value::String(s.to_uppercase())
                            } else {
                                source_value.clone()
                            }
                        },
                        TransformFunction::ToLower => {
                            if let Some(s) = source_value.as_str() {
                                Value::String(s.to_lowercase())
                            } else {
                                source_value.clone()
                            }
                        },
                        TransformFunction::NumberFormat(format) => {
                            if let Some(n) = source_value.as_f64() {
                                // 使用指定格式格式化数字
                                Value::String(format_number(n, format))
                            } else {
                                source_value.clone()
                            }
                        },
                        TransformFunction::DateFormat { source_format, target_format } => {
                            if let Some(s) = source_value.as_str() {
                                // 解析日期并重新格式化
                                let date = parse_date(s, source_format)?;
                                Value::String(format_date(&date, target_format))
                            } else {
                                source_value.clone()
                            }
                        },
                        TransformFunction::Custom(func) => {
                            func(source_value)?
                        }
                    }
                } else {
                    // 无转换，直接使用源值
                    source_value.clone()
                };
                
                // 使用点表示法构建嵌套对象路径
                set_nested_value(&mut result, &mapping.target_path, transformed_value);
            }
        }
        
        Ok(result)
    }
}

/// 设置嵌套JSON对象的值
fn set_nested_value(obj: &mut Value, path: &str, value: Value) {
    let parts: Vec<&str> = path.split('.').collect();
    let mut current = obj;
    
    for (i, part) in parts.iter().enumerate() {
        if i == parts.len() - 1 {
            // 最后一个部分，设置值
            if let Value::Object(map) = current {
                map.insert(part.to_string(), value);
            }
            return;
        } else {
            // 中间路径，确保存在对象
            if let Value::Object(map) = current {
                if !map.contains_key(*part) {
                    map.insert(part.to_string(), json!({}));
                }
                if let Some(next) = map.get_mut(*part) {
                    current = next;
                }
            }
        }
    }
}
```

### 2. 企业业务流程集成

```rust
/// 企业业务流程集成
pub trait EnterpriseSystemConnector: Send + Sync {
    /// 连接器类型名称
    fn connector_type(&self) -> &str;
    
    /// 连接到企业系统
    async fn connect(&self) -> Result<(), WorkflowError>;
    
    /// 断开连接
    async fn disconnect(&self) -> Result<(), WorkflowError>;
    
    /// 执行业务操作
    async fn execute_operation(
        &self,
        operation: &str,
        parameters: &Value
    ) -> Result<Value, WorkflowError>;
    
    /// 查询业务数据
    async fn query_data(
        &self,
        query: &str,
        parameters: &Value
    ) -> Result<Value, WorkflowError>;
    
    /// 检查系统健康状态
    async fn check_health(&self) -> Result<SystemHealth, WorkflowError>;
}

/// SAP系统连接器
pub struct SapConnector {
    connection_string: String,
    credentials: Credentials,
    client: Option<SapClient>,
    timeout: Duration,
}

impl EnterpriseSystemConnector for SapConnector {
    fn connector_type(&self) -> &str {
        "sap_connector"
    }
    
    async fn connect(&self) -> Result<(), WorkflowError> {
        // 实现SAP连接逻辑...
        Ok(())
    }
    
    async fn disconnect(&self) -> Result<(), WorkflowError> {
        // 实现断开连接逻辑...
        Ok(())
    }
    
    async fn execute_operation(
        &self,
        operation: &str,
        parameters: &Value
    ) -> Result<Value, WorkflowError> {
        // 确保已连接
        if self.client.is_none() {
            self.connect().await?;
        }
        
        // 执行SAP BAPI/函数模块
        match operation {
            "create_sales_order" => {
                // 验证参数
                let customer_id = parameters.get("customer_id")
                    .and_then(|v| v.as_str())
                    .ok_or_else(|| WorkflowError::MissingParameter("customer_id".into()))?;
                
                let items = parameters.get("items")
                    .and_then(|v| v.as_array())
                    .ok_or_else(|| WorkflowError::MissingParameter("items".into()))?;
                
                // 调用SAP API创建销售订单
                // ... 实现细节
                
                Ok(json!({
                    "order_id": "SO-123456",
                    "status": "created",
                    "timestamp": Utc::now().to_rfc3339(),
                }))
            },
            "check_inventory" => {
                // 验证参数
                let material_id = parameters.get("material_id")
                    .and_then(|v| v.as_str())
                    .ok_or_else(|| WorkflowError::MissingParameter("material_id".into()))?;
                
                let plant = parameters.get("plant")
                    .and_then(|v| v.as_str())
                    .ok_or_else(|| WorkflowError::MissingParameter("plant".into()))?;
                
                // 调用SAP API检查库存
                // ... 实现细节
                
                Ok(json!({
                    "material_id": material_id,
                    "plant": plant,
                    "available_quantity": 100,
                    "reserved_quantity": 20,
                    "timestamp": Utc::now().to_rfc3339(),
                }))
            },
            _ => Err(WorkflowError::UnsupportedOperation(format!(
                "不支持的SAP操作: {}", operation
            ))),
        }
    }
    
    async fn query_data(
        &self,
        query: &str,
        parameters: &Value
    ) -> Result<Value, WorkflowError> {
        // 实现查询逻辑...
        match query {
            "customer_info" => {
                let customer_id = parameters.get("customer_id")
                    .and_then(|v| v.as_str())
                    .ok_or_else(|| WorkflowError::MissingParameter("customer_id".into()))?;
                
                // 查询客户信息
                // ... 实现细节
                
                Ok(json!({
                    "customer_id": customer_id,
                    "name": "示例客户",
                    "credit_limit": 100000,
                    "outstanding_balance": 25000,
                    "credit_status": "good",
                }))
            },
            _ => Err(WorkflowError::UnsupportedQuery(format!(
                "不支持的SAP查询: {}", query
            ))),
        }
    }
    
    async fn check_health(&self) -> Result<SystemHealth, WorkflowError> {
        // 检查SAP系统连接
        // ... 实现细节
        
        Ok(SystemHealth {
            status: HealthStatus::Healthy,
            details: json!({
                "connection": "active",
                "response_time_ms": 120,
                "system_info": {
                    "version": "SAP S/4HANA 2021",
                    "instance": "PRD",
                }
            }),
            last_checked: Utc::now(),
        })
    }
}

/// 企业系统活动实现
pub struct EnterpriseSystemActivity {
    connector_type: String,
    operation: String,
    parameter_mapping: HashMap<String, String>,
    result_mapping: Option<String>,
    timeout: Duration,
}

impl Activity for EnterpriseSystemActivity {
    fn activity_type(&self) -> &str {
        "enterprise_system_activity"
    }
    
    async fn execute(
        &self,
        context: &ActivityContext
    ) -> Result<Value, WorkflowError> {
        // 1. 获取连接器
        let connector_registry = get_connector_registry()?;
        let connector = connector_registry.get_connector(&self.connector_type)?;
        
        // 2. 构建操作参数
        let mut parameters = json!({});
        
        for (param_name, data_path) in &self.parameter_mapping {
            // 从上下文中提取参数值
            let value = extract_value_from_context(context, data_path)?;
            parameters[param_name] = value;
        }
        
        // 3. 执行操作
        let start_time = Instant::now();
        let operation_result = tokio::time::timeout(
            self.timeout,
            connector.execute_operation(&self.operation, &parameters)
        ).await
        .map_err(|_| WorkflowError::Timeout(format!(
            "执行企业系统操作 {} 超时", self.operation
        )))??;
        
        let duration = start_time.elapsed();
        
        // 4. 处理结果映射
        let result = if let Some(result_path) = &self.result_mapping {
            // 将结果存储到指定路径
            json!({
                result_path: operation_result,
                "_metadata": {
                    "operation": self.operation,
                    "connector_type": self.connector_type,
                    "duration_ms": duration.as_millis(),
                    "timestamp": Utc::now().to_rfc3339(),
                }
            })
        } else {
            // 直接返回结果
            json!({
                "result": operation_result,
                "_metadata": {
                    "operation": self.operation,
                    "connector_type": self.connector_type,
                    "duration_ms": duration.as_millis(),
                    "timestamp": Utc::now().to_rfc3339(),
                }
            })
        };
        
        Ok(result)
    }
}
```

### 3. IoT设备集成

```rust
/// IoT设备连接器
pub trait IoTDeviceConnector: Send + Sync {
    /// 连接器类型名称
    fn connector_type(&self) -> &str;
    
    /// 连接到IoT设备或平台
    async fn connect(&self) -> Result<(), WorkflowError>;
    
    /// 断开连接
    async fn disconnect(&self) -> Result<(), WorkflowError>;
    
    /// 发送命令到设备
    async fn send_command(
        &self,
        device_id: &str,
        command: &str,
        parameters: &Value
    ) -> Result<Value, WorkflowError>;
    
    /// 查询设备状态
    async fn query_device_state(
        &self,
        device_id: &str,
        metrics: Option<Vec<String>>
    ) -> Result<DeviceState, WorkflowError>;
    
    /// 订阅设备遥测数据
    async fn subscribe_to_telemetry(
        &self,
        device_ids: Vec<String>,
        callback: Box<dyn Fn(DeviceTelemetry) + Send + Sync>
    ) -> Result<SubscriptionId, WorkflowError>;
    
    /// 取消订阅
    async fn unsubscribe(
        &self,
        subscription_id: &SubscriptionId
    ) -> Result<(), WorkflowError>;
}

/// MQTT IoT设备连接器
pub struct MqttDeviceConnector {
    broker_url: String,
    client_id: String,
    credentials: Option<Credentials>,
    topic_prefix: String,
    qos: u8,
    client: Option<AsyncClient>,
}

impl IoTDeviceConnector for MqttDeviceConnector {
    fn connector_type(&self) -> &str {
        "mqtt_connector"
    }
    
    async fn connect(&self) -> Result<(), WorkflowError> {
        // 创建MQTT客户端选项
        let mut mqtt_options = MqttOptions::new(
            &self.client_id,
            &self.broker_url,
            1883 // 默认端口
        );
        
        // 设置凭据
        if let Some(creds) = &self.credentials {
            match creds {
                Credentials::UsernamePassword { username, password } => {
                    mqtt_options.set_credentials(username, password);
                },
                Credentials::CertificateKey { cert_path, key_path, ca_path } => {
                    mqtt_options.set_tls(
                        rumqttc::TlsConfiguration::Simple {
                            ca: ca_path.as_ref().map(|p| p.to_string()),
                            alpn: None,
                            client_auth: Some((cert_path.to_string(), key_path.to_string())),
                        }
                    );
                },
                _ => return Err(WorkflowError::InvalidCredentials(
                    "MQTT连接器不支持此凭据类型".into()
                )),
            }
        }
        
        // 设置QoS
        mqtt_options.set_clean_session(true);
        mqtt_options.set_keep_alive(Duration::from_secs(30));
        
        // 创建MQTT客户端
        let (client, mut event_loop) = AsyncClient::new(mqtt_options, 10);
        
        // 异步连接处理
        tokio::spawn(async move {
            loop {
                match event_loop.poll().await {
                    Ok(notification) => {
                        match notification {
                            rumqttc::Event::Incoming(incoming) => {
                                match incoming {
                                    rumqttc::Packet::Publish(publish) => {
                                        // 处理接收到的消息
                                        // ...
                                    },
                                    _ => {}
                                }
                            },
                            rumqttc::Event::Outgoing(_) => {
                                // 处理出站事件
                            }
                        }
                    },
                    Err(e) => {
                        log::error!("MQTT连接错误: {}", e);
                        // 尝试重新连接
                        // ...
                        break;
                    }
                }
            }
        });
        
        // 存储客户端
        self.client.replace(client);
        
        Ok(())
    }
    
    async fn disconnect(&self) -> Result<(), WorkflowError> {
        if let Some(client) = &self.client {
            client.disconnect().await
                .map_err(|e| WorkflowError::ConnectionError(format!(
                    "断开MQTT连接失败: {}", e
                )))?;
        }
        
        Ok(())
    }
    
    async fn send_command(
        &self,
        device_id: &str,
        command: &str,
        parameters: &Value
    ) -> Result<Value, WorkflowError> {
        let client = match &self.client {
            Some(c) => c,
            None => return Err(WorkflowError::ConnectionError("MQTT客户端未连接".into())),
        };
        
        // 构建命令主题
        let topic = format!("{}/devices/{}/commands/{}", 
                           self.topic_prefix, device_id, command);
        
        // 序列化命令参数
        let payload = serde_json::to_string(parameters)
            .map_err(|e| WorkflowError::Serialization(format!(
                "无法序列化命令参数: {}", e
            )))?;
        
        // 发送命令
        client.publish(
            topic,
            QoS::from_u8(self.qos).unwrap_or(Qo
# Rust工作流架构全面梳理（续）

## IoT设备集成（续）

```rust
/// MQTT IoT设备连接器（续）
impl IoTDeviceConnector for MqttDeviceConnector {
    // 前面部分代码...
    
    async fn send_command(
        &self,
        device_id: &str,
        command: &str,
        parameters: &Value
    ) -> Result<Value, WorkflowError> {
        let client = match &self.client {
            Some(c) => c,
            None => return Err(WorkflowError::ConnectionError("MQTT客户端未连接".into())),
        };
        
        // 构建命令主题
        let topic = format!("{}/devices/{}/commands/{}", 
                           self.topic_prefix, device_id, command);
        
        // 序列化命令参数
        let payload = serde_json::to_string(parameters)
            .map_err(|e| WorkflowError::Serialization(format!(
                "无法序列化命令参数: {}", e
            )))?;
        
        // 发送命令
        client.publish(
            topic,
            QoS::from_u8(self.qos).unwrap_or(QoS::AtMostOnce),
            false,
            payload
        ).await.map_err(|e| WorkflowError::CommunicationError(format!(
            "发送MQTT命令失败: {}", e
        )))?;
        
        // 返回命令发送确认
        Ok(json!({
            "status": "sent",
            "device_id": device_id,
            "command": command,
            "timestamp": Utc::now().to_rfc3339(),
        }))
    }
    
    async fn query_device_state(
        &self,
        device_id: &str,
        metrics: Option<Vec<String>>
    ) -> Result<DeviceState, WorkflowError> {
        let client = match &self.client {
            Some(c) => c,
            None => return Err(WorkflowError::ConnectionError("MQTT客户端未连接".into())),
        };
        
        // 创建唯一请求ID
        let request_id = Uuid::new_v4().to_string();
        
        // 构建状态请求主题
        let request_topic = format!("{}/devices/{}/status/get", 
                                  self.topic_prefix, device_id);
        
        // 构建回复主题
        let response_topic = format!("{}/devices/{}/status/response/{}", 
                                   self.topic_prefix, device_id, request_id);
        
        // 设置临时回复处理
        let (tx, rx) = tokio::sync::oneshot::channel::<Result<DeviceState, WorkflowError>>();
        
        // 订阅回复主题
        client.subscribe(&response_topic, QoS::AtLeastOnce).await
            .map_err(|e| WorkflowError::CommunicationError(format!(
                "无法订阅设备状态回复主题: {}", e
            )))?;
        
        // 设置临时消息处理器
        // 注意：这里简化了实现，实际上需要一个更完善的消息处理系统
        let response_handler = tokio::spawn(async move {
            // 这里应该有一个超时机制
            let timeout = Duration::from_secs(10);
            let result = tokio::time::timeout(timeout, async {
                // 实际实现中，这里应该接收MQTT消息并解析
                // 简化版：模拟设备状态响应
                DeviceState {
                    device_id: device_id.to_string(),
                    online: true,
                    metrics: json!({
                        "temperature": 22.5,
                        "humidity": 45.0,
                        "battery": 85,
                    }),
                    last_updated: Utc::now(),
                }
            }).await;
            
            match result {
                Ok(state) => tx.send(Ok(state)),
                Err(_) => tx.send(Err(WorkflowError::Timeout(
                    format!("获取设备{}状态超时", device_id)
                ))),
            }
        });
        
        // 发送状态请求
        let request_payload = json!({
            "request_id": request_id,
            "response_topic": response_topic,
            "metrics": metrics,
        });
        
        client.publish(
            request_topic,
            QoS::AtLeastOnce,
            false,
            serde_json::to_string(&request_payload)?
        ).await.map_err(|e| WorkflowError::CommunicationError(format!(
            "发送设备状态请求失败: {}", e
        )))?;
        
        // 等待响应
        let result = rx.await
            .map_err(|e| WorkflowError::InternalError(format!(
                "等待设备状态响应时出错: {}", e
            )))?;
        
        // 取消订阅
        client.unsubscribe(&response_topic).await
            .map_err(|e| WorkflowError::CommunicationError(format!(
                "取消订阅设备状态回复主题失败: {}", e
            )))?;
        
        result
    }
    
    async fn subscribe_to_telemetry(
        &self,
        device_ids: Vec<String>,
        callback: Box<dyn Fn(DeviceTelemetry) + Send + Sync>
    ) -> Result<SubscriptionId, WorkflowError> {
        let client = match &self.client {
            Some(c) => c,
            None => return Err(WorkflowError::ConnectionError("MQTT客户端未连接".into())),
        };
        
        // 生成订阅ID
        let subscription_id = Uuid::new_v4().to_string();
        
        // 订阅每个设备的遥测主题
        for device_id in &device_ids {
            let telemetry_topic = format!("{}/devices/{}/telemetry", 
                                        self.topic_prefix, device_id);
            
            client.subscribe(&telemetry_topic, QoS::AtLeastOnce).await
                .map_err(|e| WorkflowError::CommunicationError(format!(
                    "无法订阅设备遥测主题: {}", e
                )))?;
                
            // 在实际实现中，应该维护订阅回调的映射关系
            // 这里简化了实现
        }
        
        // 返回订阅ID
        Ok(SubscriptionId(subscription_id))
    }
    
    async fn unsubscribe(
        &self,
        subscription_id: &SubscriptionId
    ) -> Result<(), WorkflowError> {
        // 在实际实现中，应该根据订阅ID取消相应的MQTT主题订阅
        // 这里简化了实现
        Ok(())
    }
}

/// IoT设备活动
pub struct IoTDeviceActivity {
    device_id: String,
    connector_type: String,
    action_type: IoTActionType,
    parameters: HashMap<String, String>,
    result_path: Option<String>,
    timeout: Duration,
}

enum IoTActionType {
    SendCommand {
        command: String,
    },
    QueryState {
        metrics: Option<Vec<String>>,
    },
    WaitForEvent {
        event_type: String,
        condition: Option<String>,
    },
}

impl Activity for IoTDeviceActivity {
    fn activity_type(&self) -> &str {
        "iot_device_activity"
    }
    
    async fn execute(
        &self,
        context: &ActivityContext
    ) -> Result<Value, WorkflowError> {
        // 1. 获取连接器
        let connector_registry = get_connector_registry()?;
        let connector = connector_registry.get_connector(&self.connector_type)?;
        
        // 2. 确保连接
        connector.connect().await?;
        
        // 3. 根据活动类型执行操作
        let result = match &self.action_type {
            IoTActionType::SendCommand { command } => {
                // 构建命令参数
                let mut parameters = json!({});
                for (param_name, expression) in &self.parameters {
                    let value = evaluate_expression(expression, context)?;
                    parameters[param_name] = value;
                }
                
                // 发送命令
                connector.send_command(&self.device_id, command, &parameters).await?
            },
            IoTActionType::QueryState { metrics } => {
                // 查询设备状态
                let state = connector.query_device_state(&self.device_id, metrics.clone()).await?;
                
                // 转换为JSON结果
                json!({
                    "device_id": state.device_id,
                    "online": state.online,
                    "metrics": state.metrics,
                    "last_updated": state.last_updated,
                })
            },
            IoTActionType::WaitForEvent { event_type, condition } => {
                // 实现等待特定事件的逻辑
                // 这需要更复杂的异步处理和条件评估
                
                // 示例简化实现
                let (tx, rx) = tokio::sync::oneshot::channel::<DeviceTelemetry>();
                
                // 订阅遥测数据
                let subscription_id = connector.subscribe_to_telemetry(
                    vec![self.device_id.clone()],
                    Box::new(move |telemetry| {
                        // 检查是否是我们要等待的事件类型
                        if telemetry.event_type == *event_type {
                            // 如果有条件表达式，评估它
                            if let Some(cond) = condition {
                                // 简化：实际中需要更复杂的条件评估
                                if telemetry.metrics.get("value").is_some() {
                                    let _ = tx.send(telemetry);
                                }
                            } else {
                                // 无条件，直接发送
                                let _ = tx.send(telemetry);
                            }
                        }
                    })
                ).await?;
                
                // 等待事件，或超时
                let telemetry = tokio::time::timeout(self.timeout, rx).await
                    .map_err(|_| WorkflowError::Timeout(format!(
                        "等待设备事件超时: {}", event_type
                    )))??;
                
                // 取消订阅
                connector.unsubscribe(&subscription_id).await?;
                
                // 返回事件数据
                json!({
                    "device_id": telemetry.device_id,
                    "event_type": telemetry.event_type,
                    "timestamp": telemetry.timestamp,
                    "metrics": telemetry.metrics,
                })
            }
        };
        
        // 4. 处理结果映射
        if let Some(path) = &self.result_path {
            json!({
                path: result,
                "_metadata": {
                    "device_id": self.device_id,
                    "connector_type": self.connector_type,
                    "timestamp": Utc::now().to_rfc3339(),
                }
            })
        } else {
            json!({
                "result": result,
                "_metadata": {
                    "device_id": self.device_id,
                    "connector_type": self.connector_type,
                    "timestamp": Utc::now().to_rfc3339(),
                }
            })
        }
    }
}
```

## 工作流监控与运维

### 1. 指标收集与监控

```rust
/// 工作流指标收集器
pub trait MetricsCollector: Send + Sync {
    /// 记录工作流执行时间
    fn record_workflow_duration(
        &self,
        workflow_id: &str,
        definition_id: &str,
        duration_ms: u64,
        success: bool
    );
    
    /// 记录活动执行时间
    fn record_activity_duration(
        &self,
        workflow_id: &str,
        activity_id: &str,
        activity_type: &str,
        duration_ms: u64,
        success: bool
    );
    
    /// 记录工作流状态转换
    fn record_workflow_state_transition(
        &self,
        workflow_id: &str,
        from_state: &WorkflowState,
        to_state: &WorkflowState
    );
    
    /// 记录工作流计数器
    fn increment_counter(
        &self,
        name: &str,
        value: u64,
        labels: HashMap<String, String>
    );
    
    /// 记录自定义指标
    fn record_metric(
        &self,
        name: &str,
        value: f64,
        labels: HashMap<String, String>
    );
}

/// Prometheus指标收集器实现
pub struct PrometheusMetricsCollector {
    workflow_duration: Histogram,
    activity_duration: Histogram,
    workflow_transitions: IntCounter,
    workflow_states: IntGaugeVec,
    custom_counters: HashMap<String, IntCounterVec>,
    custom_gauges: HashMap<String, GaugeVec>,
    registry: Registry,
}

impl PrometheusMetricsCollector {
    pub fn new() -> Result<Self, WorkflowError> {
        let registry = Registry::new();
        
        // 创建工作流执行时间直方图
        let workflow_duration = Histogram::with_opts(
            HistogramOpts::new(
                "workflow_duration_seconds",
                "工作流执行时间(秒)"
            )
            .buckets(vec![
                0.1, 0.5, 1.0, 5.0, 10.0, 30.0, 60.0, 300.0, 600.0, 1800.0
            ])
        )?;
        
        // 创建活动执行时间直方图
        let activity_duration = Histogram::with_opts(
            HistogramOpts::new(
                "activity_duration_seconds",
                "活动执行时间(秒)"
            )
            .buckets(vec![
                0.01, 0.05, 0.1, 0.5, 1.0, 5.0, 10.0, 30.0, 60.0, 300.0
            ])
        )?;
        
        // 创建状态转换计数器
        let workflow_transitions = IntCounter::new(
            "workflow_state_transitions_total",
            "工作流状态转换总数"
        )?;
        
        // 创建工作流状态统计
        let workflow_states = IntGaugeVec::new(
            Opts::new("workflow_states", "各状态下的工作流数量"),
            &["state"]
        )?;
        
        // 注册指标
        registry.register(Box::new(workflow_duration.clone()))?;
        registry.register(Box::new(activity_duration.clone()))?;
        registry.register(Box::new(workflow_transitions.clone()))?;
        registry.register(Box::new(workflow_states.clone()))?;
        
        Ok(Self {
            workflow_duration,
            activity_duration,
            workflow_transitions,
            workflow_states,
            custom_counters: HashMap::new(),
            custom_gauges: HashMap::new(),
            registry,
        })
    }
    
    /// 注册HTTP指标导出器
    pub fn start_http_server(&self, addr: &str) -> Result<(), WorkflowError> {
        let registry = self.registry.clone();
        
        tokio::spawn(async move {
            let encoder = TextEncoder::new();
            
            let app = Router::new()
                .route("/metrics", get(move || {
                    let registry = registry.clone();
                    async move {
                        let mut buffer = Vec::new();
                        let metric_families = registry.gather();
                        encoder.encode(&metric_families, &mut buffer).unwrap();
                        
                        Response::builder()
                            .header("Content-Type", encoder.format_type())
                            .body(Body::from(buffer))
                            .unwrap()
                    }
                }));
            
            let addr = addr.parse().unwrap();
            axum::Server::bind(&addr)
                .serve(app.into_make_service())
                .await
                .unwrap();
        });
        
        Ok(())
    }
}

impl MetricsCollector for PrometheusMetricsCollector {
    fn record_workflow_duration(
        &self,
        workflow_id: &str,
        definition_id: &str,
        duration_ms: u64,
        success: bool
    ) {
        let labels = [
            ("workflow_id", workflow_id.to_string()),
            ("definition_id", definition_id.to_string()),
            ("success", success.to_string()),
        ];
        
        // 记录执行时间，转换为秒
        let duration_seconds = duration_ms as f64 / 1000.0;
        self.workflow_duration
            .with_label_values(&[&labels[0].1, &labels[1].1, &labels[2].1])
            .observe(duration_seconds);
    }
    
    fn record_activity_duration(
        &self,
        workflow_id: &str,
        activity_id: &str,
        activity_type: &str,
        duration_ms: u64,
        success: bool
    ) {
        let labels = [
            ("workflow_id", workflow_id.to_string()),
            ("activity_id", activity_id.to_string()),
            ("activity_type", activity_type.to_string()),
            ("success", success.to_string()),
        ];
        
        // 记录执行时间，转换为秒
        let duration_seconds = duration_ms as f64 / 1000.0;
        self.activity_duration
            .with_label_values(&[&labels[0].1, &labels[1].1, &labels[2].1, &labels[3].1])
            .observe(duration_seconds);
    }
    
    fn record_workflow_state_transition(
        &self,
        workflow_id: &str,
        from_state: &WorkflowState,
        to_state: &WorkflowState
    ) {
        // 递增转换计数器
        self.workflow_transitions.inc();
        
        // 更新状态计数
        self.workflow_states
            .with_label_values(&[&format!("{:?}", from_state)])
            .dec();
        
        self.workflow_states
            .with_label_values(&[&format!("{:?}", to_state)])
            .inc();
    }
    
    fn increment_counter(
        &self,
        name: &str,
        value: u64,
        labels: HashMap<String, String>
    ) {
        // 如果计数器不存在，创建它
        let counter = self.custom_counters.get(name).cloned();
        
        if let Some(counter_vec) = counter {
            // 将HashMap转换为数组
            let label_values: Vec<String> = counter_vec
                .get_metric_with_labels(&labels)
                .label_names()
                .iter()
                .map(|&name| labels.get(name).cloned().unwrap_or_default())
                .collect();
            
            // 递增计数器
            counter_vec
                .with_label_values(&label_values)
                .inc_by(value);
        }
    }
    
    fn record_metric(
        &self,
        name: &str,
        value: f64,
        labels: HashMap<String, String>
    ) {
        // 如果指标不存在，创建它
        let gauge = self.custom_gauges.get(name).cloned();
        
        if let Some(gauge_vec) = gauge {
            // 将HashMap转换为数组
            let label_values: Vec<String> = gauge_vec
                .get_metric_with_labels(&labels)
                .label_names()
                .iter()
                .map(|&name| labels.get(name).cloned().unwrap_or_default())
                .collect();
            
            // 设置指标值
            gauge_vec
                .with_label_values(&label_values)
                .set(value);
        }
    }
}
```

### 2. 工作流可视化与管理

```rust
/// 工作流可视化器
pub trait WorkflowVisualizer: Send + Sync {
    /// 将工作流定义导出为图形表示
    fn export_workflow_graph(
        &self,
        definition: &WorkflowDefinition
    ) -> Result<String, WorkflowError>;
    
    /// 将工作流实例导出为图形表示，标记执行路径
    fn export_instance_graph(
        &self,
        definition: &WorkflowDefinition,
        instance: &WorkflowInstance
    ) -> Result<String, WorkflowError>;
    
    /// 获取工作流可视化格式
    fn format(&self) -> VisualizationFormat;
}

/// 可视化格式
pub enum VisualizationFormat {
    Dot,
    Mermaid,
    Svg,
    Json,
}

/// DOT格式可视化器
pub struct DotVisualizer;

impl WorkflowVisualizer for DotVisualizer {
    fn export_workflow_graph(
        &self,
        definition: &WorkflowDefinition
    ) -> Result<String, WorkflowError> {
        let mut dot = String::from("digraph workflow {\n");
        dot.push_str("  rankdir=LR;\n");
        dot.push_str("  node [shape=box, style=filled, fillcolor=lightblue];\n");
        
        // 添加节点
        for node in &definition.nodes {
            match node.node_type {
                NodeType::Activity => {
                    dot.push_str(&format!("  \"{}\" [label=\"{}\", shape=box];\n", 
                                        node.id, node.name));
                },
                NodeType::Gateway => {
                    dot.push_str(&format!("  \"{}\" [label=\"{}\", shape=diamond, fillcolor=lightgoldenrod];\n", 
                                        node.id, node.name));
                },
                NodeType::Event => {
                    dot.push_str(&format!("  \"{}\" [label=\"{}\", shape=ellipse, fillcolor=lightsalmon];\n", 
                                        node.id, node.name));
                },
                NodeType::SubWorkflow => {
                    dot.push_str(&format!("  \"{}\" [label=\"{}\", shape=box, style=\"filled,dashed\", fillcolor=lightgreen];\n", 
                                        node.id, node.name));
                },
            }
        }
        
        // 添加转换
        for transition in &definition.transitions {
            let label = if let Some(condition) = &transition.condition {
                format!(" [label=\"{}\"]", condition)
            } else {
                String::new()
            };
            
            dot.push_str(&format!("  \"{}\" -> \"{}\"{};
# Rust工作流架构全面梳理（续）

## 工作流可视化与管理（续）

```rust
/// DOT格式可视化器（续）
impl WorkflowVisualizer for DotVisualizer {
    fn export_workflow_graph(
        &self,
        definition: &WorkflowDefinition
    ) -> Result<String, WorkflowError> {
        // 前面部分代码...
        
        // 添加转换
        for transition in &definition.transitions {
            let label = if let Some(condition) = &transition.condition {
                format!(" [label=\"{}\"]", condition)
            } else {
                String::new()
            };
            
            dot.push_str(&format!("  \"{}\" -> \"{}\"{};\n", 
                                 transition.source_id, transition.target_id, label));
        }
        
        dot.push_str("}\n");
        
        Ok(dot)
    }
    
    fn export_instance_graph(
        &self,
        definition: &WorkflowDefinition,
        instance: &WorkflowInstance
    ) -> Result<String, WorkflowError> {
        let mut dot = String::from("digraph workflow_instance {\n");
        dot.push_str("  rankdir=LR;\n");
        dot.push_str("  node [shape=box, style=filled, fillcolor=lightblue];\n");
        
        // 设置图的标题
        dot.push_str(&format!("  labelloc=\"t\";\n"));
        dot.push_str(&format!("  label=\"{} (ID: {})\\nState: {:?}\";\n", 
                             definition.name, instance.id, instance.state));
        
        // 添加所有节点
        for node in &definition.nodes {
            let (shape, color) = match node.node_type {
                NodeType::Activity => ("box", "lightblue"),
                NodeType::Gateway => ("diamond", "lightgoldenrod"),
                NodeType::Event => ("ellipse", "lightsalmon"),
                NodeType::SubWorkflow => ("box", "lightgreen"),
            };
            
            // 检查节点是否在执行路径中
            let is_executed = instance.context.execution_path.contains(&node.id);
            let is_current = instance.context.execution_path.last() == Some(&node.id);
            
            let style = if is_current {
                "filled,bold"
            } else if is_executed {
                "filled"
            } else {
                "filled,dashed"
            };
            
            let color = if is_current {
                "green"
            } else if is_executed {
                color
            } else {
                "lightgray"
            };
            
            dot.push_str(&format!("  \"{}\" [label=\"{}\", shape={}, style=\"{}\", fillcolor={}];\n", 
                                 node.id, node.name, shape, style, color));
        }
        
        // 添加转换
        for transition in &definition.transitions {
            let source_executed = instance.context.execution_path.contains(&transition.source_id);
            let target_executed = instance.context.execution_path.contains(&transition.target_id);
            
            // 查找源节点后是否直接执行了目标节点
            let is_traversed = instance.context.execution_path.windows(2)
                .any(|w| w[0] == transition.source_id && w[1] == transition.target_id);
            
            let style = if is_traversed {
                "bold"
            } else if source_executed && target_executed {
                "solid"
            } else {
                "dashed"
            };
            
            let color = if is_traversed {
                "green"
            } else if source_executed && target_executed {
                "black"
            } else {
                "gray"
            };
            
            let label = if let Some(condition) = &transition.condition {
                format!(" [label=\"{}\", style={}, color={}]", condition, style, color)
            } else {
                format!(" [style={}, color={}]", style, color)
            };
            
            dot.push_str(&format!("  \"{}\" -> \"{}\"{};\n", 
                                 transition.source_id, transition.target_id, label));
        }
        
        dot.push_str("}\n");
        
        Ok(dot)
    }
    
    fn format(&self) -> VisualizationFormat {
        VisualizationFormat::Dot
    }
}

/// 工作流管理控制台
pub struct WorkflowAdminConsole {
    engine: Arc<WorkflowEngine>,
    definition_repository: Arc<dyn WorkflowDefinitionRepository>,
    instance_repository: Arc<dyn WorkflowInstanceRepository>,
    metrics_collector: Arc<dyn MetricsCollector>,
    visualizer: Arc<dyn WorkflowVisualizer>,
}

impl WorkflowAdminConsole {
    /// 创建管理控制台
    pub fn new(
        engine: Arc<WorkflowEngine>,
        definition_repository: Arc<dyn WorkflowDefinitionRepository>,
        instance_repository: Arc<dyn WorkflowInstanceRepository>,
        metrics_collector: Arc<dyn MetricsCollector>,
        visualizer: Arc<dyn WorkflowVisualizer>,
    ) -> Self {
        Self {
            engine,
            definition_repository,
            instance_repository,
            metrics_collector,
            visualizer,
        }
    }
    
    /// 获取工作流定义列表
    pub async fn list_workflow_definitions(
        &self,
        page: usize,
        page_size: usize,
    ) -> Result<(Vec<WorkflowDefinitionSummary>, usize), WorkflowError> {
        self.definition_repository.list_definitions(page, page_size).await
    }
    
    /// 获取工作流实例列表
    pub async fn list_workflow_instances(
        &self,
        query: &WorkflowQuery,
    ) -> Result<Vec<WorkflowInstanceSummary>, WorkflowError> {
        let instances = self.instance_repository.query_instances(query).await?;
        
        // 转换为摘要信息
        let summaries = instances.into_iter().map(|instance| {
            WorkflowInstanceSummary {
                id: instance.id,
                definition_id: instance.definition_id,
                state: instance.state,
                created_at: instance.context.created_at,
                created_by: instance.context.created_by,
                updated_at: instance.context.metadata.get("updated_at")
                    .and_then(|v| v.as_str())
                    .and_then(|s| DateTime::parse_from_rfc3339(s).ok())
                    .map(|dt| dt.with_timezone(&Utc)),
            }
        }).collect();
        
        Ok(summaries)
    }
    
    /// 获取工作流实例详情
    pub async fn get_workflow_instance_details(
        &self,
        instance_id: &str,
    ) -> Result<WorkflowInstanceDetails, WorkflowError> {
        // 加载工作流实例
        let instance = self.instance_repository.get_instance(instance_id).await?;
        
        // 加载工作流定义
        let definition = self.definition_repository
            .get_definition(&instance.definition_id)
            .await?;
        
        // 生成可视化图
        let graph = self.visualizer.export_instance_graph(&definition, &instance)?;
        
        // 计算统计信息
        let stats = self.calculate_instance_stats(&instance);
        
        // 创建详细信息
        let details = WorkflowInstanceDetails {
            id: instance.id,
            definition_id: instance.definition_id,
            definition_name: definition.name,
            state: instance.state,
            created_at: instance.context.created_at,
            created_by: instance.context.created_by,
            updated_at: instance.context.metadata.get("updated_at")
                .and_then(|v| v.as_str())
                .and_then(|s| DateTime::parse_from_rfc3339(s).ok())
                .map(|dt| dt.with_timezone(&Utc)),
            execution_path: instance.context.execution_path,
            data: instance.context.data,
            graph,
            graph_format: self.visualizer.format(),
            statistics: stats,
            error_stack: instance.context.error_stack,
        };
        
        Ok(details)
    }
    
    /// 计算工作流实例统计信息
    fn calculate_instance_stats(&self, instance: &WorkflowInstance) -> InstanceStatistics {
        // 从元数据中提取统计信息
        let start_time = instance.context.created_at;
        
        let end_time = instance.context.metadata.get("completed_at")
            .and_then(|v| v.as_str())
            .and_then(|s| DateTime::parse_from_rfc3339(s).ok())
            .map(|dt| dt.with_timezone(&Utc))
            .unwrap_or_else(|| Utc::now());
        
        let duration = (end_time - start_time).num_milliseconds() as u64;
        
        let activities_executed = instance.context.execution_path.len();
        
        let activities_failed = instance.context.metadata.get("activities_failed")
            .and_then(|v| v.as_u64())
            .unwrap_or(0) as usize;
        
        InstanceStatistics {
            start_time,
            end_time,
            duration_ms: duration,
            activities_executed,
            activities_failed,
            retries: instance.context.metadata.get("retries")
                .and_then(|v| v.as_u64())
                .unwrap_or(0) as usize,
        }
    }
    
    /// 重启失败的工作流实例
    pub async fn restart_failed_workflow(
        &self,
        instance_id: &str,
        user_context: Option<&UserContext>,
    ) -> Result<(), WorkflowError> {
        // 加载工作流实例
        let instance = self.instance_repository.get_instance(instance_id).await?;
        
        // 检查工作流状态
        if instance.state != WorkflowState::Failed {
            return Err(WorkflowError::InvalidState(format!(
                "只能重启失败的工作流，当前状态: {:?}", instance.state
            )));
        }
        
        // 使用工作流引擎重启工作流
        self.engine.restart_workflow_instance(instance_id, user_context).await
    }
    
    /// 获取工作流统计摘要
    pub async fn get_workflow_statistics(
        &self,
        time_range: Option<(DateTime<Utc>, DateTime<Utc>)>,
    ) -> Result<WorkflowStatistics, WorkflowError> {
        // 构建查询
        let mut query = WorkflowQuery::new();
        
        if let Some((start, end)) = time_range {
            query.created_after(start).created_before(end);
        }
        
        // 查询工作流实例
        let instances = self.instance_repository.query_instances(&query).await?;
        
        // 计算统计信息
        let total_workflows = instances.len();
        
        let mut completed = 0;
        let mut failed = 0;
        let mut running = 0;
        let mut other = 0;
        
        for instance in &instances {
            match instance.state {
                WorkflowState::Completed => completed += 1,
                WorkflowState::Failed(_) => failed += 1,
                WorkflowState::Running => running += 1,
                _ => other += 1,
            }
        }
        
        // 计算平均执行时间
        let mut total_duration_ms = 0;
        let mut completed_count = 0;
        
        for instance in &instances {
            if instance.state == WorkflowState::Completed {
                if let (Some(start), Some(end)) = (
                    Some(instance.context.created_at),
                    instance.context.metadata.get("completed_at")
                        .and_then(|v| v.as_str())
                        .and_then(|s| DateTime::parse_from_rfc3339(s).ok())
                        .map(|dt| dt.with_timezone(&Utc))
                ) {
                    total_duration_ms += (end - start).num_milliseconds() as u64;
                    completed_count += 1;
                }
            }
        }
        
        let avg_duration_ms = if completed_count > 0 {
            total_duration_ms / completed_count
        } else {
            0
        };
        
        // 返回统计信息
        Ok(WorkflowStatistics {
            total_workflows,
            completed,
            failed,
            running,
            other,
            avg_duration_ms,
            time_range: time_range.map(|(start, end)| (start, end)),
        })
    }
}
```

## 工作流版本管理与迁移

```rust
/// 工作流版本管理器
pub struct WorkflowVersionManager {
    definition_repository: Arc<dyn WorkflowDefinitionRepository>,
    migration_registry: HashMap<String, HashMap<SemanticVersion, Box<dyn WorkflowMigration>>>,
}

impl WorkflowVersionManager {
    /// 创建版本管理器
    pub fn new(definition_repository: Arc<dyn WorkflowDefinitionRepository>) -> Self {
        Self {
            definition_repository,
            migration_registry: HashMap::new(),
        }
    }
    
    /// 注册工作流迁移策略
    pub fn register_migration(
        &mut self,
        workflow_type: String,
        migration: Box<dyn WorkflowMigration>,
    ) {
        let source_version = migration.source_version();
        
        self.migration_registry
            .entry(workflow_type)
            .or_insert_with(HashMap::new)
            .insert(source_version, migration);
    }
    
    /// 发布新版本工作流定义
    pub async fn publish_new_version(
        &self,
        definition: WorkflowDefinition,
        user_context: Option<&UserContext>,
    ) -> Result<WorkflowDefinitionId, WorkflowError> {
        // 验证新版本
        if !definition.is_valid() {
            return Err(WorkflowError::InvalidDefinition(
                "工作流定义验证失败".into()
            ));
        }
        
        // 检查是否存在旧版本
        let workflow_type = definition.workflow_type.clone();
        let latest_version = self.definition_repository
            .get_latest_version(&workflow_type)
            .await?;
        
        if let Some(latest) = latest_version {
            // 确保新版本号大于当前最新版本
            if definition.version <= latest.version {
                return Err(WorkflowError::InvalidVersion(format!(
                    "新版本 {} 必须大于当前版本 {}",
                    definition.version, latest.version
                )));
            }
            
            // 检查是否有从当前版本到新版本的迁移路径
            let migrations = self.migration_registry.get(&workflow_type);
            
            if let Some(migrations) = migrations {
                if !self.has_migration_path(
                    migrations, 
                    &latest.version, 
                    &definition.version
                ) {
                    return Err(WorkflowError::MigrationPathMissing(format!(
                        "缺少从版本 {} 到 {} 的迁移路径",
                        latest.version, definition.version
                    )));
                }
            } else if definition.version.major > latest.version.major {
                // 主版本升级需要迁移策略
                return Err(WorkflowError::MigrationPathMissing(format!(
                    "主版本升级需要迁移策略: {} -> {}",
                    latest.version, definition.version
                )));
            }
        }
        
        // 发布新版本
        let definition_id = self.definition_repository
            .save_definition(&definition)
            .await?;
        
        Ok(definition_id)
    }
    
    /// 检查是否存在迁移路径
    fn has_migration_path(
        &self,
        migrations: &HashMap<SemanticVersion, Box<dyn WorkflowMigration>>,
        from_version: &SemanticVersion,
        to_version: &SemanticVersion,
    ) -> bool {
        // 如果只是补丁版本升级，不需要迁移
        if from_version.major == to_version.major && from_version.minor == to_version.minor {
            return true;
        }
        
        // 如果是小版本升级，只需要检查是否有小版本迁移
        if from_version.major == to_version.major && from_version.minor < to_version.minor {
            return migrations.contains_key(from_version);
        }
        
        // 主版本升级需要完整的迁移路径
        let mut current = from_version.clone();
        
        while current < *to_version {
            if let Some(migration) = migrations.get(&current) {
                current = migration.target_version();
            } else {
                return false;
            }
        }
        
        current == *to_version
    }
    
    /// 迁移工作流实例到新版本
    pub async fn migrate_instance(
        &self,
        instance_id: &str,
        target_version: Option<SemanticVersion>,
        user_context: Option<&UserContext>,
    ) -> Result<(), WorkflowError> {
        // 加载工作流实例
        let instance_repository = get_instance_repository()?;
        let mut instance = instance_repository.get_instance(instance_id).await?;
        
        // 加载当前工作流定义
        let current_definition = self.definition_repository
            .get_definition(&instance.definition_id)
            .await?;
        
        // 确定目标版本
        let target = if let Some(version) = target_version {
            version
        } else {
            // 获取最新版本
            let latest = self.definition_repository
                .get_latest_version(&current_definition.workflow_type)
                .await?
                .ok_or_else(|| WorkflowError::NotFound(format!(
                    "找不到工作流类型 {} 的最新版本",
                    current_definition.workflow_type
                )))?;
            
            latest.version
        };
        
        // 如果当前版本等于目标版本，无需迁移
        if current_definition.version == target {
            return Ok(());
        }
        
        // 检查工作流状态
        if instance.state == WorkflowState::Running {
            return Err(WorkflowError::InvalidState(
                "无法迁移正在运行的工作流实例".into()
            ));
        }
        
        // 获取迁移路径
        let workflow_type = current_definition.workflow_type.clone();
        let migrations = self.migration_registry.get(&workflow_type)
            .ok_or_else(|| WorkflowError::MigrationPathMissing(format!(
                "找不到工作流类型 {} 的迁移策略",
                workflow_type
            )))?;
        
        // 执行迁移
        let mut current_version = current_definition.version.clone();
        
        while current_version < target {
            if let Some(migration) = migrations.get(&current_version) {
                // 迁移上下文数据
                migration.migrate_instance_data(&mut instance.context.data).await?;
                
                // 更新版本信息
                current_version = migration.target_version();
                
                // 更新元数据
                instance.context.metadata.insert(
                    "migrated_from".to_string(),
                    json!(current_definition.version.to_string())
                );
                
                instance.context.metadata.insert(
                    "migrated_to".to_string(),
                    json!(current_version.to_string())
                );
                
                instance.context.metadata.insert(
                    "migrated_at".to_string(),
                    json!(Utc::now().to_rfc3339())
                );
                
                if let Some(user) = user_context {
                    instance.context.metadata.insert(
                        "migrated_by".to_string(),
                        json!(user.user_id.clone())
                    );
                }
            } else {
                return Err(WorkflowError::MigrationPathMissing(format!(
                    "缺少从版本 {} 到 {} 的迁移路径",
                    current_version, target
                )));
            }
        }
        
        // 更新实例定义ID
        let target_definition = self.definition_repository
            .get_definition_by_type_and_version(&workflow_type, &target)
            .await?
            .ok_or_else(|| WorkflowError::NotFound(format!(
                "找不到工作流类型 {} 版本 {}",
                workflow_type, target
            )))?;
        
        instance.definition_id = target_definition.id.clone();
        instance.context.definition_id = target_definition.id.clone();
        
        // 保存更新后的实例
        instance_repository.save_instance(&instance).await?;
        
        Ok(())
    }
}

/// 工作流迁移接口
pub trait WorkflowMigration: Send + Sync {
    /// 获取源版本
    fn source_version(&self) -> SemanticVersion;
    
    /// 获取目标版本
    fn target_version(&self) -> SemanticVersion;
    
    /// 迁移实例数据
    async fn migrate_instance_data(&self, data: &mut HashMap<String, Value>) -> Result<(), WorkflowError>;
    
    /// 验证迁移兼容性
    fn validate_compatibility(
        &self,
        source_definition: &WorkflowDefinition,
        target_definition: &WorkflowDefinition,
    ) -> Result<(), WorkflowError> {
        // 默认实现：验证工作流类型匹配
        if source_definition.workflow_type != target_definition.workflow_type {
            return Err(WorkflowError::IncompatibleWorkflows(format!(
                "工作流类型不匹配: {} vs {}",
                source_definition.workflow_type,
                target_definition.workflow_type
            )));
        }
        
        // 验证版本匹配
        if self.source_version() != source_definition.version {
            return Err(WorkflowError::IncompatibleWorkflows(format!(
                "源版本不匹配: {} vs {}",
                self.source_version(),
                source_definition.version
            )));
        }
        
        if self.target_version() != target_definition.version {
            return Err(WorkflowError::IncompatibleWorkflows(format!(
                "目标版本不匹配: {} vs {}",
                self.target_version(),
                target_definition.version
            )));
        }
        
        Ok(())
    }
}
```

## 安全与权限模型

```rust
/// 工作流安全管理器
pub struct SecurityManager {
    authenticator: Box<dyn Authenticator>,
    authorizer: Box<dyn Authorizer>,
    audit_logger: Box<dyn AuditLogger>,
}

impl SecurityManager {
    /// 创建安全管理器
    pub fn new(
        authenticator: Box<dyn Authenticator>,
        authorizer: Box<dyn Authorizer>,
        audit_logger: Box<dyn AuditLogger>,
    ) -> Self {
        Self {
            authenticator,
            authorizer,
            audit_logger,
        }
    }
    
    /// 验证用户身份
    pub async fn authenticate(
        &self,
        credentials: &Credentials,
    ) -> Result<UserContext, WorkflowError> {
        self.authenticator.authenticate(credentials).await
    }
    
    /// 验证用户令牌
    pub async fn validate_token(
        &self,
        token: &str,
    ) -> Result<UserContext, WorkflowError> {
        self.authenticator.validate_token(token).await
    }
    
    /// 检查用户权限
    pub async fn check_permission(
        &self,
        user: &UserContext,
        permission: Permission,
        resource: &WorkflowResource,
    ) -> Result<(), WorkflowError> {
        let authorized = self.authorizer.authorize(user, permission, resource).await?;
        
        if !authorized {
            let error = WorkflowError::Unauthorized(format!(
                "用户 {} 没有对资源 {} 的 {:?} 权限",
                user.user_id, resource.resource_id, permission
            ));
            
            // 记录审计日志
            self.audit_logger.log_access_denied(
                user,
                permission,
                resource,
                &error.to_string(),
            ).await?;
            
            return Err(error);
        }
        
        // 记录审计日志
        self.audit_logger.log_access_granted(
            user,
            permission,
            resource,
        ).await?;
        
        Ok(())
    }
    
    /// 记录操作审计
    pub async fn audit_operation(
        &self,
        user: &UserContext,
        operation: &str,
        resource: &WorkflowResource,
        details: Option<&str>,
    ) -> Result<(), WorkflowError> {
        self.audit_logger.log_operation(
            user,
            operation,
            resource,
            details,
        ).await
    }
}

/// 用户上下文
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UserContext {
    pub user_id: String,
    pub username: String,
    pub roles: Vec<String>,
    pub permissions: Vec<String>,
    pub tenant_id: Option<String>,
    pub attributes: HashMap<String, String>,
}

/// 权限枚举
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Permission {
    View,
    Create,
    Edit,
    Delete,
    Execute,
    Manage,
    Admin,
}

/// 工作流资源
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkflowResource {
    pub resource_type: ResourceType,
    pub resource_id: String,
    pub owner_id: Option<String>,
}

/// 资源类型
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ResourceType {
    WorkflowDefinition,
    WorkflowInstance,
    ActivityType,
    System,
}

/// 基于RBAC的授权器
pub struct RbacAuthorizer {
    role_permissions: HashMap<String, HashSet<(ResourceType, Permission)>>,
    resource_owners: HashMap<String, String>,
    tenant_isolation: bool,
}

impl Authorizer for RbacAuthorizer {
    async fn authorize(
        &self,
        user: &UserContext,
        permission: Permission,
        resource: &WorkflowResource,
    ) -> Result<bool, WorkflowError> {
        // 检查是否是系统管理员
        if user.roles.contains(&"system_admin".to_string()) {
            return Ok(true);
        }
        
        // 检查租户隔离
        if self.tenant_isolation {
            if let Some(resource_tenant) = self.get_resource_tenant(&resource.resource_id).await? {
                if let Some(user_tenant) = &user.tenant_id {
                    if resource_tenant != *user_tenant {
                        return Ok(false);
                    }
                }
            }
        }
        
        // 检查资源所有者
        if let Some(owner_id) = &resource.owner_id {
            if *owner_id == user.user_id {
                // 资源所有者有所有权限
                return Ok(true);
            }
        }
        
        // 检查基于角色的权限
        for role in &user.roles {
            if let Some(permissions) = self.role_permissions.get(role) {
                if permissions.contains(&(resource.resource_type.clone(), permission)) {
                    return Ok(true);
                }
            }
        }
        
        // 检查直接权限
        let permission_str = format!("{:?}_{:?}", 
                                    resource.resource_type, permission).to_lowercase();
        
        if user.permissions.contains(&permission_str) {
            return Ok(true);
        }
        
        // 资源级别的特定权限
        let resource_permission = format!("{:?}_{:?}_{}", 
                                        resource.resource_type, permission, resource.resource_id).to_lowercase();
        
        if user.permissions.contains(&resource_permission) {
            return Ok(true);
        }
        
        Ok(false)
    }
    
    // 获取资源所属租户
    async fn get_resource_tenant(&self, resource_id: &str) -> Result<Option<String>, WorkflowError> {
        // 实际实现中应该从数据库查询资源的租户信息
        // 这里简化实现
        Ok(None)
    }
}

/// 审计日志记录器
pub struct DatabaseAuditLogger {
    db_pool: Pool<ConnectionManager<PgConnection>>,
}

impl AuditLogger for DatabaseAuditLogger {
    async fn log_access_granted(
        &self,
        user: &UserContext,
        permission: Permission,
        resource: &WorkflowResource,
    ) -> Result<(), WorkflowError> {
        let audit_entry = AuditEntry {
            id: Uuid::new_v4().to_string(),
            timestamp: Utc::now(),
            user_id: user.user_id.clone(),
            user_name: user.username
# Rust工作流架构全面梳理（续）

## 安全与权限模型（续）

```rust
/// 审计日志记录器（续）
impl AuditLogger for DatabaseAuditLogger {
    async fn log_access_granted(
        &self,
        user: &UserContext,
        permission: Permission,
        resource: &WorkflowResource,
    ) -> Result<(), WorkflowError> {
        let audit_entry = AuditEntry {
            id: Uuid::new_v4().to_string(),
            timestamp: Utc::now(),
            user_id: user.user_id.clone(),
            user_name: user.username.clone(),
            tenant_id: user.tenant_id.clone(),
            action: format!("{:?}", permission),
            resource_type: format!("{:?}", resource.resource_type),
            resource_id: resource.resource_id.clone(),
            outcome: "granted".to_string(),
            details: None,
            ip_address: None,
            user_agent: None,
        };
        
        self.save_audit_entry(audit_entry).await
    }
    
    async fn log_access_denied(
        &self,
        user: &UserContext,
        permission: Permission,
        resource: &WorkflowResource,
        reason: &str,
    ) -> Result<(), WorkflowError> {
        let audit_entry = AuditEntry {
            id: Uuid::new_v4().to_string(),
            timestamp: Utc::now(),
            user_id: user.user_id.clone(),
            user_name: user.username.clone(),
            tenant_id: user.tenant_id.clone(),
            action: format!("{:?}", permission),
            resource_type: format!("{:?}", resource.resource_type),
            resource_id: resource.resource_id.clone(),
            outcome: "denied".to_string(),
            details: Some(reason.to_string()),
            ip_address: None,
            user_agent: None,
        };
        
        self.save_audit_entry(audit_entry).await
    }
    
    async fn log_operation(
        &self,
        user: &UserContext,
        operation: &str,
        resource: &WorkflowResource,
        details: Option<&str>,
    ) -> Result<(), WorkflowError> {
        let audit_entry = AuditEntry {
            id: Uuid::new_v4().to_string(),
            timestamp: Utc::now(),
            user_id: user.user_id.clone(),
            user_name: user.username.clone(),
            tenant_id: user.tenant_id.clone(),
            action: operation.to_string(),
            resource_type: format!("{:?}", resource.resource_type),
            resource_id: resource.resource_id.clone(),
            outcome: "success".to_string(),
            details: details.map(|s| s.to_string()),
            ip_address: None,
            user_agent: None,
        };
        
        self.save_audit_entry(audit_entry).await
    }
}

impl DatabaseAuditLogger {
    async fn save_audit_entry(&self, entry: AuditEntry) -> Result<(), WorkflowError> {
        // 使用非阻塞的方式执行数据库操作
        let db_pool = self.db_pool.clone();
        let entry_clone = entry.clone();
        
        tokio::spawn(async move {
            let conn = db_pool.get().expect("无法获取数据库连接");
            
            diesel::insert_into(audit_logs::table)
                .values(&entry_clone)
                .execute(&conn)
                .expect("保存审计日志失败");
        });
        
        Ok(())
    }
}

/// JWT认证器
pub struct JwtAuthenticator {
    jwt_secret: String,
    user_repository: Arc<dyn UserRepository>,
}

impl Authenticator for JwtAuthenticator {
    async fn authenticate(&self, credentials: &Credentials) -> Result<UserContext, WorkflowError> {
        match credentials {
            Credentials::UsernamePassword { username, password } => {
                // 验证用户凭据
                let user = self.user_repository.find_by_username(username).await?
                    .ok_or_else(|| WorkflowError::AuthenticationFailed("用户不存在".into()))?;
                
                // 验证密码
                if !self.verify_password(password, &user.password_hash)? {
                    return Err(WorkflowError::AuthenticationFailed("密码错误".into()));
                }
                
                // 加载用户角色和权限
                let roles = self.user_repository.get_user_roles(&user.id).await?;
                let permissions = self.user_repository.get_user_permissions(&user.id).await?;
                
                // 创建用户上下文
                let user_context = UserContext {
                    user_id: user.id,
                    username: user.username,
                    roles,
                    permissions,
                    tenant_id: user.tenant_id,
                    attributes: user.attributes,
                };
                
                Ok(user_context)
            },
            Credentials::Token(token) => {
                self.validate_token(token).await
            },
            _ => Err(WorkflowError::UnsupportedCredentials("不支持的凭据类型".into())),
        }
    }
    
    async fn validate_token(&self, token: &str) -> Result<UserContext, WorkflowError> {
        // 解析JWT
        let token_data = jsonwebtoken::decode::<JwtClaims>(
            token,
            &jsonwebtoken::DecodingKey::from_secret(self.jwt_secret.as_bytes()),
            &jsonwebtoken::Validation::default(),
        ).map_err(|e| WorkflowError::InvalidToken(format!("无效的JWT: {}", e)))?;
        
        // 验证令牌是否过期
        let claims = token_data.claims;
        let now = Utc::now().timestamp() as usize;
        
        if claims.exp < now {
            return Err(WorkflowError::ExpiredToken("令牌已过期".into()));
        }
        
        // 加载用户信息
        let user = self.user_repository.find_by_id(&claims.sub).await?
            .ok_or_else(|| WorkflowError::InvalidToken("用户不存在".into()))?;
        
        // 加载用户角色和权限
        let roles = if let Some(roles) = claims.roles {
            roles
        } else {
            self.user_repository.get_user_roles(&user.id).await?
        };
        
        let permissions = if let Some(permissions) = claims.permissions {
            permissions
        } else {
            self.user_repository.get_user_permissions(&user.id).await?
        };
        
        // 创建用户上下文
        let user_context = UserContext {
            user_id: user.id,
            username: user.username,
            roles,
            permissions,
            tenant_id: user.tenant_id,
            attributes: user.attributes,
        };
        
        Ok(user_context)
    }
}

impl JwtAuthenticator {
    fn verify_password(&self, password: &str, hash: &str) -> Result<bool, WorkflowError> {
        bcrypt::verify(password, hash)
            .map_err(|e| WorkflowError::InternalError(format!("密码验证失败: {}", e)))
    }
    
    pub fn generate_token(&self, user_context: &UserContext, expiry_hours: u32) -> Result<String, WorkflowError> {
        let expiration = Utc::now()
            .checked_add_signed(chrono::Duration::hours(expiry_hours as i64))
            .expect("有效的时间戳")
            .timestamp() as usize;
        
        let claims = JwtClaims {
            sub: user_context.user_id.clone(),
            exp: expiration,
            iat: Utc::now().timestamp() as usize,
            roles: Some(user_context.roles.clone()),
            permissions: Some(user_context.permissions.clone()),
            tenant_id: user_context.tenant_id.clone(),
        };
        
        let token = jsonwebtoken::encode(
            &jsonwebtoken::Header::default(),
            &claims,
            &jsonwebtoken::EncodingKey::from_secret(self.jwt_secret.as_bytes()),
        ).map_err(|e| WorkflowError::InternalError(format!("生成JWT失败: {}", e)))?;
        
        Ok(token)
    }
}

/// JWT声明
#[derive(Debug, Serialize, Deserialize)]
struct JwtClaims {
    sub: String,             // 用户ID
    exp: usize,              // 过期时间
    iat: usize,              // 签发时间
    roles: Option<Vec<String>>,       // 用户角色
    permissions: Option<Vec<String>>, // 用户权限
    tenant_id: Option<String>,        // 租户ID
}
```

## 整合与应用示例

最后，让我们通过一个综合示例来展示如何组合所有这些组件，创建一个完整的工作流系统：

```rust
/// 主应用入口
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    env_logger::init();
    
    // 加载配置
    let config = load_configuration()?;
    
    // 创建数据库连接池
    let db_pool = establish_database_connection(&config.database_url)?;
    
    // 创建事件存储
    let event_store = PostgresEventStore::new(db_pool.clone());
    
    // 创建快照存储
    let snapshot_store = PostgresSnapshotStore::new(db_pool.clone());
    
    // 创建工作流定义仓库
    let definition_repository = Arc::new(PostgresWorkflowDefinitionRepository::new(db_pool.clone()));
    
    // 创建工作流实例仓库
    let instance_repository = Arc::new(EventSourcedWorkflowRepository::new(
        Arc::new(event_store), 
        Arc::new(snapshot_store), 
        10
    ));
    
    // 创建活动注册表
    let mut activity_registry = ActivityRegistry::new();
    register_standard_activities(&mut activity_registry);
    register_enterprise_activities(&mut activity_registry);
    register_iot_activities(&mut activity_registry);
    
    // 创建连接器注册表
    let mut connector_registry = ConnectorRegistry::new();
    register_standard_connectors(&mut connector_registry, &config);
    
    // 创建事件总线
    let event_bus = Arc::new(RabbitMqEventBus::new(&config.rabbitmq_url).await?);
    
    // 创建分布式锁管理器
    let lock_manager = Arc::new(RedisLockManager::new(&config.redis_url).await?);
    
    // 创建恢复管理器
    let recovery_manager = Arc::new(DefaultRecoveryManager::new());
    
    // 创建指标收集器
    let metrics_collector = Arc::new(PrometheusMetricsCollector::new()?);
    metrics_collector.start_http_server(&config.metrics_addr)?;
    
    // 创建安全组件
    let user_repository = Arc::new(PostgresUserRepository::new(db_pool.clone()));
    let authenticator = Box::new(JwtAuthenticator::new(config.jwt_secret.clone(), user_repository.clone()));
    let authorizer = Box::new(RbacAuthorizer::new(db_pool.clone(), config.tenant_isolation));
    let audit_logger = Box::new(DatabaseAuditLogger::new(db_pool.clone()));
    
    let security_manager = Arc::new(SecurityManager::new(
        authenticator,
        authorizer,
        audit_logger,
    ));
    
    // 创建工作流引擎
    let workflow_engine = Arc::new(WorkflowEngine::new(
        definition_repository.clone(),
        instance_repository.clone(),
        Arc::new(activity_registry),
        event_bus.clone(),
        lock_manager.clone(),
        recovery_manager,
    ).with_security_manager(security_manager.clone()));
    
    // 创建工作流可视化器
    let visualizer = Arc::new(DotVisualizer::new());
    
    // 创建管理控制台
    let admin_console = WorkflowAdminConsole::new(
        workflow_engine.clone(),
        definition_repository.clone(),
        instance_repository.clone(),
        metrics_collector.clone(),
        visualizer,
    );
    
    // 创建版本管理器
    let version_manager = WorkflowVersionManager::new(definition_repository.clone());
    
    // 创建HTTP API服务器
    let api_server = create_api_server(
        workflow_engine.clone(),
        admin_console,
        version_manager,
        security_manager,
        &config,
    );
    
    // 启动事件监听器
    let _event_listener = WorkflowEventListener::new(
        event_bus.clone(),
        workflow_engine.clone(),
    );
    
    // 启动API服务器
    let server_future = api_server.serve();
    
    // 启动系统监控
    let monitoring_future = start_system_monitoring(
        metrics_collector.clone(),
        &config,
    );
    
    // 等待信号处理
    let signal_future = handle_shutdown_signals();
    
    // 同时运行所有任务
    tokio::select! {
        _ = server_future => {
            log::info!("API服务器已停止");
        },
        _ = monitoring_future => {
            log::info!("监控系统已停止");
        },
        _ = signal_future => {
            log::info!("收到停止信号，正在关闭...");
        }
    }
    
    // 优雅关闭
    log::info!("正在关闭工作流系统...");
    
    // 关闭事件总线连接
    event_bus.close().await?;
    
    log::info!("工作流系统已成功关闭");
    
    Ok(())
}

/// IoT温度监控工作流示例
fn create_temperature_monitoring_workflow() -> WorkflowDefinition {
    let mut definition = WorkflowDefinition::new(
        "temperature_monitoring",
        "设备温度监控工作流",
        SemanticVersion { major: 1, minor: 0, patch: 0 },
    );
    
    // 添加开始事件
    definition.add_node(WorkflowNode {
        id: "start".to_string(),
        name: "开始".to_string(),
        node_type: NodeType::Event,
        metadata: json!({
            "event_type": "start"
        }),
    });
    
    // 添加设备初始化活动
    definition.add_node(WorkflowNode {
        id: "initialize_device".to_string(),
        name: "初始化设备".to_string(),
        node_type: NodeType::Activity,
        metadata: json!({
            "activity_type": "iot_device_activity",
            "device_id": "${workflow.deviceId}",
            "connector_type": "mqtt_connector",
            "action_type": "SendCommand",
            "command": "initialize",
            "parameters": {
                "mode": "monitoring",
                "interval": 60,
                "thresholds": {
                    "temperature": 30.0,
                    "humidity": 80.0
                }
            }
        }),
    });
    
    // 添加循环监控网关
    definition.add_node(WorkflowNode {
        id: "monitoring_loop".to_string(),
        name: "监控循环".to_string(),
        node_type: NodeType::Gateway,
        metadata: json!({
            "gateway_type": "inclusive"
        }),
    });
    
    // 添加查询设备状态活动
    definition.add_node(WorkflowNode {
        id: "query_device_state".to_string(),
        name: "查询设备状态".to_string(),
        node_type: NodeType::Activity,
        metadata: json!({
            "activity_type": "iot_device_activity",
            "device_id": "${workflow.deviceId}",
            "connector_type": "mqtt_connector",
            "action_type": "QueryState",
            "metrics": ["temperature", "humidity", "battery"],
            "result_path": "device_state"
        }),
    });
    
    // 添加检查温度阈值网关
    definition.add_node(WorkflowNode {
        id: "check_temperature".to_string(),
        name: "检查温度".to_string(),
        node_type: NodeType::Gateway,
        metadata: json!({
            "gateway_type": "exclusive"
        }),
    });
    
    // 添加发送告警活动
    definition.add_node(WorkflowNode {
        id: "send_alert".to_string(),
        name: "发送告警".to_string(),
        node_type: NodeType::Activity,
        metadata: json!({
            "activity_type": "notification_activity",
            "notification_type": "email",
            "recipients": "${workflow.alertRecipients}",
            "subject": "设备温度警报",
            "body_template": "设备 ${workflow.deviceId} 温度异常，当前温度: ${device_state.metrics.temperature}°C，超过阈值: ${workflow.temperatureThreshold}°C"
        }),
    });
    
    // 添加记录企业系统活动
    definition.add_node(WorkflowNode {
        id: "log_to_enterprise_system".to_string(),
        name: "记录到企业系统".to_string(),
        node_type: NodeType::Activity,
        metadata: json!({
            "activity_type": "enterprise_system_activity",
            "connector_type": "sap_connector",
            "operation": "create_maintenance_request",
            "parameter_mapping": {
                "device_id": "${workflow.deviceId}",
                "temperature": "${device_state.metrics.temperature}",
                "humidity": "${device_state.metrics.humidity}",
                "timestamp": "${device_state.last_updated}",
                "alert_level": "high"
            }
        }),
    });
    
    // 添加等待周期网关
    definition.add_node(WorkflowNode {
        id: "wait_cycle".to_string(),
        name: "等待周期".to_string(),
        node_type: NodeType::Activity,
        metadata: json!({
            "activity_type": "delay_activity",
            "delay_seconds": "${workflow.monitoringInterval}"
        }),
    });
    
    // 添加结束事件
    definition.add_node(WorkflowNode {
        id: "end".to_string(),
        name: "结束".to_string(),
        node_type: NodeType::Event,
        metadata: json!({
            "event_type": "end"
        }),
    });
    
    // 添加转换
    definition.add_transition(Transition {
        source_id: "start".to_string(),
        target_id: "initialize_device".to_string(),
        condition: None,
    });
    
    definition.add_transition(Transition {
        source_id: "initialize_device".to_string(),
        target_id: "monitoring_loop".to_string(),
        condition: None,
    });
    
    definition.add_transition(Transition {
        source_id: "monitoring_loop".to_string(),
        target_id: "query_device_state".to_string(),
        condition: None,
    });
    
    definition.add_transition(Transition {
        source_id: "query_device_state".to_string(),
        target_id: "check_temperature".to_string(),
        condition: None,
    });
    
    definition.add_transition(Transition {
        source_id: "check_temperature".to_string(),
        target_id: "send_alert".to_string(),
        condition: Some("${device_state.metrics.temperature > workflow.temperatureThreshold}".to_string()),
    });
    
    definition.add_transition(Transition {
        source_id: "check_temperature".to_string(),
        target_id: "wait_cycle".to_string(),
        condition: Some("${device_state.metrics.temperature <= workflow.temperatureThreshold}".to_string()),
    });
    
    definition.add_transition(Transition {
        source_id: "send_alert".to_string(),
        target_id: "log_to_enterprise_system".to_string(),
        condition: None,
    });
    
    definition.add_transition(Transition {
        source_id: "log_to_enterprise_system".to_string(),
        target_id: "wait_cycle".to_string(),
        condition: None,
    });
    
    definition.add_transition(Transition {
        source_id: "wait_cycle".to_string(),
        target_id: "monitoring_loop".to_string(),
        condition: Some("${workflow.monitoringCount < workflow.maxMonitoringCycles}".to_string()),
    });
    
    definition.add_transition(Transition {
        source_id: "wait_cycle".to_string(),
        target_id: "end".to_string(),
        condition: Some("${workflow.monitoringCount >= workflow.maxMonitoringCycles}".to_string()),
    });
    
    definition
}
```

## 总结

我们已经完成了一个全面的Rust工作流架构设计，该架构：

1. **充分利用Rust的类型系统**：通过trait、泛型和所有权模型保证了系统的安全性和正确性

2. **区分了三个流层面**：
   - 数据流：通过数据转换器和映射处理数据的流动和转换
   - 执行流：通过活动和任务定义执行逻辑
   - 控制流：通过网关和条件定义工作流的编排和决策

3. **考虑了分布式系统特性**：
   - 使用事件溯源确保一致性和可恢复性
   - 使用分布式锁避免竞态条件
   - 实现了容错和重试机制
   - 支持异步执行和并发处理

4. **兼容企业业务流程与IoT领域**：
   - 提供了通用的集成接口
   - 设计了特定领域的连接器
   - 支持跨领域的数据映射和转换

5. **支持工作流持久化和上下文管理**：
   - 使用事件溯源实现了可靠的状态管理
   - 通过快照优化了状态恢复性能
   - 设计了全面的监控和遥测系统
   - 支持动态调整和版本管理

这个架构不仅在技术上稳健，而且在理论上也有坚实的基础，结合了Petri网、状态机、事件溯源等核心理论，
适合构建企业级的工作流系统。
