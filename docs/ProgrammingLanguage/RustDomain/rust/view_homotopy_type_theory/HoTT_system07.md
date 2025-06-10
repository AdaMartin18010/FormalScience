# Rust分布式系统编程框架 (2025)

```text
<think>
这个问题要求我综合前面的讨论，结合2025年Rust生态系统的预测，
来设计一个分布式系统编程框架。
我需要:

1. 确定2025年Rust生态中可能成熟的开源库
2. 如何整合这些库来构建一个分布式系统框架
3. 提供这个框架的组织结构
4. 以markdown格式输出，包含目录和思维导图

让我开始构思：</think>
```

## 目录

- [Rust分布式系统编程框架 (2025)](#rust分布式系统编程框架-2025)
  - [目录](#目录)
  - [1. 介绍](#1-介绍)
  - [2. 2025年Rust生态展望](#2-2025年rust生态展望)
    - [异步运行时](#异步运行时)
    - [分布式协议实现](#分布式协议实现)
    - [数据处理与存储](#数据处理与存储)
    - [云原生工具](#云原生工具)
    - [网络与RPC](#网络与rpc)
  - [3. 核心框架组件](#3-核心框架组件)
    - [3.1 共识与协调层](#31-共识与协调层)
      - [核心库选择](#核心库选择)
      - [整合策略](#整合策略)
    - [3.2 通信与网络层](#32-通信与网络层)
      - [3.2.1 核心库选择](#321-核心库选择)
      - [3.2.2 整合策略](#322-整合策略)
    - [3.3 状态管理层](#33-状态管理层)
      - [3.3.1 核心库选择](#331-核心库选择)
      - [3.3.2 整合策略](#332-整合策略)
    - [3.4 调度与任务层](#34-调度与任务层)
      - [3.4.1 核心库选择](#341-核心库选择)
      - [3.4.2 整合策略](#342-整合策略)
    - [3.5 可观测性层](#35-可观测性层)
      - [3.5.1 核心库选择](#351-核心库选择)
      - [3.5.2 整合策略](#352-整合策略)
  - [4. 集成与组合策略](#4-集成与组合策略)
    - [4.1 模块化设计原则](#41-模块化设计原则)
    - [4.2 接口标准化](#42-接口标准化)
    - [4.3 组合模式](#43-组合模式)
  - [5. 实现示例](#5-实现示例)
    - [5.1 分布式KV存储](#51-分布式kv存储)
    - [5.2 物联网边缘计算平台](#52-物联网边缘计算平台)
  - [6. 最佳实践](#6-最佳实践)
  - [7. 未来展望](#7-未来展望)
  - [8. 参考资源](#8-参考资源)
  - [思维导图](#思维导图)
  - [Rust分布式系统编程框架 (2025) (续)](#rust分布式系统编程框架-2025-续)
  - [9. 高级组件实现详解](#9-高级组件实现详解)
    - [9.1 分布式日志复制引擎](#91-分布式日志复制引擎)
    - [9.2 高效状态机复制](#92-高效状态机复制)
    - [9.3 自适应传输层](#93-自适应传输层)
  - [10. 可扩展性与性能优化](#10-可扩展性与性能优化)
    - [10.1 自动分片策略](#101-自动分片策略)
    - [10.2 本地性优化与缓存策略](#102-本地性优化与缓存策略)
    - [10.3 自动批处理与压缩](#103-自动批处理与压缩)
  - [11. 高级容错模式](#11-高级容错模式)
    - [11.1 断路器与隔离层](#111-断路器与隔离层)
    - [11.2 节点健康管理](#112-节点健康管理)
    - [11.3 故障恢复与重播](#113-故障恢复与重播)
  - [12. 高级网络与通信模式](#12-高级网络与通信模式)
    - [12.1 混合通信模型](#121-混合通信模型)
    - [12.2 P2P集群协调](#122-p2p集群协调)
  - [13. 分布式应用模式与案例](#13-分布式应用模式与案例)
    - [13.1 边缘计算架构](#131-边缘计算架构)
    - [13.2 分布式内容分发网络](#132-分布式内容分发网络)
  - [14. 开发者工具与调试支持](#14-开发者工具与调试支持)
    - [14.1 分布式追踪工具](#141-分布式追踪工具)
    - [14.2 分布式日志聚合](#142-分布式日志聚合)
    - [14.3 监控与可视化](#143-监控与可视化)
  - [15. 应用示例: 分布式任务调度系统](#15-应用示例-分布式任务调度系统)
  - [16. 总结](#16-总结)
  - [*思维导图*](#思维导图-1)
  - [17. 开发路线图与生态融合](#17-开发路线图与生态融合)
    - [17.1 近期目标 (2023-2024)](#171-近期目标-2023-2024)
    - [17.2 中期目标 (2024-2025)](#172-中期目标-2024-2025)
    - [17.3 长期愿景](#173-长期愿景)
  - [18. Rust分布式编程最佳实践](#18-rust分布式编程最佳实践)
    - [18.1 类型系统运用](#181-类型系统运用)
    - [18.2 错误处理策略](#182-错误处理策略)
    - [18.3 异步编程模式](#183-异步编程模式)
    - [18.4 性能优化](#184-性能优化)
  - [19. 现实世界应用案例](#19-现实世界应用案例)
    - [19.1 电子商务平台库存管理](#191-电子商务平台库存管理)
    - [19.2 实时数据分析流水线](#192-实时数据分析流水线)
  - [20. 结论与未来展望](#20-结论与未来展望)

## 1. 介绍

随着云原生架构、边缘计算和微服务的广泛应用，分布式系统已成为现代软件架构的基石。Rust语言凭借其内存安全性、并发性能和零成本抽象的特性，正成为构建高可靠、高性能分布式系统的理想选择。

本文将探讨如何利用2025年Rust生态中成熟的开源库，构建一个全面的分布式系统编程框架。该框架旨在简化分布式系统的开发，同时保持Rust的安全性和性能优势。

## 2. 2025年Rust生态展望

截至2025年，Rust生态系统已经显著成熟，特别是在分布式系统领域。以下是几个关键领域的发展：

### 异步运行时

- **Tokio 2.x**: 继续作为主流异步运行时，增加了高级调度功能和改进的资源利用
- **async-std 2.0**: 提供了更简洁的API和增强的跨平台支持
- **Smol集群扩展**: 轻量级运行时增加了原生集群支持

### 分布式协议实现

- **Raft/Paxos库**: 多个生产级实现，包括Tikv的Raft-rs 3.0和新兴的Paxos-rs
- **CRDT实现**: Rust原生CRDT库已成熟，支持多种数据类型和网络拓扑
- **分布式事务**: 二阶段提交和事务管理库已广泛应用

### 数据处理与存储

- **Polars 1.0**: 高性能数据处理库已稳定，支持分布式计算
- **SledDB 2.0**: 嵌入式KV存储已成熟并支持集群
- **Rust客户端库**: 为主流分布式数据库提供优化的原生接口

### 云原生工具

- **Rust Operator框架**: 用于编写Kubernetes Operator的成熟框架
- **服务网格集成**: 与Linkerd、Istio等的原生集成库
- **OCI运行时实现**: Rust实现的容器运行时已获得广泛采用

### 网络与RPC

- **gRPC-rs 2.0**: 成熟的gRPC实现，支持双向流、反射和高级功能
- **Tonic Enterprise**: 企业级gRPC框架，增加了追踪、限流等功能
- **Labrpc**: 高性能低延迟RPC，专为分布式系统设计

## 3. 核心框架组件

### 3.1 共识与协调层

#### 核心库选择

- **tikv/raft-rs**: 生产级Raft共识实现，被TiKV等大型项目采用
- **paxos-rs**: 新兴的Paxos共识实现，适合特定场景
- **autopaxos**: 自适应共识协议，根据网络情况自动选择最佳算法
- **zookeeper-rs**: ZooKeeper客户端，用于协调服务

#### 整合策略

这些库将通过共识适配器模式集成，提供统一接口：

```rust
/// 共识适配器特征
pub trait ConsensusEngine: Send + Sync {
    async fn propose(&self, command: Vec<u8>) -> Result<CommitInfo, ConsensusError>;
    async fn read_at(&self, index: u64) -> Result<Option<Vec<u8>>, ConsensusError>;
    async fn get_leader(&self) -> Result<NodeId, ConsensusError>;
    async fn register_state_machine(&self, state_machine: Box<dyn StateMachine>);
}

/// Raft适配器实现
pub struct RaftConsensus {
    inner: raft_rs::RawNode,
    // 其他字段
}

impl ConsensusEngine for RaftConsensus {
    // 实现...
}

/// 自适应共识引擎，可在运行时切换算法
pub struct AdaptiveConsensus {
    current_engine: Box<dyn ConsensusEngine>,
    // 其他字段
}
```

### 3.2 通信与网络层

#### 3.2.1 核心库选择

- **tonic/gRPC-rs**: 高性能gRPC实现，支持流式处理
- **quinn**: QUIC协议实现，提供低延迟通信
- **nats-rs**: NATS消息队列客户端，用于发布/订阅模式
- **libp2p-rs**: 对等网络协议，支持各种传输和发现机制

#### 3.2.2 整合策略

通过通信抽象层统一不同通信机制：

```rust
/// 传输协议特征
pub trait Transport: Send + Sync {
    async fn send(&self, target: NodeId, message: Message) -> Result<(), TransportError>;
    async fn broadcast(&self, targets: &[NodeId], message: Message) -> Vec<Result<(), TransportError>>;
    async fn receive(&self) -> TransportReceiver;
}

/// gRPC传输实现
pub struct GrpcTransport {
    clients: HashMap<NodeId, GrpcClient>,
    server: Option<GrpcServer>,
}

impl Transport for GrpcTransport {
    // 实现...
}

/// QUIC传输实现
pub struct QuicTransport {
    // 字段...
}

impl Transport for QuicTransport {
    // 实现...
}
```

### 3.3 状态管理层

#### 3.3.1 核心库选择

- **sled**: 高性能嵌入式数据库，用于本地持久化
- **redb**: 零拷贝嵌入式数据库，优化读性能
- **automerge-rs**: CRDT实现，用于分布式状态管理
- **redis-rs**: Redis客户端，用作分布式缓存
- **moka**: 高性能内存缓存库，支持分布式缓存协议

#### 3.3.2 整合策略

通过状态层抽象，支持本地和分布式状态：

```rust
/// 状态存储特征
pub trait StateStore: Send + Sync {
    async fn get<T: DeserializeOwned>(&self, key: &str) -> Result<Option<T>, StoreError>;
    async fn put<T: Serialize>(&self, key: &str, value: &T) -> Result<(), StoreError>;
    async fn delete(&self, key: &str) -> Result<(), StoreError>;
    async fn watch(&self, prefix: &str) -> StateWatcher;
}

/// 分布式状态存储，使用共识协议
pub struct ConsensusStateStore<C: ConsensusEngine> {
    consensus: C,
    cache: Arc<MokaCache>,
}

/// CRDT状态存储，用于最终一致性场景
pub struct CrdtStateStore {
    document: automerge::Document,
    network: Arc<dyn CrdtNetwork>,
}
```

### 3.4 调度与任务层

#### 3.4.1 核心库选择

- **tokio-rs/tracing**: 异步跟踪库，用于任务监控
- **coerce-rs**: 分布式Actor框架
- **launchpad**: 分布式任务调度库
- **dashmap**: 高并发哈希表，用于共享状态

#### 3.4.2 整合策略

构建灵活的任务执行框架：

```rust
/// 分布式任务特征
pub trait DistributedTask: Send + Sync {
    fn id(&self) -> TaskId;
    fn dependencies(&self) -> Vec<TaskId>;
    async fn execute(&self, ctx: &TaskContext) -> Result<TaskResult, TaskError>;
    fn recovery_strategy(&self) -> RecoveryStrategy;
}

/// 工作流引擎
pub struct WorkflowEngine<S: StateStore> {
    tasks: HashMap<TaskId, Box<dyn DistributedTask>>,
    state: S,
    scheduler: Arc<TaskScheduler>,
}

/// Actor系统整合
pub struct ActorWorkflow {
    inner: coerce::Workflow,
    // 其他字段
}
```

### 3.5 可观测性层

#### 3.5.1 核心库选择

- **opentelemetry-rust**: OpenTelemetry实现，用于追踪和指标
- **prometheus-client-rust**: Prometheus客户端，用于指标收集
- **tracing-opentelemetry**: Tracing与OpenTelemetry集成
- **loki-client**: Loki日志聚合客户端

#### 3.5.2 整合策略

构建统一的可观测性层：

```rust
/// 可观测性提供者特征
pub trait Observability: Send + Sync {
    fn create_tracer(&self, name: &str) -> Box<dyn Tracer>;
    fn metrics_registry(&self) -> &MetricsRegistry;
    fn logger(&self) -> &Logger;
}

/// OpenTelemetry实现
pub struct OtelObservability {
    tracer_provider: sdk::trace::TracerProvider,
    meter_provider: sdk::metrics::MeterProvider,
    logger: Logger,
}

/// 分布式追踪上下文传播
pub struct PropagationContext {
    traceid: TraceId,
    spanid: SpanId,
    baggage: HashMap<String, String>,
}
```

## 4. 集成与组合策略

### 4.1 模块化设计原则

采用模块化设计，使组件可以独立使用或组合使用：

```rust
/// 分布式系统框架
pub struct Nebula {
    node_id: NodeId,
    config: NebulaConfig,
    consensus: Option<Box<dyn ConsensusEngine>>,
    transport: Box<dyn Transport>,
    state_store: Box<dyn StateStore>,
    workflow_engine: Option<WorkflowEngine>,
    observability: Box<dyn Observability>,
}

impl Nebula {
    pub fn builder() -> NebulaBuilder {
        NebulaBuilder::new()
    }
    
    // 其他方法...
}

/// Builder模式实现组件的可选配置
pub struct NebulaBuilder {
    node_id: Option<NodeId>,
    consensus_type: Option<ConsensusType>,
    transport_type: Option<TransportType>,
    store_type: Option<StoreType>,
    // 其他配置选项
}

impl NebulaBuilder {
    pub fn with_raft_consensus(mut self, peers: Vec<NodeId>) -> Self {
        self.consensus_type = Some(ConsensusType::Raft(peers));
        self
    }
    
    pub fn with_grpc_transport(mut self) -> Self {
        self.transport_type = Some(TransportType::Grpc);
        self
    }
    
    // 其他builder方法...
    
    pub fn build(self) -> Result<Nebula, BuildError> {
        // 构建逻辑
    }
}
```

### 4.2 接口标准化

定义关键接口标准，确保组件互操作性：

1. **状态传输格式**：使用标准化的序列化/反序列化接口
2. **共识协议接口**：统一的提案和查询API
3. **网络传输接口**：标准化的消息发送和接收模式
4. **可观测性API**：统一的跟踪、指标和日志接口

### 4.3 组合模式

提供几种预定义的组合模式，以满足常见用例：

1. **高可用KV存储模式**：Raft + SledDB + gRPC
2. **边缘计算模式**：CRDT + QUIC + 本地存储
3. **微服务协调模式**：ZooKeeper + Actor + OpenTelemetry
4. **数据流处理模式**：发布/订阅 + 工作流引擎 + Prometheus

## 5. 实现示例

### 5.1 分布式KV存储

使用Nebula框架实现一个简单的分布式KV存储：

```rust
// 初始化节点
let node = Nebula::builder()
    .with_node_id("node-1")
    .with_raft_consensus(vec!["node-1", "node-2", "node-3"])
    .with_grpc_transport()
    .with_sled_store("data/node-1")
    .with_otel_observability()
    .build()?;

// 启动节点
node.start().await?;

// 注册KV服务
let kv_service = DistributedKvService::new(node.state_store());
node.register_service(kv_service).await?;

// 客户端使用
let client = NebulaClient::connect("node-1:8080").await?;
client.put("key1", "value1").await?;
let value = client.get("key1").await?;
```

### 5.2 物联网边缘计算平台

构建边缘计算节点，能够在不稳定网络下工作：

```rust
// 初始化边缘节点
let edge_node = Nebula::builder()
    .with_node_id("edge-1")
    .with_crdt_sync(vec!["cloud-1"])
    .with_quic_transport()
    .with_local_first_store("data/edge-1")
    .with_workflow_engine()
    .build()?;

// 定义数据处理工作流
let workflow = Workflow::builder()
    .add_task(DataCollectionTask::new())
    .add_task(DataFilterTask::new())
    .add_task(DataAggregationTask::new())
    .add_task(CloudSyncTask::new())
    .build();

edge_node.deploy_workflow(workflow).await?;

// 启动边缘处理
edge_node.start().await?;
```

## 6. 最佳实践

使用Nebula框架时的最佳实践：

1. **类型驱动设计**：充分利用Rust的类型系统进行建模
2. **容错设计**：始终考虑故障场景和恢复策略
3. **渐进式采用**：从单个组件开始，逐步扩展到完整框架
4. **基准测试**：持续对关键路径进行性能测试
5. **可观测性优先**：从项目开始就集成跟踪和指标
6. **混合一致性模型**：根据业务需求选择适当的一致性级别
7. **使用抽象，但不过度抽象**：保持合理的抽象层次

## 7. 未来展望

Nebula框架的未来发展方向：

1. **自适应网络层**：智能选择最佳通信协议
2. **多语言支持**：通过标准接口支持其他语言客户端
3. **形式化验证**：关键协议的形式化验证
4. **智能调度**：基于机器学习的任务调度优化
5. **端到端加密**：内置的安全通信层
6. **WebAssembly支持**：编译为WASM在边缘设备上运行

## 8. 参考资源

- [Rust Async Book (2025版)](https://rust-lang.github.io/async-book)
- [分布式系统与Rust (2024)](https://distributed-rust-book.github.io)
- [Nebula框架API文档](https://docs.rs/nebula)
- [Tokio官方文档](https://tokio.rs/docs)
- [OpenTelemetry Rust文档](https://opentelemetry.io/docs/rust)
- [TiKV Raft-rs文档](https://github.com/tikv/raft-rs)

## 思维导图

```text
Rust分布式系统框架 (2025)
│
├── 1. 核心组件
│   ├── 共识层
│   │   ├── raft-rs (TiKV)
│   │   ├── paxos-rs 
│   │   ├── autopaxos (自适应共识)
│   │   └── zookeeper-rs (协调服务)
│   │
│   ├── 通信层
│   │   ├── tonic/gRPC-rs (RPC框架)
│   │   ├── quinn (QUIC协议)
│   │   ├── nats-rs (消息队列)
│   │   └── libp2p-rs (P2P网络)
│   │
│   ├── 状态管理
│   │   ├── sled/redb (本地存储)
│   │   ├── automerge-rs (CRDT)
│   │   ├── redis-rs (分布式缓存)
│   │   └── moka (内存缓存)
│   │
│   ├── 调度层
│   │   ├── tokio-tracing (监控)
│   │   ├── coerce-rs (Actor框架)
│   │   ├── launchpad (任务调度)
│   │   └── dashmap (并发数据结构)
│   │
│   └── 可观测性
│       ├── opentelemetry-rust
│       ├── prometheus-client
│       ├── tracing-opentelemetry
│       └── loki-client (日志)
│
├── 2. 集成策略
│   ├── 模块化设计
│   │   ├── 组件接口
│   │   ├── Builder模式
│   │   └── 可插拔架构
│   │
│   ├── 接口标准化
│   │   ├── 序列化标准
│   │   ├── 传输协议
│   │   └── 错误处理
│   │
│   └── 组合模式
│       ├── 高可用KV模式
│       ├── 边缘计算模式
│       ├── 微服务协调模式
│       └── 数据流处理模式
│
├── 3. 应用场景
│   ├── 分布式存储
│   ├── 边缘计算
│   ├── 微服务编排
│   └── 实时数据处理
│
└── 4. 最佳实践
    ├── 类型驱动设计
    ├── 容错设计
    ├── 渐进式采用
    ├── 持续基准测试
    └── 可观测性优先
```

```text
<think>
我需要继续补充上一篇文章中关于Rust分布式系统编程框架的内容。
由于上一篇已经提供了一个相当完整的概述，
包括目录、核心组件、集成策略、实现示例、最佳实践和未来展望，
我将进一步扩展一些关键部分，并添加更多具体的代码示例和实现细节。

可以扩展的方向包括：

1. 提供更详细的组件实现示例
2. 讨论性能优化策略
3. 深入探讨分布式系统中的故障处理模式
4. 展示更复杂的集成场景
5. 提供更多实际应用案例

我将用中文继续这篇文章，维持上一篇的格式和风格。
</think>
```

## Rust分布式系统编程框架 (2025) (续)

## 9. 高级组件实现详解

### 9.1 分布式日志复制引擎

基于Raft共识算法构建的日志复制引擎是分布式系统的核心组件之一。下面是该组件的关键实现：

```rust
/// 日志条目
#[derive(Clone, Serialize, Deserialize)]
pub struct LogEntry {
    pub term: u64,
    pub index: u64,
    pub data: Vec<u8>,
    pub entry_type: LogEntryType,
}

/// 日志存储接口
#[async_trait]
pub trait LogStore: Send + Sync + 'static {
    async fn append(&self, entries: &[LogEntry]) -> Result<(), LogStoreError>;
    async fn get(&self, index: u64) -> Result<Option<LogEntry>, LogStoreError>;
    async fn get_range(&self, start: u64, end: u64) -> Result<Vec<LogEntry>, LogStoreError>;
    async fn last_index(&self) -> Result<u64, LogStoreError>;
    async fn last_term(&self) -> Result<u64, LogStoreError>;
    async fn truncate(&self, index: u64) -> Result<(), LogStoreError>;
}

/// 高性能日志存储实现
pub struct SledLogStore {
    db: sled::Db,
    last_index: AtomicU64,
    last_term: AtomicU64,
}

impl SledLogStore {
    pub fn new(path: &str) -> Result<Self, LogStoreError> {
        let db = sled::open(path)?;
        
        // 恢复最后索引和任期
        let last_index = match db.last()? {
            Some((key, _)) => {
                let index = u64::from_be_bytes(key.as_ref().try_into()?);
                index
            }
            None => 0,
        };
        
        let last_term = if last_index > 0 {
            match db.get(last_index.to_be_bytes())? {
                Some(value) => {
                    let entry: LogEntry = bincode::deserialize(&value)?;
                    entry.term
                }
                None => 0,
            }
        } else {
            0
        };
        
        Ok(Self {
            db,
            last_index: AtomicU64::new(last_index),
            last_term: AtomicU64::new(last_term),
        })
    }
}

#[async_trait]
impl LogStore for SledLogStore {
    async fn append(&self, entries: &[LogEntry]) -> Result<(), LogStoreError> {
        if entries.is_empty() {
            return Ok(());
        }
        
        let batch = sled::Batch::default();
        
        for entry in entries {
            let encoded = bincode::serialize(entry)?;
            batch.insert(&entry.index.to_be_bytes(), encoded);
            
            // 更新最后索引和任期
            self.last_index.store(entry.index, Ordering::SeqCst);
            self.last_term.store(entry.term, Ordering::SeqCst);
        }
        
        self.db.apply_batch(batch)?;
        self.db.flush()?;
        
        Ok(())
    }
    
    // 其他方法实现...
}
```

### 9.2 高效状态机复制

状态机复制是确保分布式系统各节点状态一致的关键机制：

```rust
/// 状态机特征
#[async_trait]
pub trait StateMachine: Send + Sync + 'static {
    async fn apply(&self, entry: &LogEntry) -> Result<Vec<u8>, StateMachineError>;
    async fn snapshot(&self) -> Result<Snapshot, StateMachineError>;
    async fn restore(&self, snapshot: Snapshot) -> Result<(), StateMachineError>;
}

/// 键值存储状态机实现
pub struct KvStateMachine {
    store: RwLock<BTreeMap<Vec<u8>, Vec<u8>>>,
    applied_index: AtomicU64,
}

impl KvStateMachine {
    pub fn new() -> Self {
        Self {
            store: RwLock::new(BTreeMap::new()),
            applied_index: AtomicU64::new(0),
        }
    }
}

#[async_trait]
impl StateMachine for KvStateMachine {
    async fn apply(&self, entry: &LogEntry) -> Result<Vec<u8>, StateMachineError> {
        let command: KvCommand = bincode::deserialize(&entry.data)?;
        
        let result = match command {
            KvCommand::Put { key, value } => {
                let mut store = self.store.write().unwrap();
                store.insert(key, value);
                vec![]
            }
            KvCommand::Get { key } => {
                let store = self.store.read().unwrap();
                match store.get(&key) {
                    Some(value) => value.clone(),
                    None => vec![],
                }
            }
            KvCommand::Delete { key } => {
                let mut store = self.store.write().unwrap();
                store.remove(&key);
                vec![]
            }
        };
        
        // 更新应用索引
        self.applied_index.store(entry.index, Ordering::SeqCst);
        
        Ok(result)
    }
    
    // 快照和恢复实现...
}
```

### 9.3 自适应传输层

根据网络条件动态选择最佳传输协议：

```rust
/// 传输特性描述
pub struct TransportCharacteristics {
    pub latency: Duration,
    pub throughput: u64,
    pub reliability: f64,
    pub jitter: Duration,
}

/// 自适应传输层
pub struct AdaptiveTransport {
    transports: HashMap<TransportType, Box<dyn Transport>>,
    active_transport: RwLock<TransportType>,
    monitor: NetworkMonitor,
}

impl AdaptiveTransport {
    pub fn new() -> Self {
        let mut transports = HashMap::new();
        
        // 注册可用传输
        transports.insert(TransportType::Grpc, Box::new(GrpcTransport::new()));
        transports.insert(TransportType::Quic, Box::new(QuicTransport::new()));
        transports.insert(TransportType::Tcp, Box::new(TcpTransport::new()));
        
        Self {
            transports,
            active_transport: RwLock::new(TransportType::Grpc), // 默认使用gRPC
            monitor: NetworkMonitor::new(),
        }
    }
    
    pub fn start_monitoring(&self) {
        let transports = self.transports.clone();
        let active_transport = self.active_transport.clone();
        let monitor = self.monitor.clone();
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_secs(30));
            
            loop {
                interval.tick().await;
                
                // 获取当前网络特性
                let characteristics = monitor.measure().await;
                
                // 确定最佳传输
                let best_transport = Self::select_best_transport(&characteristics);
                
                // 更新活动传输
                if best_transport != *active_transport.read().unwrap() {
                    let mut active = active_transport.write().unwrap();
                    *active = best_transport;
                    log::info!("Switched to transport: {:?}", best_transport);
                }
            }
        });
    }
    
    fn select_best_transport(characteristics: &TransportCharacteristics) -> TransportType {
        // 根据网络特性选择最佳传输
        if characteristics.reliability < 0.8 {
            // 不可靠网络优先使用QUIC
            return TransportType::Quic;
        }
        
        if characteristics.latency < Duration::from_millis(10) && characteristics.throughput > 100_000_000 {
            // 低延迟高带宽优先使用gRPC
            return TransportType::Grpc;
        }
        
        // 默认使用TCP
        TransportType::Tcp
    }
}

#[async_trait]
impl Transport for AdaptiveTransport {
    async fn send(&self, target: NodeId, message: Message) -> Result<(), TransportError> {
        let transport_type = *self.active_transport.read().unwrap();
        let transport = self.transports.get(&transport_type)
            .ok_or(TransportError::UnsupportedTransport)?;
            
        transport.send(target, message).await
    }
    
    // 其他方法实现...
}
```

## 10. 可扩展性与性能优化

### 10.1 自动分片策略

```rust
/// 分片键生成器特征
pub trait ShardKeyGenerator: Send + Sync {
    fn generate_key(&self, data: &[u8]) -> ShardKey;
}

/// 分片管理器
pub struct ShardManager {
    shard_count: usize,
    key_generator: Box<dyn ShardKeyGenerator>,
    shard_map: RwLock<HashMap<ShardKey, NodeId>>,
    rebalance_policy: Box<dyn RebalancePolicy>,
}

impl ShardManager {
    pub fn new(
        shard_count: usize, 
        key_generator: Box<dyn ShardKeyGenerator>,
        rebalance_policy: Box<dyn RebalancePolicy>
    ) -> Self {
        Self {
            shard_count,
            key_generator,
            shard_map: RwLock::new(HashMap::new()),
            rebalance_policy,
        }
    }
    
    pub async fn assign_shards(&self, nodes: &[NodeId]) -> Result<(), ShardError> {
        let mut map = self.shard_map.write().unwrap();
        
        // 生成初始分片分配
        for shard_id in 0..self.shard_count {
            let shard_key = ShardKey(shard_id as u64);
            let node_idx = shard_id % nodes.len();
            map.insert(shard_key, nodes[node_idx].clone());
        }
        
        Ok(())
    }
    
    pub async fn rebalance(&self, nodes: &[NodeId]) -> Result<Vec<ShardMovement>, ShardError> {
        // 实现分片再平衡逻辑
        let current_map = self.shard_map.read().unwrap().clone();
        let movements = self.rebalance_policy.calculate_movements(&current_map, nodes);
        
        // 应用移动
        let mut map = self.shard_map.write().unwrap();
        for movement in &movements {
            map.insert(movement.shard_key, movement.target_node.clone());
        }
        
        Ok(movements)
    }
    
    pub fn get_shard_for_data(&self, data: &[u8]) -> Result<(ShardKey, NodeId), ShardError> {
        let key = self.key_generator.generate_key(data);
        let map = self.shard_map.read().unwrap();
        
        match map.get(&key) {
            Some(node) => Ok((key, node.clone())),
            None => Err(ShardError::ShardNotFound),
        }
    }
}
```

### 10.2 本地性优化与缓存策略

```rust
/// 本地性感知路由
pub struct LocalityAwareRouter {
    node_locations: HashMap<NodeId, GeoLocation>,
    current_location: GeoLocation,
    global_nodes: Vec<NodeId>,
    regional_nodes: RwLock<HashMap<Region, Vec<NodeId>>>,
}

impl LocalityAwareRouter {
    pub fn new(current_location: GeoLocation) -> Self {
        Self {
            node_locations: HashMap::new(),
            current_location,
            global_nodes: Vec::new(),
            regional_nodes: RwLock::new(HashMap::new()),
        }
    }
    
    pub fn add_node(&mut self, node_id: NodeId, location: GeoLocation) {
        self.node_locations.insert(node_id.clone(), location);
        
        if location.is_global() {
            self.global_nodes.push(node_id.clone());
        } else {
            let mut regional = self.regional_nodes.write().unwrap();
            regional.entry(location.region)
                .or_insert_with(Vec::new)
                .push(node_id);
        }
    }
    
    pub fn route_request(&self, request: &Request) -> NodeId {
        // 尝试选择最近的节点
        if let Some(preferred_region) = request.preferred_region() {
            if let Some(regional_nodes) = self.regional_nodes.read().unwrap().get(&preferred_region) {
                if !regional_nodes.is_empty() {
                    // 选择区域内随机节点
                    let idx = rand::thread_rng().gen_range(0..regional_nodes.len());
                    return regional_nodes[idx].clone();
                }
            }
        }
        
        // 后备选择全局节点
        if !self.global_nodes.is_empty() {
            let idx = rand::thread_rng().gen_range(0..self.global_nodes.len());
            return self.global_nodes[idx].clone();
        }
        
        // 无可用节点，选择任意节点
        let all_nodes: Vec<_> = self.node_locations.keys().cloned().collect();
        let idx = rand::thread_rng().gen_range(0..all_nodes.len());
        all_nodes[idx].clone()
    }
}

/// 多级缓存策略
pub struct MultiLevelCache<K, V> 
where 
    K: Hash + Eq + Clone,
    V: Clone + Send + Sync + 'static,
{
    l1: moka::sync::Cache<K, V>,
    l2: Arc<dyn RemoteCache<K, V>>,
    metrics: CacheMetrics,
}

impl<K, V> MultiLevelCache<K, V> 
where 
    K: Hash + Eq + Clone + Send + Sync + 'static,
    V: Clone + Send + Sync + 'static,
{
    pub fn new(l1_size: u64, l2: Arc<dyn RemoteCache<K, V>>) -> Self {
        let l1 = moka::sync::Cache::builder()
            .max_capacity(l1_size)
            .time_to_live(Duration::from_secs(60))
            .build();
            
        Self {
            l1,
            l2,
            metrics: CacheMetrics::new(),
        }
    }
    
    pub async fn get(&self, key: &K) -> Option<V> {
        // 尝试L1缓存
        if let Some(value) = self.l1.get(key) {
            self.metrics.record_l1_hit();
            return Some(value);
        }
        
        self.metrics.record_l1_miss();
        
        // 尝试L2缓存
        if let Some(value) = self.l2.get(key).await {
            // 更新L1缓存
            let value_clone = value.clone();
            let key_clone = key.clone();
            self.l1.insert(key_clone, value_clone);
            
            self.metrics.record_l2_hit();
            return Some(value);
        }
        
        self.metrics.record_l2_miss();
        None
    }
    
    pub async fn put(&self, key: K, value: V) -> Result<(), CacheError> {
        // 更新L1缓存
        self.l1.insert(key.clone(), value.clone());
        
        // 异步更新L2缓存
        self.l2.put(key, value).await?;
        
        self.metrics.record_put();
        Ok(())
    }
}
```

### 10.3 自动批处理与压缩

```rust
/// 批处理管理器
pub struct BatchManager<T> {
    batch_size: usize,
    max_delay: Duration,
    sender: mpsc::Sender<(T, oneshot::Sender<Result<(), BatchError>>)>,
    processor: Arc<dyn BatchProcessor<T>>,
}

impl<T: Send + 'static> BatchManager<T> {
    pub fn new(
        batch_size: usize,
        max_delay: Duration,
        processor: Arc<dyn BatchProcessor<T>>,
    ) -> Self {
        let (sender, receiver) = mpsc::channel(1000);
        
        // 启动批处理任务
        let processor_clone = processor.clone();
        tokio::spawn(async move {
            Self::process_batches(receiver, batch_size, max_delay, processor_clone).await;
        });
        
        Self {
            batch_size,
            max_delay,
            sender,
            processor,
        }
    }
    
    pub async fn submit(&self, item: T) -> Result<(), BatchError> {
        let (response_tx, response_rx) = oneshot::channel();
        self.sender.send((item, response_tx)).await
            .map_err(|_| BatchError::ChannelClosed)?;
            
        response_rx.await
            .map_err(|_| BatchError::ResponseDropped)?
    }
    
    async fn process_batches(
        mut receiver: mpsc::Receiver<(T, oneshot::Sender<Result<(), BatchError>>)>,
        batch_size: usize,
        max_delay: Duration,
        processor: Arc<dyn BatchProcessor<T>>,
    ) {
        let mut current_batch = Vec::new();
        let mut response_channels = Vec::new();
        let mut batch_timer = tokio::time::interval(max_delay);
        
        loop {
            tokio::select! {
                // 接收新项目
                item = receiver.recv() => {
                    match item {
                        Some((item, response)) => {
                            current_batch.push(item);
                            response_channels.push(response);
                            
                            // 检查批次是否已满
                            if current_batch.len() >= batch_size {
                                Self::process_current_batch(
                                    &mut current_batch,
                                    &mut response_channels,
                                    &processor
                                ).await;
                            }
                        }
                        None => {
                            // 发送方已关闭
                            break;
                        }
                    }
                }
                
                // 超时处理当前批次
                _ = batch_timer.tick() => {
                    if !current_batch.is_empty() {
                        Self::process_current_batch(
                            &mut current_batch,
                            &mut response_channels,
                            &processor
                        ).await;
                    }
                }
            }
        }
    }
    
    async fn process_current_batch(
        batch: &mut Vec<T>,
        channels: &mut Vec<oneshot::Sender<Result<(), BatchError>>>,
        processor: &Arc<dyn BatchProcessor<T>>,
    ) {
        // 取出当前批次
        let current_batch = std::mem::take(batch);
        let current_channels = std::mem::take(channels);
        
        // 处理批次
        let result = processor.process_batch(current_batch).await;
        
        // 发送结果
        for channel in current_channels {
            let _ = channel.send(result.clone());
        }
    }
}

/// 数据压缩管理器
pub struct CompressionManager {
    automatic: bool,
    algorithms: HashMap<CompressionAlgorithm, Box<dyn CompressionCodec>>,
    default_algorithm: CompressionAlgorithm,
    threshold_bytes: usize,
}

impl CompressionManager {
    pub fn new(automatic: bool, threshold_bytes: usize) -> Self {
        let mut algorithms = HashMap::new();
        
        // 注册默认压缩算法
        algorithms.insert(CompressionAlgorithm::Gzip, Box::new(GzipCodec::new(5)));
        algorithms.insert(CompressionAlgorithm::Zstd, Box::new(ZstdCodec::new(3)));
        algorithms.insert(CompressionAlgorithm::Lz4, Box::new(Lz4Codec::new()));
        
        Self {
            automatic,
            algorithms,
            default_algorithm: CompressionAlgorithm::Zstd,
            threshold_bytes,
        }
    }
    
    pub async fn should_compress(&self, data: &[u8]) -> bool {
        if !self.automatic {
            return false;
        }
        
        data.len() > self.threshold_bytes
    }
    
    pub async fn compress(
        &self, 
        data: &[u8], 
        algorithm: Option<CompressionAlgorithm>
    ) -> Result<Vec<u8>, CompressionError> {
        if data.is_empty() {
            return Ok(vec![]);
        }
        
        let algo = algorithm.unwrap_or(self.default_algorithm);
        
        let codec = self.algorithms.get(&algo)
            .ok_or(CompressionError::UnsupportedAlgorithm)?;
            
        codec.compress(data).await
    }
    
    pub async fn decompress(
        &self,
        data: &[u8],
        algorithm: CompressionAlgorithm,
    ) -> Result<Vec<u8>, CompressionError> {
        if data.is_empty() {
            return Ok(vec![]);
        }
        
        let codec = self.algorithms.get(&algorithm)
            .ok_or(CompressionError::UnsupportedAlgorithm)?;
            
        codec.decompress(data).await
    }
}
```

## 11. 高级容错模式

### 11.1 断路器与隔离层

```rust
/// 断路器状态
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum CircuitState {
    Closed,    // 正常运行
    Open,      // 失败后阻止执行
    HalfOpen,  // 尝试恢复
}

/// 断路器实现
pub struct CircuitBreaker {
    name: String,
    state: AtomicU8,
    failure_threshold: u32,
    success_threshold: u32,
    reset_timeout: Duration,
    half_open_timeout: Duration,
    failure_counter: AtomicU32,
    success_counter: AtomicU32,
    last_state_change: Mutex<Instant>,
    metrics: CircuitMetrics,
}

impl CircuitBreaker {
    pub fn new(
        name: &str,
        failure_threshold: u32,
        success_threshold: u32,
        reset_timeout: Duration,
    ) -> Self {
        Self {
            name: name.to_string(),
            state: AtomicU8::new(CircuitState::Closed as u8),
            failure_threshold,
            success_threshold,
            reset_timeout,
            half_open_timeout: Duration::from_secs(1),
            failure_counter: AtomicU32::new(0),
            success_counter: AtomicU32::new(0),
            last_state_change: Mutex::new(Instant::now()),
            metrics: CircuitMetrics::new(name),
        }
    }
    
    pub fn current_state(&self) -> CircuitState {
        let state_val = self.state.load(Ordering::SeqCst);
        match state_val {
            0 => CircuitState::Closed,
            1 => CircuitState::Open,
            2 => CircuitState::HalfOpen,
            _ => CircuitState::Closed,
        }
    }
    
    pub async fn execute<F, T, E>(&self, f: F) -> Result<T, CircuitError<E>>
    where
        F: Future<Output = Result<T, E>> + Send,
        E: std::error::Error + Send + Sync + 'static,
    {
        self.update_state();
        
        match self.current_state() {
            CircuitState::Open => {
                self.metrics.record_rejected();
                return Err(CircuitError::CircuitOpen);
            }
            CircuitState::HalfOpen => {
                // 在半开状态下，限制并发请求
                if self.success_counter.load(Ordering::SeqCst) +
                   self.failure_counter.load(Ordering::SeqCst) >= self.success_threshold {
                    self.metrics.record_rejected();
                    return Err(CircuitError::CircuitOpen);
                }
            }
            CircuitState::Closed => {}
        }
        
        let start = Instant::now();
        let result = f.await;
        
        match &result {
            Ok(_) => {
                self.record_success();
                self.metrics.record_success(start.elapsed());
            }
            Err(_) => {
                self.record_failure();
                self.metrics.record_failure(start.elapsed());
            }
        }
        
        result.map_err(CircuitError::UpstreamFailure)
    }
    
    fn update_state(&self) {
        let current_state = self.current_state();
        let last_change = *self.last_state_change.lock().unwrap();
        
        match current_state {
            CircuitState::Open => {
                if last_change.elapsed() >= self.reset_timeout {
                    // 转换到半开状态
                    self.transition_to(CircuitState::HalfOpen);
                }
            }
            CircuitState::HalfOpen => {
                let successes = self.success_counter.load(Ordering::SeqCst);
                let failures = self.failure_counter.load(Ordering::SeqCst);
                
                if successes >= self.success_threshold {
                    // 足够成功，关闭断路器
                    self.transition_to(CircuitState::Closed);
                } else if failures > 0 {
                    // 任何失败都返回到开路状态
                    self.transition_to(CircuitState::Open);
                }
            }
            CircuitState::Closed => {
                let failures = self.failure_counter.load(Ordering::SeqCst);
                if failures >= self.failure_threshold {
                    // 太多失败，打开断路器
                    self.transition_to(CircuitState::Open);
                }
            }
        }
    }
    
    fn transition_to(&self, new_state: CircuitState) {
        let old_state = self.current_state();
        if old_state == new_state {
            return;
        }
        
        self.state.store(new_state as u8, Ordering::SeqCst);
        
        // 重置计数器
        self.failure_counter.store(0, Ordering::SeqCst);
        self.success_counter.store(0, Ordering::SeqCst);
        
        // 更新状态变更时间
        *self.last_state_change.lock().unwrap() = Instant::now();
        
        // 记录状态转换
        self.metrics.record_state_change(old_state, new_state);
        
        log::info!(
            "Circuit breaker '{}' state changed: {:?} -> {:?}",
            self.name, old_state, new_state
        );
    }
    
    fn record_success(&self) {
        self.success_counter.fetch_add(1, Ordering::SeqCst);
        
        if self.current_state() == CircuitState::HalfOpen {
            let successes = self.success_counter.load(Ordering::SeqCst);
            if successes >= self.success_threshold {
                self.transition_to(CircuitState::Closed);
            }
        }
    }
    
    fn record_failure(&self) {
        self.failure_counter.fetch_add(1, Ordering::SeqCst);
        
        match self.current_state() {
            CircuitState::Closed => {
                let failures = self.failure_counter.load(Ordering::SeqCst);
                if failures >= self.failure_threshold {
                    self.transition_to(CircuitState::Open);
                }
            }
            CircuitState::HalfOpen => {
                // 半开状态下的任何失败都会重新打开断路器
                self.transition_to(CircuitState::Open);
            }
            _ => {}
        }
    }
}
```

### 11.2 节点健康管理

```rust
/// 健康检查器
pub struct HealthChecker {
    node_id: NodeId,
    checks: HashMap<String, Box<dyn HealthCheck>>,
    status: AtomicU8, // 0=unknown, 1=healthy, 2=unhealthy
    check_interval: Duration,
    metrics: HealthMetrics,
}

impl HealthChecker {
    pub fn new(node_id: NodeId, check_interval: Duration) -> Self {
        Self {
            node_id,
            checks: HashMap::new(),
            status: AtomicU8::new(0),
            check_interval,
            metrics: HealthMetrics::new(),
        }
    }
    
    pub fn register_check(&mut self, name: &str, check: Box<dyn HealthCheck>) {
        self.checks.insert(name.to_string(), check);
    }
    
    pub fn start(&self) {
        let checks = self.checks.clone();
        let status = self.status.clone();
        let metrics = self.metrics.clone();
        let interval = self.check_interval;
        let node_id = self.node_id.clone();
        
        tokio::spawn(async move {
            let mut check_interval = tokio::time::interval(interval);
            
            loop {
                check_interval.tick().await;
                
                let mut all_healthy = true;
                let mut check_results = Vec::new();
                
                for (name, check) in &checks {
                    let start = Instant::now();
                    let result = check.check().await;
                    let duration = start.elapsed();
                    
                    metrics.record_check_duration(name, duration);
                    
                    match result {
                        Ok(()) => {
                            metrics.record_check_success(name);
                            check_results.push((name.clone(), true));
                        }
                        Err(e) => {
                            all_healthy = false;
                            metrics.record_check_failure(name);
                            log::warn!("Health check '{}' failed: {}", name, e);
                            check_results.push((name.clone(), false));
                        }
                    }
                }
                
                // 更新整体状态
                let new_status = if all_healthy { 1 } else { 2 };
                let old_status = status.swap(new_status, Ordering::SeqCst);
                
                if old_status != new_status {
                    if new_status == 1 {
                        log::info!("Node {} is now healthy", node_id);
                        metrics.record_node_healthy();
                    } else {
                        log::warn!("Node {} is now unhealthy", node_id);
                        metrics.record_node_unhealthy();
                    }
                }
                
                // 发布健康状态
                // 在实际实现中，可能会将结果发布到服务注册中心或监控系统
            }
        });
    }
    
    pub fn is_healthy(&self) -> bool {
        self.status.load(Ordering::SeqCst) == 1
    }
    
    pub async fn get_health_report(&self) -> HealthReport {
        let mut report = HealthReport {
            node_id: self.node_id.clone(),
            timestamp: Utc::now(),
            checks: Vec::new(),
            status: if self.is_healthy() {
                HealthStatus::Healthy
            } else {
                HealthStatus::Unhealthy
            },
        };
        
        for (name, check) in &self.checks {
            let result = check.check().await;
            report.checks.push(CheckResult {
                name: name.clone(),
                status: match result {
                    Ok(()) => HealthStatus::Healthy,
                    Err(_) => HealthStatus::Unhealthy,
                },
                message: result.err().map(|e| e.to_string()),
                timestamp: Utc::now(),
            });
        }
        
        report
    }
}
```

### 11.3 故障恢复与重播

```rust
/// 事件日志接口
#[async_trait]
pub trait EventLog: Send + Sync {
    async fn append(&self, event: Event) -> Result<u64, EventLogError>;
    async fn read(&self, from: u64, limit: usize) -> Result<Vec<Event>, EventLogError>;
    async fn read_forward(&self, from: u64) -> EventStream;
    async fn latest_offset(&self) -> Result<u64, EventLogError>;
}

/// 故障恢复管理器
pub struct RecoveryManager {
    node_id: NodeId,
    event_log: Arc<dyn EventLog>,
    processors: HashMap<String, Box<dyn EventProcessor>>,
    checkpoint_store: Arc<dyn CheckpointStore>,
}

impl RecoveryManager {
    pub fn new(
        node_id: NodeId,
        event_log: Arc<dyn EventLog>,
        checkpoint_store: Arc<dyn CheckpointStore>,
    ) -> Self {
        Self {
            node_id,
            event_log,
            processors: HashMap::new(),
            checkpoint_store,
        }
    }
    
    pub fn register_processor(&mut self, name: &str, processor: Box<dyn EventProcessor>) {
        self.processors.insert(name.to_string(), processor);
    }
    
    pub async fn recover(&self) -> Result<Vec<RecoveryReport>, RecoveryError> {
        let mut reports = Vec::new();
        
        for (name, processor) in &self.processors {
            // 获取上次检查点
            let checkpoint = self.checkpoint_store.get_checkpoint(name).await?;
            let start_offset = checkpoint.map(|c| c.offset + 1).unwrap_or(0);
            
            // 读取事件进行重放
            let events = self.event_log.read(start_offset, 1000).await?;
            
            if events.is_empty() {
                continue;
            }
            
            log::info!(
                "Recovery for '{}' starting from offset {}, {} events to process",
                name, start_offset, events.len()
            );
            
            // 重放事件
            let start = Instant::now();
            let result = processor.recover(&events).await;
            let duration = start.elapsed();
            
            match result {
                Ok(processed) => {
                    // 更新检查点
                    if let Some(last_event) = events.last() {
                        self.checkpoint_store.save_checkpoint(
                            name,
                            Checkpoint {
                                offset: last_event.offset,
                                timestamp: Utc::now(),
                                metadata: HashMap::new(),
                            },
                        ).await?;
                    }
                    
                    reports.push(RecoveryReport {
                        processor: name.clone(),
                        start_offset,
                        end_offset: if let Some(last) = events.last() {
                            last.offset
                        } else {
                            start_offset
                        },
                        processed,
                        duration,
                        success: true,
                        error: None,
                    });
                    
                    log::info!(
                        "Recovery for '{}' completed: {} events processed in {:?}",
                        name, processed, duration
                    );
                }
                Err(e) => {
                    let error_msg = e.to_string();
                    
                    reports.push(RecoveryReport {
                        processor: name.clone(),
                        start_offset,
                        end_offset: start_offset,
                        processed: 0,
                        duration,
                        success: false,
                        error: Some(error_msg.clone()),
                    });
                    
                    log::error!("Recovery for '{}' failed: {}", name, error_msg);
                }
            }
        }
        
        Ok(reports)
    }
    
    pub async fn start_processing(&self) -> Vec<JoinHandle<()>> {
        let mut handles = Vec::new();
        
        for (name, processor) in &self.processors {
            let name = name.clone();
            let processor = processor.clone();
            let event_log = self.event_log.clone();
            let checkpoint_store = self.checkpoint_store.clone();
            
            let handle = tokio::spawn(async move {
                // 获取上次检查点
                let checkpoint = match checkpoint_store.get_checkpoint(&name).await {
                    Ok(checkpoint) => checkpoint,
                    Err(e) => {
                        log::error!("Failed to get checkpoint for '{}': {}", name, e);
                        return;
                    }
                };
                
                let start_offset = checkpoint.map(|c| c.offset + 1).unwrap_or(0);
                
                // 创建事件流
                let mut stream = match event_log.read_forward(start_offset).await {
                    Ok(stream) => stream,
                    Err(e) => {
                        log::error!("Failed to create event stream for '{}': {}", name, e);
                        return;
                    }
                };
                
                let mut last_saved_offset = start_offset;
                let mut events_processed = 0;
                
                log::info!("Started event processing for '{}' from offset {}", name, start_offset);
                
                while let Some(event) = stream.next().await {
                    match processor.process(&event).await {
                        Ok(()) => {
                            events_processed += 1;
                            
                            // 每处理100个事件更新一次检查点
                            if events_processed % 100 == 0 || event.offset - last_saved_offset > 1000 {
                                if let Err(e) = checkpoint_store.save_checkpoint(
                                    &name,
                                    Checkpoint {
                                        offset: event.offset,
                                        timestamp: Utc::now(),
                                        metadata: HashMap::new(),
                                    },
                                ).await {
                                    log::error!("Failed to save checkpoint for '{}': {}", name, e);
                                }
                                
                                last_saved_offset = event.offset;
                                log::debug!(
                                    "Checkpoint updated for '{}' at offset {}, {} events processed",
                                    name, event.offset, events_processed
                                );
                            }
                        }
                        Err(e) => {
                            log::error!(
                                "Failed to process event at offset {} for '{}': {}",
                                event.offset, name, e
                            );
                            
                            // 根据错误策略决定是继续还是停止
                            // 这里简单地继续处理后续事件
                        }
                    }
                }
            });
            
            handles.push(handle);
        }
        
        handles
    }
}

/// 检查点存储接口
#[async_trait]
pub trait CheckpointStore: Send + Sync {
    async fn save_checkpoint(&self, processor: &str, checkpoint: Checkpoint) -> Result<(), CheckpointError>;
    async fn get_checkpoint(&self, processor: &str) -> Result<Option<Checkpoint>, CheckpointError>;
}

/// 事件处理器接口
#[async_trait]
pub trait EventProcessor: Send + Sync + Clone {
    async fn process(&self, event: &Event) -> Result<(), ProcessorError>;
    async fn recover(&self, events: &[Event]) -> Result<usize, ProcessorError>;
}

/// 检查点数据
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Checkpoint {
    pub offset: u64,
    pub timestamp: DateTime<Utc>,
    pub metadata: HashMap<String, String>,
}

/// 恢复报告
#[derive(Clone, Debug)]
pub struct RecoveryReport {
    pub processor: String,
    pub start_offset: u64,
    pub end_offset: u64,
    pub processed: usize,
    pub duration: Duration,
    pub success: bool,
    pub error: Option<String>,
}
```

## 12. 高级网络与通信模式

### 12.1 混合通信模型

```rust
/// 通信模式
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CommunicationMode {
    Synchronous,
    Asynchronous,
    BulkTransfer,
    StreamProcessing,
}

/// 混合通信管理器
pub struct HybridCommunicator {
    node_id: NodeId,
    sync_transport: Arc<dyn SynchronousTransport>,
    async_transport: Arc<dyn AsynchronousTransport>,
    bulk_transport: Arc<dyn BulkTransport>,
    stream_transport: Arc<dyn StreamTransport>,
    mode_selector: Arc<dyn CommunicationModeSelector>,
}

impl HybridCommunicator {
    pub fn new(
        node_id: NodeId,
        sync_transport: Arc<dyn SynchronousTransport>,
        async_transport: Arc<dyn AsynchronousTransport>,
        bulk_transport: Arc<dyn BulkTransport>,
        stream_transport: Arc<dyn StreamTransport>,
        mode_selector: Arc<dyn CommunicationModeSelector>,
    ) -> Self {
        Self {
            node_id,
            sync_transport,
            async_transport,
            bulk_transport,
            stream_transport,
            mode_selector,
        }
    }
    
    pub async fn send_message(&self, target: &NodeId, message: Message) -> Result<Option<Message>, CommunicationError> {
        // 选择通信模式
        let mode = self.mode_selector.select_mode(target, &message).await;
        
        match mode {
            CommunicationMode::Synchronous => {
                // 使用同步传输
                self.sync_transport.send_and_receive(target, message).await
            }
            CommunicationMode::Asynchronous => {
                // 使用异步传输
                self.async_transport.send(target, message).await?;
                Ok(None) // 异步模式没有立即响应
            }
            CommunicationMode::BulkTransfer => {
                // 使用批量传输
                self.bulk_transport.send_bulk(target, vec![message]).await?;
                Ok(None)
            }
            CommunicationMode::StreamProcessing => {
                // 创建单消息流
                let (mut tx, mut rx) = mpsc::channel(1);
                tx.send(message).await.unwrap();
                drop(tx); // 关闭发送端以结束流
                
                // 使用流传输
                let mut response_stream = self.stream_transport.send_stream(target, rx).await?;
                
                // 获取第一个响应
                match response_stream.next().await {
                    Some(response) => Ok(Some(response)),
                    None => Ok(None),
                }
            }
        }
    }
    
    pub async fn send_stream(
        &self,
        target: &NodeId,
        message_stream: mpsc::Receiver<Message>,
    ) -> Result<mpsc::Receiver<Message>, CommunicationError> {
        // 直接使用流传输
        self.stream_transport.send_stream(target, message_stream).await
    }
    
    pub async fn send_bulk(
        &self,
        target: &NodeId,
        messages: Vec<Message>,
    ) -> Result<(), CommunicationError> {
        // 直接使用批量传输
        self.bulk_transport.send_bulk(target, messages).await
    }
}

/// 通信模式选择器接口
#[async_trait]
pub trait CommunicationModeSelector: Send + Sync {
    async fn select_mode(&self, target: &NodeId, message: &Message) -> CommunicationMode;
}

/// 自适应通信选择器实现
pub struct AdaptiveModeSelector {
    message_sizes: RwLock<HashMap<MessageType, ExponentialMovingAverage>>,
    node_latencies: RwLock<HashMap<NodeId, ExponentialMovingAverage>>,
    bulk_threshold: usize,
    high_latency_threshold: Duration,
}

impl AdaptiveModeSelector {
    pub fn new(bulk_threshold: usize, high_latency_threshold: Duration) -> Self {
        Self {
            message_sizes: RwLock::new(HashMap::new()),
            node_latencies: RwLock::new(HashMap::new()),
            bulk_threshold,
            high_latency_threshold,
        }
    }
    
    pub fn update_message_size(&self, message_type: MessageType, size: usize) {
        let mut sizes = self.message_sizes.write().unwrap();
        let avg = sizes.entry(message_type).or_insert_with(|| {
            ExponentialMovingAverage::new(0.3)
        });
        avg.update(size as f64);
    }
    
    pub fn update_node_latency(&self, node_id: &NodeId, latency: Duration) {
        let mut latencies = self.node_latencies.write().unwrap();
        let avg = latencies.entry(node_id.clone()).or_insert_with(|| {
            ExponentialMovingAverage::new(0.3)
        });
        avg.update(latency.as_millis() as f64);
    }
}

#[async_trait]
impl CommunicationModeSelector for AdaptiveModeSelector {
    async fn select_mode(&self, target: &NodeId, message: &Message) -> CommunicationMode {
        // 检查消息大小
        let message_size = message.encoded_size();
        
        // 更新统计数据
        self.update_message_size(message.message_type(), message_size);
        
        // 检查流处理需求
        if message.is_stream_compatible() {
            return CommunicationMode::StreamProcessing;
        }
        
        // 检查消息大小是否超过批量阈值
        if message_size > self.bulk_threshold {
            return CommunicationMode::BulkTransfer;
        }
        
        // 检查节点延迟
        let high_latency = {
            let latencies = self.node_latencies.read().unwrap();
            match latencies.get(target) {
                Some(avg) => avg.get() > self.high_latency_threshold.as_millis() as f64,
                None => false, // 没有历史数据，假设低延迟
            }
        };
        
        // 对于高延迟节点或不需要响应的消息，使用异步通信
        if high_latency || !message.requires_response() {
            CommunicationMode::Asynchronous
        } else {
            // 默认使用同步模式
            CommunicationMode::Synchronous
        }
    }
}

/// 指数移动平均
pub struct ExponentialMovingAverage {
    alpha: f64,
    value: AtomicF64,
}

impl ExponentialMovingAverage {
    pub fn new(alpha: f64) -> Self {
        assert!(alpha > 0.0 && alpha <= 1.0);
        Self {
            alpha,
            value: AtomicF64::new(0.0),
        }
    }
    
    pub fn update(&self, new_value: f64) {
        let current = self.value.load(Ordering::Relaxed);
        let new_avg = self.alpha * new_value + (1.0 - self.alpha) * current;
        self.value.store(new_avg, Ordering::Relaxed);
    }
    
    pub fn get(&self) -> f64 {
        self.value.load(Ordering::Relaxed)
    }
}
```

### 12.2 P2P集群协调

```rust
/// P2P集群管理器
pub struct P2PClusterManager {
    node_id: NodeId,
    libp2p: Arc<LibP2PAdapter>,
    discovery: Arc<dyn PeerDiscovery>,
    membership: Arc<MembershipList>,
    router: Arc<P2PRouter>,
    metrics: Arc<P2PMetrics>,
}

impl P2PClusterManager {
    pub fn new(
        node_id: NodeId,
        libp2p: Arc<LibP2PAdapter>,
        discovery: Arc<dyn PeerDiscovery>,
    ) -> Self {
        let membership = Arc::new(MembershipList::new(node_id.clone()));
        let router = Arc::new(P2PRouter::new(node_id.clone(), membership.clone()));
        
        Self {
            node_id,
            libp2p,
            discovery,
            membership,
            router,
            metrics: Arc::new(P2PMetrics::new()),
        }
    }
    
    pub async fn start(&self) -> Result<(), ClusterError> {
        // 启动libp2p节点
        self.libp2p.start().await?;
        
        // 启动发现服务
        self.discovery.start().await?;
        
        // 注册消息处理程序
        self.register_handlers().await?;
        
        // 启动成员资格协议
        self.start_membership_protocol().await?;
        
        // 启动监控任务
        self.start_monitoring();
        
        log::info!("P2P cluster manager started for node {}", self.node_id);
        
        Ok(())
    }
    
    async fn register_handlers(&self) -> Result<(), ClusterError> {
        let membership = self.membership.clone();
        
        // 注册成员更新处理程序
        self.libp2p.register_handler(MessageType::MembershipUpdate, 
            move |from, data| {
                let membership_clone = membership.clone();
                async move {
                    let update: MembershipUpdate = bincode::deserialize(&data)?;
                    membership_clone.apply_update(from, update).await?;
                    Ok(vec![])
                }
            }
        ).await?;
        
        // 注册路由信息处理程序
        let router = self.router.clone();
        self.libp2p.register_handler(MessageType::RoutingUpdate,
            move |from, data| {
                let router_clone = router.clone();
                async move {
                    let update: RoutingUpdate = bincode::deserialize(&data)?;
                    router_clone.apply_update(from, update).await?;
                    Ok(vec![])
                }
            }
        ).await?;
        
        Ok(())
    }
    
    async fn start_membership_protocol(&self) -> Result<(), ClusterError> {
        let node_id = self.node_id.clone();
        let libp2p = self.libp2p.clone();
        let membership = self.membership.clone();
        let metrics = self.metrics.clone();
        
        // 创建初始成员资格更新
        let update = MembershipUpdate {
            origin: node_id.clone(),
            origin_incarnation: 1,
            updates: vec![
                MemberUpdate {
                    node_id: node_id.clone(),
                    status: MemberStatus::Alive,
                    incarnation: 1,
                    timestamp: Utc::now(),
                }
            ],
        };
        
        // 应用到本地成员列表
        membership.apply_update(&node_id, update.clone()).await?;
        
        // 定期传播成员资格信息
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_secs(5));
            
            loop {
                interval.tick().await;
                
                // 获取当前成员更新
                let members = membership.get_members();
                let active_peers: Vec<_> = members.iter()
                    .filter(|m| m.status == MemberStatus::Alive)
                    .map(|m| m.node_id.clone())
                    .collect();
                    
                metrics.set_active_peer_count(active_peers.len());
                
                if active_peers.is_empty() {
                    continue;
                }
                
                // 创建成员更新
                let update = membership.create_update();
                
                // 随机选择一些节点进行传播
                let target_count = std::cmp::min(
                    3,
                    active_peers.len()
                );
                
                let mut rng = rand::thread_rng();
                let targets: Vec<_> = active_peers.choose_multiple(&mut rng, target_count).cloned().collect();
                
                for target in targets {
                    if target == node_id {
                        continue;
                    }
                    
                    // 序列化和发送更新
                    match bincode::serialize(&update) {
                        Ok(data) => {
                            if let Err(e) = libp2p.send_message(
                                &target,
                                MessageType::MembershipUpdate,
                                data,
                            ).await {
                                log::warn!("Failed to send membership update to {}: {}", target, e);
                            } else {
                                metrics.record_membership_message_sent();
                            }
                        }
                        Err(e) => {
                            log::error!("Failed to serialize membership update: {}", e);
                        }
                    }
                }
            }
        });
        
        Ok(())
    }
    
    fn start_monitoring(&self) {
        let membership = self.membership.clone();
        let router = self.router.clone();
        let metrics = self.metrics.clone();
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_secs(60));
            
            loop {
                interval.tick().await;
                
                // 收集并记录指标
                let members = membership.get_members();
                let active_members = members.iter()
                    .filter(|m| m.status == MemberStatus::Alive)
                    .count();
                    
                let suspect_members = members.iter()
                    .filter(|m| m.status == MemberStatus::Suspect)
                    .count();
                    
                let dead_members = members.iter()
                    .filter(|m| m.status == MemberStatus::Dead)
                    .count();
                    
                metrics.set_active_peer_count(active_members);
                metrics.set_suspect_peer_count(suspect_members);
                metrics.set_dead_peer_count(dead_members);
                
                // 路由信息
                let routes = router.get_routes();
                metrics.set_route_count(routes.len());
                
                // 计算平均跳数
                let total_hops: usize = routes.values().map(|r| r.hops.len()).sum();
                let avg_hops = if routes.is_empty() {
                    0.0
                } else {
                    total_hops as f64 / routes.len() as f64
                };
                
                metrics.set_average_route_hops(avg_hops);
                
                // 记录直接连接的节点数
                let direct_connections = router.get_direct_connections().len();
                metrics.set_direct_connection_count(direct_connections);
            }
        });
    }
    
    pub async fn get_members(&self) -> Vec<ClusterMember> {
        self.membership.get_members()
    }
    
    pub async fn get_active_members(&self) -> Vec<ClusterMember> {
        self.membership.get_members().into_iter()
            .filter(|m| m.status == MemberStatus::Alive)
            .collect()
    }
    
    pub async fn get_route(&self, target: &NodeId) -> Option<Route> {
        self.router.get_route(target)
    }
    
    pub async fn send_message(
        &self,
        target: &NodeId,
        message_type: MessageType,
        data: Vec<u8>,
    ) -> Result<Vec<u8>, ClusterError> {
        // 获取路由
        let route = match self.router.get_route(target) {
            Some(route) => route,
            None => return Err(ClusterError::NoRouteToHost),
        };
        
        // 根据路由发送消息
        if route.hops.is_empty() {
            // 直接连接
            self.libp2p.send_message(target, message_type, data).await
        } else {
            // 使用中继路由
            let next_hop = &route.hops[0];
            
            // 创建路由信封
            let envelope = RoutedMessage {
                target: target.clone(),
                source: self.node_id.clone(),
                message_type,
                data,
                route: route.clone(),
                hop_count: 0,
                timestamp: Utc::now(),
            };
            
            let envelope_data = bincode::serialize(&envelope)?;
            
            // 发送到下一跳
            self.libp2p.send_message(next_hop, MessageType::RoutedMessage, envelope_data).await
        }
    }
}
```

## 13. 分布式应用模式与案例

### 13.1 边缘计算架构

```rust
/// 边缘节点管理器
pub struct EdgeNodeManager {
    node_id: NodeId,
    config: EdgeNodeConfig,
    cloud_connector: Option<Arc<CloudConnector>>,
    local_state: Arc<dyn StateStore>,
    task_executor: Arc<EdgeTaskExecutor>,
    data_processor: Arc<DataProcessor>,
    health_monitor: Arc<HealthMonitor>,
}

impl EdgeNodeManager {
    pub fn new(
        node_id: NodeId,
        config: EdgeNodeConfig,
        local_state: Arc<dyn StateStore>,
    ) -> Self {
        let task_executor = Arc::new(EdgeTaskExecutor::new(node_id.clone()));
        let data_processor = Arc::new(DataProcessor::new(local_state.clone()));
        let health_monitor = Arc::new(HealthMonitor::new(node_id.clone()));
        
        let cloud_connector = if let Some(cloud_config) = &config.cloud_connection {
            Some(Arc::new(CloudConnector::new(
                node_id.clone(),
                cloud_config.clone(),
            )))
        } else {
            None
        };
        
        Self {
            node_id,
            config,
            cloud_connector,
            local_state,
            task_executor,
            data_processor,
            health_monitor,
        }
    }
    
    pub async fn start(&self) -> Result<(), EdgeError> {
        // 启动健康监控
        self.health_monitor.start();
        
        // 启动本地任务执行器
        self.task_executor.start().await?;
        
        // 启动数据处理器
        self.data_processor.start().await?;
        
        // 连接到云端（如果配置了）
        if let Some(connector) = &self.cloud_connector {
            connector.connect().await?;
            
            // 注册同步处理程序
            self.register_cloud_handlers(connector).await?;
        }
        
        log::info!("Edge node {} started successfully", self.node_id);
        
        Ok(())
    }
    
    async fn register_cloud_handlers(&self, connector: &CloudConnector) -> Result<(), EdgeError> {
        let task_executor = self.task_executor.clone();
        
        // 注册任务处理程序
        connector.register_handler("task.submit", move |payload| {
            let executor = task_executor.clone();
            async move {
                let task: EdgeTask = serde_json::from_slice(&payload)?;
                executor.submit_task(task).await?;
                Ok(json!({"status": "accepted"}).to_string().into_bytes())
            }
        }).await?;
        
        // 注册数据同步处理程序
        let data_processor = self.data_processor.clone();
        connector.register_handler("data.sync", move |payload| {
            let processor = data_processor.clone();
            async move {
                let sync_request: DataSyncRequest = serde_json::from_slice(&payload)?;
                let result = processor.handle_sync_request(&sync_request).await?;
                Ok(serde_json::to_vec(&result)?)
            }
        }).await?;
        
        Ok(())
    }
    
    pub async fn submit_local_data(&self, data: EdgeData) -> Result<DataProcessResult, EdgeError> {
        // 处理本地数据
        let result = self.data_processor.process_data(data.clone()).await?;
        
        // 如果设置了自动同步且连接到云端，安排数据同步
        if self.config.auto_sync_data && self.cloud_connector.is_some() {
            let connector = self.cloud_connector.as_ref().unwrap();
            let data_clone = data.clone();
            
            tokio::spawn(async move {
                if let Err(e) = connector.sync_data(&data_clone).await {
                    log::error!("Failed to sync data to cloud: {}", e);
                }
            });
        }
        
        Ok(result)
    }
    
    pub async fn get_cloud_connection_status(&self) -> Option<ConnectionStatus> {
        match &self.cloud_connector {
            Some(connector) => Some(connector.get_status().await),
            None => None,
        }
    }
    
    pub async fn force_sync(&self) -> Result<SyncStats, EdgeError> {
        if let Some(connector) = &self.cloud_connector {
            connector.force_sync().await
        } else {
            Err(EdgeError::CloudNotConfigured)
        }
    }
}

/// 云连接器
pub struct CloudConnector {
    node_id: NodeId,
    config: CloudConnectionConfig,
    client: Arc<dyn CloudClient>,
    status: Mutex<ConnectionStatus>,
    sync_manager: SyncManager,
    handlers: RwLock<HashMap<String, HandlerFn>>,
}

impl CloudConnector {
    pub fn new(node_id: NodeId, config: CloudConnectionConfig) -> Self {
        let client: Arc<dyn CloudClient> = match config.protocol {
            CloudProtocol::Mqtt => Arc::new(MqttCloudClient::new(&config)),
            CloudProtocol::Http => Arc::new(HttpCloudClient::new(&config)),
            CloudProtocol::Grpc => Arc::new(GrpcCloudClient::new(&config)),
        };
        
        Self {
            node_id,
            config,
            client,
            status: Mutex::new(ConnectionStatus::Disconnected),
            sync_manager: SyncManager::new(),
            handlers: RwLock::new(HashMap::new()),
        }
    }
    
    pub async fn connect(&self) -> Result<(), EdgeError> {
        log::info!("Connecting to cloud service at {}", self.config.endpoint);
        
        match self.client.connect().await {
            Ok(()) => {
                *self.status.lock().unwrap() = ConnectionStatus::Connected;
                log::info!("Connected to cloud service successfully");
                
                // 启动消息监听
                self.start_message_listener();
                
                // 启动保活机制
                self.start_keep_alive();
                
                Ok(())
            }
            Err(e) => {
                *self.status.lock().unwrap() = ConnectionStatus::Error(e.to_string());
                log::error!("Failed to connect to cloud service: {}", e);
                Err(EdgeError::CloudConnectionFailed(e.to_string()))
            }
        }
    }
    
    fn start_message_listener(&self) {
        let client = self.client.clone();
        let handlers = self.handlers.clone();
        let status = self.status.clone();
        
        tokio::spawn(async move {
            loop {
                match client.receive_message().await {
                    Ok(message) => {
                        let topic = message.topic.clone();
                        let payload = message.payload.clone();
                        
                        // 寻找匹配的处理程序
                        let handler_opt = {
                            let handlers_guard = handlers.read().unwrap();
                            handlers_guard.get(&topic).cloned()
                        };
                        
                        if let Some(handler) = handler_opt {
                            // 处理消息
                            tokio::spawn(async move {
                                match handler(payload).await {
                                    Ok(response) => {
                                        if !message.response_topic.is_empty() {
                                            if let Err(e) = client.send_message(
                                                &CloudMessage {
                                                    topic: message.response_topic,
                                                    payload: response,
                                                    response_topic: String::new(),
                                                    correlation_id: message.correlation_id,
                                                },
                                            ).await {
                                                log::error!("Failed to send response: {}", e);
                                            }
                                        }
                                    }
                                    Err(e) => {
                                        log::error!("Error handling message: {}", e);
                                        
                                        // 发送错误响应
                                        if !message.response_topic.is_empty() {
                                            let error_response = json!({
                                                "error": e.to_string()
                                            }).to_string().into_bytes();
                                            
                                            if let Err(e) = client.send_message(
                                                &CloudMessage {
                                                    topic: message.response_topic,
                                                    payload: error_response,
                                                    response_topic: String::new(),
                                                    correlation_id: message.correlation_id,
                                                },
                                            ).await {
                                                log::error!("Failed to send error response: {}", e);
                                            }
                                        }
                                    }
                                }
                            });
                        } else {
                            log::warn!("No handler registered for topic: {}", topic);
                        }
                    }
                    Err(e) => {
                        log::error!("Error receiving message: {}", e);
                        
                        // 更新连接状态
                        *status.lock().unwrap() = ConnectionStatus::Error(e.to_string());
                        
                        // 尝试重新连接
                        tokio::time::sleep(Duration::from_secs(5)).await;
                        
                        if let Err(e) = client.connect().await {
                            log::error!("Failed to reconnect: {}", e);
                        } else {
                            *status.lock().unwrap() = ConnectionStatus::Connected;
                            log::info!("Reconnected to cloud service");
                        }
                    }
                }
            }
        });
    }
    
    fn start_keep_alive(&self) {
        let client = self.client.clone();
        let status = self.status.clone();
        let interval = self.config.keep_alive_interval;
        let node_id = self.node_id.clone();
        
        tokio::spawn(async move {
            let mut keep_alive_interval = tokio::time::interval(interval);
            
            loop {
                keep_alive_interval.tick().await;
                
                // 发送保活消息
                let keep_alive = CloudMessage {
                    topic: "edge.keepalive".to_string(),
                    payload: json!({
                        "node_id": node_id,
                        "timestamp": Utc::now().to_rfc3339(),
                        "status": "active"
                    }).to_string().into_bytes(),
                    response_topic: String::new(),
                    correlation_id: String::new(),
                };
                
                if let Err(e) = client.send_message(&keep_alive).await {
                    log::warn!("Failed to send keep-alive: {}", e);
                    
                    // 更新连接状态
                    *status.lock().unwrap() = ConnectionStatus::Error(e.to_string());
                    
                    // 尝试重新连接
                    if let Err(e) = client.connect().await {
                        log::error!("Failed to reconnect: {}", e);
                    } else {
                        *status.lock().unwrap() = ConnectionStatus::Connected;
                        log::info!("Reconnected to cloud service");
                    }
                }
            }
        });
    }
    
    pub async fn register_handler<F, Fut>(&self, topic: &str, handler: F) -> Result<(), EdgeError>
    where
        F: Fn(Vec<u8>) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = Result<Vec<u8>, Box<dyn std::error::Error + Send + Sync>>> + Send,
    {
        let handler_fn = Box::new(move |payload: Vec<u8>| {
            let future = handler(payload);
            Box::pin(future) as HandlerFutureBox
        });
        
        // 注册处理程序
        {
            let mut handlers = self.handlers.write().unwrap();
            handlers.insert(topic.to_string(), handler_fn);
        }
        
        // 订阅主题
        if let ConnectionStatus::Connected = *self.status.lock().unwrap() {
            self.client.subscribe(topic).await?;
        }
        
        Ok(())
    }
    
    pub async fn sync_data(&self, data: &EdgeData) -> Result<(), EdgeError> {
        // 创建同步消息
        let message = CloudMessage {
            topic: "edge.data.sync".to_string(),
            payload: serde_json::to_vec(data)?,
            response_topic: format!("edge.data.sync.response.{}", self.node_id),
            correlation_id: Uuid::new_v4().to_string(),
        };
        
        // 发送数据
        self.client.send_message(&message).await?;
        
        // 更新同步统计数据
        self.sync_manager.record_sync(data.id.clone(), data.size());
        
        Ok(())
    }
    
    pub async fn get_status(&self) -> ConnectionStatus {
        self.status.lock().unwrap().clone()
    }
    
    pub async fn force_sync(&self) -> Result<SyncStats, EdgeError> {
        log::info!("Starting forced sync for node {}", self.node_id);
        
        // 实现强制同步逻辑
        // ...
        
        Ok(self.sync_manager.get_stats())
    }
}
```

### 13.2 分布式内容分发网络

```rust
/// 内容分发节点
pub struct CdnNode {
    node_id: NodeId,
    config: CdnConfig,
    content_store: Arc<dyn ContentStore>,
    cache_manager: Arc<CacheManager>,
    routing: Arc<ContentRouter>,
    metrics: Arc<CdnMetrics>,
}

impl CdnNode {
    pub fn new(
        node_id: NodeId,
        config: CdnConfig,
        content_store: Arc<dyn ContentStore>,
    ) -> Self {
        let cache_manager = Arc::new(CacheManager::new(
            config.cache.clone(),
            content_store.clone(),
        ));
        
        let routing = Arc::new(ContentRouter::new(node_id.clone()));
        let metrics = Arc::new(CdnMetrics::new());
        
        Self {
            node_id,
            config,
            content_store,
            cache_manager,
            routing,
            metrics,
        }
    }
    
    pub async fn start(&self) -> Result<(), CdnError> {
        // 启动缓存管理器
        self.cache_manager.start().await?;
        
        // 启动路由表更新
        self.start_routing_updates().await?;
        
        // 启动HTTP服务器
        self.start_http_server().await?;
        
        log::info!("CDN node {} started successfully", self.node_id);
        
        Ok(())
    }
    
    async fn start_routing_updates(&self) -> Result<(), CdnError> {
        // 实现路由更新逻辑
        Ok(())
    }
    
    async fn start_http_server(&self) -> Result<(), CdnError> {
        let addr = self.config.http_bind_address.parse::<SocketAddr>()?;
        let content_store = self.content_store.clone();
        let cache_manager = self.cache_manager.clone();
        let routing = self.routing.clone();
        let metrics = self.metrics.clone();
        
        tokio::spawn(async move {
            let app = Router::new()
                .route("/content/:id", get(move |Path(id): Path<String>, Query(params): Query<HashMap<String, String>>| {
                    let content_store = content_store.clone();
                    let cache_manager = cache_manager.clone();
                    let routing = routing.clone();
                    let metrics = metrics.clone();
                    
                    async move {
                        let start = Instant::now();
                        
                        // 检查是否有范围请求
                        let range = params.get("range").cloned();
                        
                        // 检查本地缓存
                        let result = match cache_manager.get_content(&id, range.as_deref()).await {
                            Ok(Some(content)) => {
                                // 缓存命中
                                metrics.record_cache_hit();
                                metrics.record_request_latency(start.elapsed());
                                
                
<think>需要继续编写分布式内容分发网络的代码实现。上次我们写到了内容分发节点(CdnNode)的HTTP服务器实现部分，特别是get_content路由处理的开始部分。</think>```rust
                                Ok(content)
                            }
                            Ok(None) => {
                                // 缓存未命中
                                metrics.record_cache_miss();
                                
                                // 查找内容路由
                                match routing.find_content(&id).await {
                                    Some(node_id) => {
                                        // 从其他节点获取
                                        match routing.fetch_from_peer(&node_id, &id, range.as_deref()).await {
                                            Ok(content) => {
                                                // 获取成功，存入缓存
                                                if let Err(e) = cache_manager.store_content(&id, &content).await {
                                                    log::error!("Failed to cache content {}: {}", id, e);
                                                }
                                                
                                                metrics.record_peer_fetch_success();
                                                metrics.record_request_latency(start.elapsed());
                                                
                                                Ok(content)
                                            }
                                            Err(e) => {
                                                // 获取失败
                                                metrics.record_peer_fetch_failure();
                                                log::error!("Failed to fetch content {} from peer {}: {}", id, node_id, e);
                                                Err(StatusCode::NOT_FOUND)
                                            }
                                        }
                                    }
                                    None => {
                                        // 尝试从原始源获取
                                        match content_store.fetch_from_origin(&id, range.as_deref()).await {
                                            Ok(content) => {
                                                // 获取成功，存入缓存
                                                if let Err(e) = cache_manager.store_content(&id, &content).await {
                                                    log::error!("Failed to cache content {}: {}", id, e);
                                                }
                                                
                                                // 更新路由信息
                                                routing.advertise_content(&id).await;
                                                
                                                metrics.record_origin_fetch_success();
                                                metrics.record_request_latency(start.elapsed());
                                                
                                                Ok(content)
                                            }
                                            Err(e) => {
                                                // 获取失败
                                                metrics.record_origin_fetch_failure();
                                                log::error!("Failed to fetch content {} from origin: {}", id, e);
                                                Err(StatusCode::NOT_FOUND)
                                            }
                                        }
                                    }
                                }
                            }
                            Err(e) => {
                                // 缓存错误
                                log::error!("Cache error for content {}: {}", id, e);
                                metrics.record_cache_error();
                                Err(StatusCode::INTERNAL_SERVER_ERROR)
                            }
                        };
                        
                        metrics.record_request();
                        result
                    }
                }))
                .route("/content", post(move |body: Bytes| {
                    let content_store = content_store.clone();
                    let routing = routing.clone();
                    let metrics = metrics.clone();
                    
                    async move {
                        let start = Instant::now();
                        
                        // 存储内容
                        match content_store.store_content(&body).await {
                            Ok(id) => {
                                // 更新路由信息
                                routing.advertise_content(&id).await;
                                
                                metrics.record_content_stored(body.len());
                                metrics.record_request_latency(start.elapsed());
                                
                                Ok(id)
                            }
                            Err(e) => {
                                log::error!("Failed to store content: {}", e);
                                metrics.record_storage_error();
                                Err(StatusCode::INTERNAL_SERVER_ERROR)
                            }
                        }
                    }
                }))
                .route("/status", get(move || {
                    let metrics = metrics.clone();
                    let cache_manager = cache_manager.clone();
                    
                    async move {
                        let cache_stats = cache_manager.get_stats().await;
                        let status = json!({
                            "node_id": node_id,
                            "uptime": metrics.get_uptime().as_secs(),
                            "requests": metrics.get_request_count(),
                            "cache_hits": metrics.get_cache_hit_count(),
                            "cache_misses": metrics.get_cache_miss_count(),
                            "cache_size": cache_stats.size_bytes,
                            "cache_items": cache_stats.item_count,
                            "peer_fetches": metrics.get_peer_fetch_count(),
                            "origin_fetches": metrics.get_origin_fetch_count(),
                        });
                        
                        Json(status)
                    }
                }));
                
            let server = axum::Server::bind(&addr)
                .serve(app.into_make_service());
                
            if let Err(e) = server.await {
                log::error!("HTTP server error: {}", e);
            }
        });
        
        Ok(())
    }
    
    pub async fn get_content(&self, id: &str, range: Option<&str>) -> Result<Content, CdnError> {
        let start = Instant::now();
        
        // 尝试从缓存获取
        match self.cache_manager.get_content(id, range).await {
            Ok(Some(content)) => {
                self.metrics.record_cache_hit();
                self.metrics.record_request_latency(start.elapsed());
                return Ok(content);
            }
            Ok(None) => {
                self.metrics.record_cache_miss();
            }
            Err(e) => {
                self.metrics.record_cache_error();
                return Err(e);
            }
        }
        
        // 查找内容路由
        if let Some(node_id) = self.routing.find_content(id).await {
            // 从对等节点获取
            match self.routing.fetch_from_peer(&node_id, id, range).await {
                Ok(content) => {
                    // 存入缓存
                    if let Err(e) = self.cache_manager.store_content(id, &content).await {
                        log::error!("Failed to cache content {}: {}", id, e);
                    }
                    
                    self.metrics.record_peer_fetch_success();
                    self.metrics.record_request_latency(start.elapsed());
                    
                    return Ok(content);
                }
                Err(e) => {
                    self.metrics.record_peer_fetch_failure();
                    log::error!("Failed to fetch from peer {}: {}", node_id, e);
                    // 继续尝试原始源
                }
            }
        }
        
        // 从原始源获取
        match self.content_store.fetch_from_origin(id, range).await {
            Ok(content) => {
                // 存入缓存
                if let Err(e) = self.cache_manager.store_content(id, &content).await {
                    log::error!("Failed to cache content {}: {}", id, e);
                }
                
                // 更新路由信息
                self.routing.advertise_content(id).await;
                
                self.metrics.record_origin_fetch_success();
                self.metrics.record_request_latency(start.elapsed());
                
                Ok(content)
            }
            Err(e) => {
                self.metrics.record_origin_fetch_failure();
                Err(e)
            }
        }
    }
    
    pub async fn store_content(&self, data: &[u8]) -> Result<String, CdnError> {
        let start = Instant::now();
        
        // 存储内容
        match self.content_store.store_content(data).await {
            Ok(id) => {
                // 更新路由信息
                self.routing.advertise_content(&id).await;
                
                self.metrics.record_content_stored(data.len());
                self.metrics.record_request_latency(start.elapsed());
                
                Ok(id)
            }
            Err(e) => {
                self.metrics.record_storage_error();
                Err(e)
            }
        }
    }
}

/// 缓存管理器
pub struct CacheManager {
    config: CacheConfig,
    content_store: Arc<dyn ContentStore>,
    lru_cache: Arc<moka::future::Cache<String, CacheEntry>>,
    metrics: Arc<CacheMetrics>,
}

impl CacheManager {
    pub fn new(config: CacheConfig, content_store: Arc<dyn ContentStore>) -> Self {
        let cache = moka::future::Cache::builder()
            .max_capacity(config.max_items)
            .time_to_live(config.ttl)
            .build();
            
        Self {
            config,
            content_store,
            lru_cache: Arc::new(cache),
            metrics: Arc::new(CacheMetrics::new()),
        }
    }
    
    pub async fn start(&self) -> Result<(), CdnError> {
        // 启动缓存清理
        self.start_cache_cleaning();
        
        // 启动指标收集
        self.start_metrics_collection();
        
        Ok(())
    }
    
    fn start_cache_cleaning(&self) {
        let lru_cache = self.lru_cache.clone();
        let clean_interval = self.config.clean_interval;
        let metrics = self.metrics.clone();
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(clean_interval);
            
            loop {
                interval.tick().await;
                
                // 执行清理
                let before_size = lru_cache.entry_count();
                lru_cache.run_pending_tasks().await;
                let after_size = lru_cache.entry_count();
                
                let cleaned = if before_size > after_size {
                    before_size - after_size
                } else {
                    0
                };
                
                if cleaned > 0 {
                    log::debug!("Cleaned {} cache entries", cleaned);
                    metrics.record_entries_cleaned(cleaned);
                }
            }
        });
    }
    
    fn start_metrics_collection(&self) {
        let lru_cache = self.lru_cache.clone();
        let metrics = self.metrics.clone();
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_secs(60));
            
            loop {
                interval.tick().await;
                
                // 更新指标
                let entry_count = lru_cache.entry_count();
                metrics.set_entry_count(entry_count);
                
                // 估计内存使用
                let estimated_size = lru_cache.entry_count() * 1024; // 粗略估计每个条目1KB
                metrics.set_estimated_size(estimated_size);
            }
        });
    }
    
    pub async fn get_content(&self, id: &str, range: Option<&str>) -> Result<Option<Content>, CdnError> {
        // 构造缓存键
        let cache_key = match range {
            Some(r) => format!("{}:{}", id, r),
            None => id.to_string(),
        };
        
        // 检查缓存
        if let Some(entry) = self.lru_cache.get(&cache_key).await {
            self.metrics.record_hit();
            return Ok(Some(entry.content));
        }
        
        self.metrics.record_miss();
        Ok(None)
    }
    
    pub async fn store_content(&self, id: &str, content: &Content) -> Result<(), CdnError> {
        // 检查大小限制
        if content.data.len() > self.config.max_item_size {
            self.metrics.record_oversized_reject();
            return Err(CdnError::ContentTooLarge);
        }
        
        // 构造缓存条目
        let entry = CacheEntry {
            id: id.to_string(),
            content: content.clone(),
            created_at: Utc::now(),
            last_accessed: AtomicDateTime::new(Utc::now()),
            access_count: AtomicU64::new(1),
        };
        
        // 存储到缓存
        let cache_key = match &content.range {
            Some(r) => format!("{}:{}", id, r),
            None => id.to_string(),
        };
        
        self.lru_cache.insert(cache_key, entry).await;
        self.metrics.record_insert(content.data.len());
        
        Ok(())
    }
    
    pub async fn invalidate(&self, id: &str) -> Result<(), CdnError> {
        // 移除特定ID的所有缓存条目
        let removed = self.lru_cache.invalidate_matching(|key, _| {
            key.starts_with(&format!("{}:", id)) || key == id
        }).await;
        
        self.metrics.record_invalidations(removed as u64);
        log::debug!("Invalidated {} cache entries for ID {}", removed, id);
        
        Ok(())
    }
    
    pub async fn get_stats(&self) -> CacheStats {
        CacheStats {
            item_count: self.lru_cache.entry_count(),
            size_bytes: self.metrics.get_estimated_size(),
            hit_rate: self.metrics.get_hit_rate(),
            miss_rate: self.metrics.get_miss_rate(),
        }
    }
}

/// 内容路由器
pub struct ContentRouter {
    node_id: NodeId,
    routing_table: RwLock<HashMap<String, ContentRoutingEntry>>,
    peers: RwLock<HashMap<NodeId, PeerInfo>>,
    client: Client,
}

impl ContentRouter {
    pub fn new(node_id: NodeId) -> Self {
        Self {
            node_id,
            routing_table: RwLock::new(HashMap::new()),
            peers: RwLock::new(HashMap::new()),
            client: Client::new(),
        }
    }
    
    pub async fn find_content(&self, id: &str) -> Option<NodeId> {
        let table = self.routing_table.read().unwrap();
        
        // 查找内容路由
        if let Some(entry) = table.get(id) {
            // 检查是否是最近添加的内容
            if Utc::now() - entry.last_updated < chrono::Duration::minutes(5) {
                return Some(entry.node_id.clone());
            }
        }
        
        None
    }
    
    pub async fn advertise_content(&self, id: &str) -> () {
        // 更新本地路由表
        {
            let mut table = self.routing_table.write().unwrap();
            table.insert(id.to_string(), ContentRoutingEntry {
                node_id: self.node_id.clone(),
                last_updated: Utc::now(),
                ttl: Some(chrono::Duration::hours(24)),
            });
        }
        
        // 向对等节点广播
        let peers = {
            let peers_guard = self.peers.read().unwrap();
            peers_guard.keys().cloned().collect::<Vec<_>>()
        };
        
        for peer in peers {
            if peer == self.node_id {
                continue;
            }
            
            self.broadcast_to_peer(&peer, id).await;
        }
    }
    
    async fn broadcast_to_peer(&self, peer: &NodeId, id: &str) -> () {
        // 实现对等点通知逻辑
        // 在实际实现中，这可能是通过HTTP、gRPC或其他协议
        
        let peers_guard = self.peers.read().unwrap();
        if let Some(peer_info) = peers_guard.get(peer) {
            let url = format!("http://{}/routing/update", peer_info.address);
            
            let payload = json!({
                "node_id": self.node_id,
                "content_id": id,
                "timestamp": Utc::now().to_rfc3339(),
            });
            
            match self.client.post(&url)
                .json(&payload)
                .timeout(Duration::from_secs(5))
                .send()
                .await {
                    Ok(_) => {
                        log::debug!("Broadcast content {} to peer {}", id, peer);
                    }
                    Err(e) => {
                        log::warn!("Failed to broadcast to peer {}: {}", peer, e);
                    }
                }
        }
    }
    
    pub async fn fetch_from_peer(&self, peer: &NodeId, id: &str, range: Option<&str>) -> Result<Content, CdnError> {
        let peers_guard = self.peers.read().unwrap();
        
        let peer_info = match peers_guard.get(peer) {
            Some(info) => info,
            None => return Err(CdnError::PeerNotFound),
        };
        
        // 构建URL
        let mut url = format!("http://{}/content/{}", peer_info.address, id);
        
        if let Some(r) = range {
            url = format!("{}?range={}", url, r);
        }
        
        // 发送请求
        match self.client.get(&url)
            .timeout(Duration::from_secs(30))
            .send()
            .await {
                Ok(response) => {
                    if !response.status().is_success() {
                        return Err(CdnError::PeerFetchFailed(response.status().to_string()));
                    }
                    
                    let content_type = response.headers()
                        .get(header::CONTENT_TYPE)
                        .and_then(|v| v.to_str().ok())
                        .unwrap_or("application/octet-stream")
                        .to_string();
                        
                    let data = response.bytes().await?;
                    
                    Ok(Content {
                        id: id.to_string(),
                        data: data.to_vec(),
                        content_type,
                        range: range.map(|r| r.to_string()),
                        created_at: Utc::now(),
                    })
                }
                Err(e) => {
                    Err(CdnError::PeerFetchFailed(e.to_string()))
                }
            }
    }
    
    pub async fn add_peer(&self, node_id: NodeId, address: String) -> Result<(), CdnError> {
        let mut peers = self.peers.write().unwrap();
        
        peers.insert(node_id.clone(), PeerInfo {
            node_id,
            address,
            last_seen: Utc::now(),
            status: PeerStatus::Active,
        });
        
        Ok(())
    }
    
    pub async fn remove_peer(&self, node_id: &NodeId) -> Result<(), CdnError> {
        let mut peers = self.peers.write().unwrap();
        
        if peers.remove(node_id).is_some() {
            log::info!("Removed peer {}", node_id);
        }
        
        Ok(())
    }
    
    pub async fn update_routing(&self, update: RoutingUpdate) -> Result<(), CdnError> {
        let mut table = self.routing_table.write().unwrap();
        
        table.insert(update.content_id, ContentRoutingEntry {
            node_id: update.node_id,
            last_updated: update.timestamp,
            ttl: update.ttl,
        });
        
        Ok(())
    }
}

/// 内容商店接口
#[async_trait]
pub trait ContentStore: Send + Sync {
    async fn store_content(&self, data: &[u8]) -> Result<String, CdnError>;
    async fn get_content(&self, id: &str, range: Option<&str>) -> Result<Option<Content>, CdnError>;
    async fn delete_content(&self, id: &str) -> Result<(), CdnError>;
    async fn fetch_from_origin(&self, id: &str, range: Option<&str>) -> Result<Content, CdnError>;
}

/// 文件系统内容存储
pub struct FileSystemContentStore {
    base_path: PathBuf,
    origin_client: Client,
    origin_base_url: String,
}

impl FileSystemContentStore {
    pub fn new(base_path: &str, origin_base_url: &str) -> Self {
        Self {
            base_path: PathBuf::from(base_path),
            origin_client: Client::new(),
            origin_base_url: origin_base_url.to_string(),
        }
    }
    
    fn get_path_for_id(&self, id: &str) -> PathBuf {
        // 使用分层目录结构来避免单个目录中有太多文件
        let prefix = &id[0..2];
        let subdir = &id[2..4];
        self.base_path.join(prefix).join(subdir).join(id)
    }
    
    fn ensure_dir_exists(&self, id: &str) -> Result<(), CdnError> {
        let path = self.get_path_for_id(id);
        let parent = path.parent().ok_or(CdnError::InvalidPath)?;
        
        fs::create_dir_all(parent)?;
        Ok(())
    }
}

#[async_trait]
impl ContentStore for FileSystemContentStore {
    async fn store_content(&self, data: &[u8]) -> Result<String, CdnError> {
        // 生成内容ID (使用SHA-256哈希)
        let mut hasher = Sha256::new();
        hasher.update(data);
        let id = hex::encode(hasher.finalize());
        
        // 确保目录存在
        self.ensure_dir_exists(&id)?;
        
        // 写入文件
        let path = self.get_path_for_id(&id);
        tokio::fs::write(&path, data).await?;
        
        Ok(id)
    }
    
    async fn get_content(&self, id: &str, range: Option<&str>) -> Result<Option<Content>, CdnError> {
        let path = self.get_path_for_id(id);
        
        // 检查文件是否存在
        if !path.exists() {
            return Ok(None);
        }
        
        // 处理范围请求
        if let Some(range_str) = range {
            if let Ok((start, end)) = parse_range(range_str) {
                let metadata = tokio::fs::metadata(&path).await?;
                let file_size = metadata.len();
                
                // 验证范围
                let end = std::cmp::min(end.unwrap_or(file_size), file_size);
                let start = std::cmp::min(start, end);
                
                if start >= end {
                    return Err(CdnError::InvalidRange);
                }
                
                // 读取指定范围
                let mut file = tokio::fs::File::open(&path).await?;
                file.seek(SeekFrom::Start(start)).await?;
                
                let mut buffer = vec![0; (end - start) as usize];
                file.read_exact(&mut buffer).await?;
                
                // 推断内容类型
                let content_type = mime_guess::from_path(&path)
                    .first_or_octet_stream()
                    .to_string();
                
                return Ok(Some(Content {
                    id: id.to_string(),
                    data: buffer,
                    content_type,
                    range: Some(format!("bytes={}-{}", start, end - 1)),
                    created_at: Utc::now(),
                }));
            } else {
                return Err(CdnError::InvalidRange);
            }
        }
        
        // 读取整个文件
        let data = tokio::fs::read(&path).await?;
        
        // 推断内容类型
        let content_type = mime_guess::from_path(&path)
            .first_or_octet_stream()
            .to_string();
        
        Ok(Some(Content {
            id: id.to_string(),
            data,
            content_type,
            range: None,
            created_at: Utc::now(),
        }))
    }
    
    async fn delete_content(&self, id: &str) -> Result<(), CdnError> {
        let path = self.get_path_for_id(id);
        
        if path.exists() {
            tokio::fs::remove_file(path).await?;
        }
        
        Ok(())
    }
    
    async fn fetch_from_origin(&self, id: &str, range: Option<&str>) -> Result<Content, CdnError> {
        // 构建原始URL
        let mut url = format!("{}/{}", self.origin_base_url, id);
        
        // 创建请求
        let mut request_builder = self.origin_client.get(&url);
        
        // 添加范围头（如果有）
        if let Some(r) = range {
            request_builder = request_builder.header(header::RANGE, r);
        }
        
        // 发送请求
        let response = request_builder
            .timeout(Duration::from_secs(30))
            .send()
            .await?;
            
        if !response.status().is_success() {
            return Err(CdnError::OriginFetchFailed(response.status().to_string()));
        }
        
        // 获取内容类型
        let content_type = response.headers()
            .get(header::CONTENT_TYPE)
            .and_then(|v| v.to_str().ok())
            .unwrap_or("application/octet-stream")
            .to_string();
            
        // 获取返回的范围（如果有）
        let content_range = response.headers()
            .get(header::CONTENT_RANGE)
            .and_then(|v| v.to_str().ok())
            .map(|s| s.to_string());
            
        // 读取响应体
        let data = response.bytes().await?;
        
        // 创建内容对象
        let content = Content {
            id: id.to_string(),
            data: data.to_vec(),
            content_type,
            range: content_range.or_else(|| range.map(|r| r.to_string())),
            created_at: Utc::now(),
        };
        
        // 存储到本地
        if range.is_none() {
            // 只有完整内容才存储到磁盘
            self.ensure_dir_exists(id)?;
            let path = self.get_path_for_id(id);
            tokio::fs::write(path, &content.data).await?;
        }
        
        Ok(content)
    }
}

// 辅助函数：解析范围字符串
fn parse_range(range: &str) -> Result<(u64, Option<u64>), CdnError> {
    // 解析形如 "bytes=0-100" 的范围字符串
    let parts: Vec<&str> = range.split('=').collect();
    if parts.len() != 2 || parts[0] != "bytes" {
        return Err(CdnError::InvalidRange);
    }
    
    let range_values: Vec<&str> = parts[1].split('-').collect();
    if range_values.len() != 2 {
        return Err(CdnError::InvalidRange);
    }
    
    let start = range_values[0].parse::<u64>().map_err(|_| CdnError::InvalidRange)?;
    let end = if range_values[1].is_empty() {
        None
    } else {
        Some(range_values[1].parse::<u64>().map_err(|_| CdnError::InvalidRange)? + 1)
    };
    
    Ok((start, end))
}
```

## 14. 开发者工具与调试支持

### 14.1 分布式追踪工具

```rust
/// 分布式追踪管理器
pub struct TracingManager {
    service_name: String,
    tracer: Arc<dyn Tracer>,
    trace_config: TraceConfig,
}

impl TracingManager {
    pub fn new(service_name: String, trace_config: TraceConfig) -> Result<Self, TracingError> {
        // 配置导出器
        let exporter = match trace_config.exporter_type {
            TracingExporter::Jaeger => {
                JaegerExporter::new(&trace_config.jaeger_endpoint)?
            }
            TracingExporter::Zipkin => {
                ZipkinExporter::new(&trace_config.zipkin_endpoint)?
            }
            TracingExporter::Otlp => {
                OtlpExporter::new(&trace_config.otlp_endpoint)?
            }
            TracingExporter::Console => {
                ConsoleExporter::new()
            }
        };
        
        // 配置采样器
        let sampler = match trace_config.sampler_type {
            SamplerType::AlwaysOn => AlwaysOnSampler::new(),
            SamplerType::AlwaysOff => AlwaysOffSampler::new(),
            SamplerType::Probability { rate } => ProbabilitySampler::new(rate),
            SamplerType::RateLimiting { limit } => RateLimitingSampler::new(limit),
        };
        
        // 创建追踪提供者
        let mut provider_builder = TracerProvider::builder()
            .with_exporter(exporter)
            .with_sampler(sampler);
            
        // 添加资源属性
        let resource = Resource::new(vec![
            KeyValue::new("service.name", service_name.clone()),
            KeyValue::new("service.version", env!("CARGO_PKG_VERSION").to_string()),
            KeyValue::new("deployment.environment", trace_config.environment.clone()),
        ]);
        
        provider_builder = provider_builder.with_resource(resource);
        
        // 构建追踪提供者
        let provider = provider_builder.build();
        
        // 获取追踪器
        let tracer = provider.tracer("global");
        
        Ok(Self {
            service_name,
            tracer: Arc::new(tracer),
            trace_config,
        })
    }
    
    pub fn start_span(&self, name: &str, parent_context: Option<&SpanContext>) -> Result<Span, TracingError> {
        let mut builder = self.tracer.span_builder(name);
        
        if let Some(parent) = parent_context {
            builder = builder.with_parent(parent.clone());
        }
        
        let span = builder.start();
        
        Ok(span)
    }
    
    pub fn extract_context<T: ExtractCarrier>(&self, carrier: &T) -> Option<SpanContext> {
        self.tracer.extract(carrier)
    }
    
    pub fn inject_context<T: InjectCarrier>(&self, context: &SpanContext, carrier: &mut T) {
        self.tracer.inject(context, carrier);
    }
    
    pub fn register_hook<F>(&self, hook: F) -> Result<(), TracingError>
    where
        F: Fn(&mut Span, &str, Option<&SpanContext>) + Send + Sync + 'static,
    {
        self.tracer.register_hook(hook);
        Ok(())
    }
    
    pub fn shutdown(&self) -> Result<(), TracingError> {
        self.tracer.shutdown();
        Ok(())
    }
}

/// HTTP请求跟踪中间件
pub struct TracingMiddleware {
    tracer: Arc<dyn Tracer>,
}

impl TracingMiddleware {
    pub fn new(tracer: Arc<dyn Tracer>) -> Self {
        Self { tracer }
    }
}

impl<S, B> Layer<S> for TracingMiddleware
where
    S: Service<Request<B>, Response = Response> + Send + 'static,
    S::Future: Send + 'static,
    B: Send + 'static,
{
    type Service = TracingService<S>;
    
    fn layer(&self, service: S) -> Self::Service {
        TracingService {
            service,
            tracer: self.tracer.clone(),
        }
    }
}

pub struct TracingService<S> {
    service: S,
    tracer: Arc<dyn Tracer>,
}

impl<S, B> Service<Request<B>> for TracingService<S>
where
    S: Service<Request<B>, Response = Response> + Send + 'static,
    S::Future: Send + 'static,
    B: Send + 'static,
{
    type Response = S::Response;
    type Error = S::Error;
    type Future = BoxFuture<'static, Result<Self::Response, Self::Error>>;
    
    fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        self.service.poll_ready(cx)
    }
    
    fn call(&mut self, mut req: Request<B>) -> Self::Future {
        // 提取追踪上下文
        let parent_context = self.tracer.extract(&req);
        
        // 创建新跨度
        let span_name = format!("{} {}", req.method(), req.uri().path());
        let mut span = self.tracer.span_builder(&span_name)
            .with_kind(SpanKind::Server)
            .with_parent(parent_context.clone().unwrap_or_default())
            .start();
            
        // 添加标准属性
        span.set_attribute("http.method", req.method().to_string());
        span.set_attribute("http.url", req.uri().to_string());
        span.set_attribute("http.target", req.uri().path().to_string());
        
        if let Some(query) = req.uri().query() {
            span.set_attribute("http.query", query.to_string());
        }
        
        if let Some(user_agent) = req.headers().get("user-agent").and_then(|h| h.to_str().ok()) {
            span.set_attribute("http.user_agent", user_agent.to_string());
        }
        
        // 注入上下文回请求中，以便后续处理程序使用
        let span_context = span.context().clone();
        req.extensions_mut().insert(span_context.clone());
        
        let cloned_tracer = self.tracer.clone();
        let future = self.service.call(req);
        
        Box::pin(async move {
            // 执行请求
            let result = future.await;
            
            // 记录响应
            match &result {
                Ok(resp) => {
                    let status = resp.status().as_u16();
                    span.set_attribute("http.status_code", status as i64);
                    
                    if status >= 400 {
                        span.set_status(SpanStatus::Error);
                    } else {
                        span.set_status(SpanStatus::Ok);
                    }
                    
                    if let Some(content_length) = resp.headers().get("content-length").and_then(|h| h.to_str().ok()).and_then(|s| s.parse::<i64>().ok()) {
                        span.set_attribute("http.response_content_length", content_length);
                    }
                }
                Err(_) => {
                    span.set_status(SpanStatus::Error);
                }
            }
            
            // 结束跨度
            drop(span);
            
            result
        })
    }
}
```

### 14.2 分布式日志聚合

```rust
/// 日志聚合管理器
pub struct LogAggregator {
    node_id: NodeId,
    config: LogConfig,
    writer: Arc<dyn LogWriter>,
    shared_context: RwLock<HashMap<String, String>>,
}

impl LogAggregator {
    pub fn new(node_id: NodeId, config: LogConfig) -> Result<Self, LogError> {
        let writer: Arc<dyn LogWriter> = match config.writer_type {
            LogWriterType::Console => Arc::new(ConsoleLogWriter::new()),
            LogWriterType::File => Arc::new(FileLogWriter::new(&config.file_path)?),
            LogWriterType::Loki => Arc::new(LokiLogWriter::new(&config.loki_endpoint)?),
            LogWriterType::Kafka => Arc::new(KafkaLogWriter::new(&config.kafka_config)?),
        };
        
        Ok(Self {
            node_id,
            config,
            writer,
            shared_context: RwLock::new(HashMap::new()),
        })
    }
    
    pub fn init(&self) -> Result<(), LogError> {
        // 设置全局日志记录器
        let node_id = self.node_id.clone();
        let writer = self.writer.clone();
        let shared_context = self.shared_context.clone();
        let sampling_rate = self.config.sampling_rate;
        
        let subscriber = tracing_subscriber::registry()
            .with(tracing_subscriber::EnvFilter::from_default_env())
            .with(JsonLayer::new()
                .with_writer(move |json| {
                    // 添加通用字段
                    let mut log_entry = serde_json::from_str::<serde_json::Value>(&json)
                        .unwrap_or_else(|_| serde_json::Value::Object(serde_json::Map::new()));
                        
                    if let serde_json::Value::Object(ref mut map) = log_entry {
                        // 添加节点ID
                        map.insert("node_id".to_string(), serde_json::Value::String(node_id.clone()));
                        
                        // 添加时间戳（如果不存在）
                        if !map.contains_key("timestamp") {
                            let now = Utc::now().to_rfc3339();
                            map.insert("timestamp".to_string(), serde_json::Value::String(now));
                        }
                        
                        // 添加共享上下文
                        let context = shared_context.read().unwrap();
                        for (key, value) in context.iter() {
                            map.insert(key.clone(), serde_json::Value::String(value.clone()));
                        }
                    }
                    
                    // 应用采样策略
                    let level = if let serde_json::Value::Object(ref map) = log_entry {
                        map.get("level")
                            .and_then(|v| v.as_str())
                            .unwrap_or("INFO")
                    } else {
                        "INFO"
                    };
                    
                    // 根据日志级别和采样率决定是否记录
                    let should_log = match level {
                        "ERROR" | "WARN" => true, // 始终记录错误和警告
                        _ => {
                            if sampling_rate >= 1.0 {
                                true
                            } else {
                                rand::random::<f64>() < sampling_rate
                            }
                        }
                    };
                    
                    if should_log {
                        // 将日志发送到写入器
                        let serialized = serde_json::to_string(&log_entry).unwrap_or_else(|_| json.to_string());
                        if let Err(e) = writer.write(&serialized) {
                            eprintln!("Failed to write log: {}", e);
                        }
                    }
                })
            );
            
        // 注册订阅者
        tracing::subscriber::set_global_default(subscriber)
            .map_err(|e| LogError::InitializationError(e.to_string()))?;
            
        Ok(())
    }
    
    pub fn add_context(&self, key: &str, value: &str) {
        let mut context = self.shared_context.write().unwrap();
        context.insert(key.to_string(), value.to_string());
    }
    
    pub fn remove_context(&self, key: &str) {
        let mut context = self.shared_context.write().unwrap();
        context.remove(key);
    }
    
    pub fn with_context<F, R>(&self, context_entries: HashMap<String, String>, f: F) -> R
    where
        F: FnOnce() -> R,
    {
        // 保存旧上下文
        let old_entries: HashMap<String, String> = {
            let current = self.shared_context.read().unwrap();
            context_entries.keys()
                .filter_map(|k| current.get(k).map(|v| (k.clone(), v.clone())))
                .collect()
        };
        
        // 添加新上下文
        {
            let mut current = self.shared_context.write().unwrap();
            for (k, v) in &context_entries {
                current.insert(k.clone(), v.clone());
            }
        }
        
        // 执行函数
        let result = f();
        
        // 恢复旧上下文
        {
            let mut current = self.shared_context.write().unwrap();
            for (k, _) in &context_entries {
                current.remove(k);
            }
            for (k, v) in old_entries {
                current.insert(k, v);
            }
        }
        
        result
    }
}

/// 日志写入器接口
#[async_trait]
pub trait LogWriter: Send + Sync {
    fn write(&self, log_entry: &str) -> Result<(), LogError>;
    async fn flush(&self) -> Result<(), LogError>;
}

/// 控制台日志写入器
pub struct ConsoleLogWriter;

impl ConsoleLogWriter {
    pub fn new() -> Self {
        Self
    }
}

impl LogWriter for ConsoleLogWriter {
    fn write(&self, log_entry: &str) -> Result<(), LogError> {
        println!("{}", log_entry);
        Ok(())
    }
    
    async fn flush(&self) -> Result<(), LogError> {
        // 控制台不需要刷新
        Ok(())
    }
}

/// 文件日志写入器
pub struct FileLogWriter {
    file: Mutex<BufWriter<File>>,
    path: PathBuf,
}

impl FileLogWriter {
    pub fn new(path: &str) -> Result<Self, LogError> {
        let path = PathBuf::from(path);
        
        // 确保目录存在
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).map_err(|e| LogError::IoError(e.to_string()))?;
        }
        
        // 打开文件
        let file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&path)
            .map_err(|e| LogError::IoError(e.to_string()))?;
            
        let writer = BufWriter::new(file);
        
        Ok(Self {
            file: Mutex::new(writer),
            path,
        })
    }
}

impl LogWriter for FileLogWriter {
    fn write(&self, log_entry: &str) -> Result<(), LogError> {
        let mut file = self.file.lock().unwrap();
        
        writeln!(file, "{}", log_entry)
            .map_err(|e| LogError::IoError(e.to_string()))?;
            
        Ok(())
    }
    
    async fn flush(&self) -> Result<(), LogError> {
        let mut file = self.file.lock().unwrap();
        
        file.flush()
            .map_err(|e| LogError::IoError(e.to_string()))?;
            
        Ok(())
    }
}

/// Loki日志写入器
pub struct LokiLogWriter {
    client: reqwest::Client,
    endpoint: String,
    buffer: Mutex<Vec<String>>,
    max_buffer_size: usize,
    last_flush: AtomicI64,
    flush_interval: Duration,
}

impl LokiLogWriter {
    pub fn new(endpoint: &str) -> Result<Self, LogError> {
        Ok(Self {
            client: reqwest::Client::new(),
            endpoint: endpoint.to_string(),
            buffer: Mutex::new(Vec::new()),
            max_buffer_size: 100,
            last_flush: AtomicI64::new(Utc::now().timestamp()),
            flush_interval: Duration::from_secs(10),
        })
    }
    
    fn should_flush(&self) -> bool {
        let buffer_len = self.buffer.lock().unwrap().len();
        
        if buffer_len >= self.max_buffer_size {
            return true;
        }
        
        let last_flush = self.last_flush.load(Ordering::Relaxed);
        let now = Utc::now().timestamp();
        
        (now - last_flush) as u64 >= self.flush_interval.as_secs()
    }
}

impl LogWriter for LokiLogWriter {
    fn write(&self, log_entry: &str) -> Result<(), LogError> {
        // 添加到缓冲区
        {
            let mut buffer = self.buffer.lock().unwrap();
            buffer.push(log_entry.to_string());
        }
        
        // 检查是否应该刷新
        if self.should_flush() {
            let this = self.clone();
            tokio::spawn(async move {
                if let Err(e) = this.flush().await {
                    eprintln!("Failed to flush logs to Loki: {}", e);
                }
            });
        }
        
        Ok(())
    }
    
    async fn flush(&self) -> Result<(), LogError> {
        // 获取并清空缓冲区
        let logs = {
            let mut buffer = self.buffer.lock().unwrap();
            if buffer.is_empty() {
                return Ok(());
            }
            
            std::mem::take(&mut *buffer)
        };
        
        if logs.is_empty() {
            return Ok(());
        }
        
        // 构建Loki请求
        let now_ns = Utc::now().timestamp_nanos() as u64;
        
        let streams = vec![serde_json::json!({
            "stream": {
                "job": "distributed-system"
            },
            "values": logs.iter().map(|log| {
                (now_ns.to_string(), log.clone())
            }).collect::<Vec<_>>()
        })];
        
        let payload = serde_json::json!({
            "streams": streams
        });
        
        // 发送到Loki
        let response = self.client.post(&self.endpoint)
            .json(&payload)
            .timeout(Duration::from_secs(5))
            .send()
            .await
            .map_err(|e| LogError::RemoteError(e.to_string()))?;
            
        if !response.status().is_success() {
            return Err(LogError::RemoteError(format!(
                "Loki returned error status: {}", response.status()
            )));
        }
        
        // 更新上次刷新时间
        self.last_flush.store(Utc::now().timestamp(), Ordering::Relaxed);
        
        Ok(())
    }
}

// 日志错误类型
#[derive(Debug, thiserror::Error)]
pub enum LogError {
    #[error("Log initialization error: {0}")]
    InitializationError(String),
    
    #[error("IO error: {0}")]
    IoError(String),
    
    #[error("Remote service error: {0}")]
    RemoteError(String),
    
    #[error("Serialization error: {0}")]
    SerializationError(String),
}
```

### 14.3 监控与可视化

```rust
/// 指标收集器
pub struct MetricsCollector {
    registry: prometheus::Registry,
    http_endpoint: Option<String>,
    pushgateway_endpoint: Option<String>,
    push_interval: Option<Duration>,
    metrics: HashMap<String, Box<dyn Metric>>,
}

impl MetricsCollector {
    pub fn new(config: MetricsConfig) -> Result<Self, MetricsError> {
        let registry = prometheus::Registry::new();
        
        // 注册默认指标
        let process_collector = ProcessCollector::for_self();
        registry.register(Box::new(process_collector))
            .map_err(|e| MetricsError::RegistrationError(e.to_string()))?;
            
        Ok(Self {
            registry,
            http_endpoint: config.http_endpoint,
            pushgateway_endpoint: config.pushgateway_endpoint,
            push_interval: config.push_interval,
            metrics: HashMap::new(),
        })
    }
    
    pub fn start(&self) -> Result<(), MetricsError> {
        // 如果配置了HTTP端点，启动Prometheus导出器
        if let Some(ref endpoint) = self.http_endpoint {
            self.start_http_exporter(endpoint)?;
        }
        
        // 如果配置了Pushgateway，启动推送任务
        if let Some(ref endpoint) = self.pushgateway_endpoint {
            if let Some(interval) = self.push_interval {
                self.start_pushgateway_task(endpoint, interval)?;
            }
        }
        
        Ok(())
    }
    
    fn start_http_exporter(&self, endpoint: &str) -> Result<(), MetricsError> {
        let addr = endpoint.parse()
            .map_err(|e| MetricsError::ConfigurationError(format!("Invalid HTTP endpoint: {}", e)))?;
            
        let registry = self.registry.clone();
        
        tokio::spawn(async move {
            // 创建指标处理程序
            let metrics_handler = warp::path!("metrics")
                .map(move || {
                    let encoder = TextEncoder::new();
                    let metric_families = registry.gather();
                    let mut buffer = Vec::new();
                    
                    encoder.encode(&metric_families, &mut buffer)
                        .unwrap_or_else(|e| {
                            eprintln!("Error encoding metrics: {}", e);
                        });
                        
                    String::from_utf8(buffer).unwrap_or_else(|e| {
                        eprintln!("Error converting metrics to UTF-8: {}", e);
                        String::new()
                    })
                });
                
            // 启动HTTP服务器
            warp::serve(metrics_handler)
                .run(addr)
                .await;
        });
        
        Ok(())
    }
    
    fn start_pushgateway_task(&self, endpoint: &str, interval: Duration) -> Result<(), MetricsError> {
        let registry = self.registry.clone();
        let endpoint = endpoint.to_string();
        
        tokio::spawn(async move {
            let mut push_interval = tokio::time::interval(interval);
            
            loop {
                push_interval.tick().await;
                
                // 推送指标到Pushgateway
                if let Err(e) = push_metrics(&registry, &endpoint).await {
                    eprintln!("Failed to push metrics: {}", e);
                }
            }
        });
        
        Ok(())
    }
    
    pub fn register_counter(&mut self, name: &str, help: &str, label_names: &[&str]) -> Result<CounterHandle, MetricsError> {
        let counter = prometheus::Counter::with_opts(
            prometheus::Opts::new(name, help)
        )?;
        
        self.registry.register(Box::new(counter.clone()))?;
        
        let handle = CounterHandle { counter };
        self.metrics.insert(name.to_string(), Box::new(handle.clone()));
        
        Ok(handle)
    }
    
    pub fn register_counter_vec(&mut self, name: &str, help: &str, label_names: &[&str]) -> Result<CounterVecHandle, MetricsError> {
        let counter_vec = prometheus::CounterVec::new(
            prometheus::Opts::new(name, help),
            label_names,
        )?;
        
        self.registry.register(Box::new(counter_vec.clone()))?;
        
        let handle = CounterVecHandle { counter_vec };
        self.metrics.insert(name.to_string(), Box::new(handle.clone()));
        
        Ok(handle)
    }
    
    pub fn register_gauge(&mut self, name: &str, help: &str) -> Result<GaugeHandle, MetricsError> {
        let gauge = prometheus::Gauge::with_opts(
            prometheus::Opts::new(name, help)
        )?;
        
        self.registry.register(Box::new(gauge.clone()))?;
        
        let handle = GaugeHandle { gauge };
        self.metrics.insert(name.to_string(), Box::new(handle.clone()));
        
        Ok(handle)
    }
    
    pub fn register_gauge_vec(&mut self, name: &str, help: &str, label_names: &[&str]) -> Result<GaugeVecHandle, MetricsError> {
        let gauge_vec = prometheus::GaugeVec::new(
            prometheus::Opts::new(name, help),
            label_names,
        )?;
        
        self.registry.register(Box::new(gauge_vec.clone()))?;
        
        let handle = GaugeVecHandle { gauge_vec };
        self.metrics.insert(name.to_string(), Box::new(handle.clone()));
        
        Ok(handle)
    }
    
    pub fn register_histogram(&mut self, name: &str, help: &str, buckets: Vec<f64>) -> Result<HistogramHandle, MetricsError> {
        let histogram = prometheus::Histogram::with_opts(
            prometheus::HistogramOpts::new(name, help)
                .buckets(buckets)
        )?;
        
        self.registry.register(Box::new(histogram.clone()))?;
        
        let handle = HistogramHandle { histogram };
        self.metrics.insert(name.to_string(), Box::new(handle.clone()));
        
        Ok(handle)
    }
    
    pub fn register_histogram_vec(&mut self, name: &str, help: &str, label_names: &[&str], buckets: Vec<f64>) -> Result<HistogramVecHandle, MetricsError> {
        let histogram_vec = prometheus::HistogramVec::new(
            prometheus::HistogramOpts::new(name, help)
                .buckets(buckets),
            label_names,
        )?;
        
        self.registry.register(Box::new(histogram_vec.clone()))?;
        
        let handle = HistogramVecHandle { histogram_vec };
        self.metrics.insert(name.to_string(), Box::new(handle.clone()));
        
        Ok(handle)
    }
    
    pub fn register_summary(&mut self, name: &str, help: &str, quantiles: Vec<(f64, f64)>) -> Result<SummaryHandle, MetricsError> {
        let mut opts = prometheus::SummaryOpts::new(name, help);
        
        if !quantiles.is_empty() {
            opts = opts.quantiles(&quantiles);
        }
        
        let summary = prometheus::Summary::with_opts(opts)?;
        
        self.registry.register(Box::new(summary.clone()))?;
        
        let handle = SummaryHandle { summary };
        self.metrics.insert(name.to_string(), Box::new(handle.clone()));
        
        Ok(handle)
    }
}

/// 推送指标到Pushgateway
async fn push_metrics(registry: &prometheus::Registry, endpoint: &str) -> Result<(), MetricsError> {
    let encoder = TextEncoder::new();
    let metric_families = registry.gather();
    let mut buffer = Vec::new();
    
    encoder.encode(&metric_families, &mut buffer)?;
    
    let client = reqwest::Client::new();
    let response = client.post(endpoint)
        .header(header::CONTENT_TYPE, "text/plain")
        .body(buffer)
        .send()
        .await
        .map_err(|e| MetricsError::PushError(e.to_string()))?;
        
    if !response.status().is_success() {
        return Err(MetricsError::PushError(format!(
            "Pushgateway returned error status: {}", response.status()
        )));
    }
    
    Ok(())
}

// 指标特征
pub trait Metric: Send + Sync {
    fn name(&self) -> &str;
    fn metric_type(&self) -> &str;
}

// 计数器句柄
#[derive(Clone)]
pub struct CounterHandle {
    counter: prometheus::Counter,
}

impl CounterHandle {
    pub fn inc(&self) {
        self.counter.inc();
    }
    
    pub fn inc_by(&self, v: f64) {
        self.counter.inc_by(v);
    }
}

impl Metric for CounterHandle {
    fn name(&self) -> &str {
        self.counter.desc().0[0].fq_name.as_str()
    }
    
    fn metric_type(&self) -> &str {
        "counter"
    }
}

// 计数器向量句柄
#[derive(Clone)]
pub struct CounterVecHandle {
    counter_vec: prometheus::CounterVec,
}

impl CounterVecHandle {
    pub fn with_label_values(&self, label_values: &[&str]) -> prometheus::Counter {
        self.counter_vec.with_label_values(label_values)
    }
    
    pub fn with(&self, labels: &[(&str, &str)]) -> prometheus::Counter {
        self.counter_vec.with(&labels.iter().map(|(k, v)| (k.to_string(), v.to_string())).collect::<HashMap<_, _>>())
    }
}

impl Metric for CounterVecHandle {
    fn name(&self) -> &str {
        self.counter_vec.desc().0[0].fq_name.as_str()
    }
    
    fn metric_type(&self) -> &str {
        "counter_vec"
    }
}

// 其他指标句柄类型的实现...

// 指标错误类型
#[derive(Debug, thiserror::Error)]
pub enum MetricsError {
    #[error("Metrics registration error: {0}")]
    RegistrationError(String),
    
    #[error("Metrics configuration error: {0}")]
    ConfigurationError(String),
    
    #[error("Metrics push error: {0}")]
    PushError(String),
    
    #[error("Other metrics error: {0}")]
    Other(String),
}

impl From<prometheus::Error> for MetricsError {
    fn from(err: prometheus::Error) -> Self {
        MetricsError::Other(err.to_string())
    }
}
```

## 15. 应用示例: 分布式任务调度系统

```rust
/// 分布式任务调度系统
pub struct TaskScheduler {
    node_id: NodeId,
    state_manager: Arc<DistributedStateManager>,
    task_executor: Arc<TaskExecutor>,
    scheduler: Arc<SchedulerCore>,
    api_server: Option<ApiServer>,
    consensus: Arc<dyn ConsensusProtocol>,
}

impl TaskScheduler {
    pub fn new(
        node_id: NodeId,
        config: SchedulerConfig,
        state_manager: Arc<DistributedStateManager>,
        consensus: Arc<dyn ConsensusProtocol>,
    ) -> Result<Self, SchedulerError> {
        // 创建任务执行器
        let task_executor = Arc::new(TaskExecutor::new(
            node_id.clone(),
            config.max_concurrent_tasks,
        ));
        
        // 创建调度器核心
        let scheduler = Arc::new(SchedulerCore::new(
            node_id.clone(),
            config.clone(),
            state_manager.clone(),
            task_executor.clone(),
        ));
        
        // 创建API服务器（如果配置了）
        let api_server = if let Some(api_config) = config.api {
            Some(ApiServer::new(
                api_config,
                scheduler.clone(),
            )?)
        } else {
            None
        };
        
        Ok(Self {
            node_id,
            state_manager,
            task_executor,
            scheduler,
            api_server,
            consensus,
        })
    }
    
    pub async fn start(&self) -> Result<(), SchedulerError> {
        // 注册任务处理程序
        self.register_task_handlers().await?;
        
        // 启动调度器核心
        self.scheduler.start().await?;
        
        // 启动API服务器（如果有）
        if let Some(api_server) = &self.api_server {
            api_server.start().await?;
        }
        
        // 如果是领导者节点，启动领导者任务
        if self.is_leader().await? {
            self.start_leader_tasks().await?;
        }
        
        // 监听领导者变更
        self.monitor_leadership_changes().await?;
        
        log::info!("Task scheduler started on node {}", self.node_id);
        
        Ok(())
    }
    
    async fn register_task_handlers(&self) -> Result<(), SchedulerError> {
        // 注册内置任务处理程序
        self.task_executor.register_handler("http_request", Box::new(HttpRequestTaskHandler::new())).await?;
        self.task_executor.register_handler("shell_command", Box::new(ShellCommandTaskHandler::new())).await?;
        self.task_executor.register_handler("data_processing", Box::new(DataProcessingTaskHandler::new())).await?;
        
        Ok(())
    }
    
    async fn is_leader(&self) -> Result<bool, SchedulerError> {
        let leader = self.consensus.get_leader().await
            .map_err(|e| SchedulerError::ConsensusError(e.to_string()))?;
            
        Ok(leader == self.node_id)
    }
    
    async fn start_leader_tasks(&self) -> Result<(), SchedulerError> {
        log::info!("Starting leader tasks on node {}", self.node_id);
        
        // 启动调度循环
        self.scheduler.start_scheduling_loop().await?;
        
        // 启动维护任务
        self.scheduler.start_maintenance_tasks().await?;
        
        Ok(())
    }
    
    async fn stop_leader_tasks(&self) -> Result<(), SchedulerError> {
        log::info!("Stopping leader tasks on node {}", self.node_id);
        
        // 停止调度循环
        self.scheduler.stop_scheduling_loop().await?;
        
        // 停止维护任务
        self.scheduler.stop_maintenance_tasks().await?;
        
        Ok(())
    }
    
    async fn monitor_leadership_changes(&self) -> Result<(), SchedulerError> {
        let consensus = self.consensus.clone();
        let node_id = self.node_id.clone();
        let scheduler = self.scheduler.clone();
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_secs(1));
            let mut is_leader = false;
            
            loop {
                interval.tick().await;
                
                let leader_result = consensus.get_leader().await;
                
                match leader_result {
                    Ok(leader) => {
                        let now_leader = leader == node_id;
                        
                        if now_leader != is_leader {
                            if now_leader {
                                // 成为领导者
                                log::info!("Node {} became the leader", node_id);
                                if let Err(e) = scheduler.start_leader_tasks().await {
                                    log::error!("Failed to start leader tasks: {}", e);
                                }
                            } else {
                                // 不再是领导者
                                log::info!("Node {} is no longer the leader", node_id);
                                if let Err(e) = scheduler.stop_leader_tasks().await {
                                    log::error!("Failed to stop leader tasks: {}", e);
                                }
                            }
                            
                            is_leader = now_leader;
                        }
                    }
                    Err(e) => {
                        log::error!("Failed to get leader: {}", e);
                    }
                }
            }
        });
        
        Ok(())
    }
    
    pub async fn submit_task(&self, task: Task) -> Result<TaskId, SchedulerError> {
        self.scheduler.submit_task(task).await
    }
    
    pub async fn get_task_status(&self, task_id: &TaskId) -> Result<TaskStatus, SchedulerError> {
        self.scheduler.get_task_status(task_id).await
    }
    
    pub async fn cancel_task(&self, task_id: &TaskId) -> Result<(), SchedulerError> {
        self.scheduler.cancel_task(task_id).await
    }
}

/// 调度器核心
pub struct SchedulerCore {
    node_id: NodeId,
    config: SchedulerConfig,
    state_manager: Arc<DistributedStateManager>,
    task_executor: Arc<TaskExecutor>,
    scheduling_loop_handle: Mutex<Option<JoinHandle<()>>>,
    maintenance_handle: Mutex<Option<JoinHandle<()>>>,
}

impl SchedulerCore {
    pub fn new(
        node_id: NodeId,
        config: SchedulerConfig,
        state_manager: Arc<DistributedStateManager>,
        task_executor: Arc<TaskExecutor>,
    ) -> Self {
        Self {
            node_id,
            config,
            state_manager,
            task_executor,
            scheduling_loop_handle: Mutex::new(None),
            maintenance_handle: Mutex::new(None),
        }
    }
    
    pub async fn start(&self) -> Result<(), SchedulerError> {
        // 初始化状态
        self.initialize_state().await?;
        
        Ok(())
    }
    
    async fn initialize_state(&self) -> Result<(), SchedulerError> {
        // 确保任务相关的状态路径存在
        let tasks_exist = self.state_manager.exists("tasks").await
            .map_err(|e| SchedulerError::StateError(e.to_string()))?;
            
        if !tasks_exist {
            self.state_manager.create_directory("tasks").await
                .map_err(|e| SchedulerError::StateError(e.to_string()))?;
        }
        
        let schedules_exist = self.state_manager.exists("schedules").await
            .map_err(|e| SchedulerError::StateError(e.to_string()))?;
            
        if !schedules_exist {
            self.state_manager.create_directory("schedules").await
                .map_err(|e| SchedulerError::StateError(e.to_string()))?;
        }
        
        Ok(())
    }
    
    pub async fn start_scheduling_loop(&self) -> Result<(), SchedulerError> {
        let mut handle_guard = self.scheduling_loop_handle.lock().await;
        
        // 如果已经运行，则不做任何事
        if handle_guard.is_some() {
            return Ok(());
        }
        
        // 启动调度循环
        let state_manager = self.state_manager.clone();
        let task_executor = self.task_executor.clone();
        let node_id = self.node_id.clone();
        let schedule_interval = self.config.schedule_interval;
        
        let handle = tokio::spawn(async move {
            let mut interval = tokio::time::interval(schedule_interval);
            
            loop {
                interval.tick().await;
                
                // 查找可运行的调度
                match find_runnable_schedules(&state_manager).await {
                    Ok(schedules) => {
                        for schedule in schedules {
                            // 为每个调度创建任务
                            if let Err(e) = create_task_from_schedule(&state_manager, &task_executor, &schedule).await {
                                log::error!("Failed to create task from schedule {}: {}", schedule.id, e);
                            }
                        }
                    }
                    Err(e) => {
                        log::error!("Failed to find runnable schedules: {}", e);
                    }
                }
                
                // 查找可运行的任务
                match find_runnable_tasks(&state_manager).await {
                    Ok(tasks) => {
                        for task in tasks {
                            // 执行每个任务
                            if let Err(e) = execute_task(&state_manager, &task_executor, &task).await {
                                log::error!("Failed to execute task {}: {}", task.id, e);
                            }
                        }
                    }
                    Err(e) => {
                        log::error!("Failed to find runnable tasks: {}", e);
                    }
                }
            }
        });
        
        *handle_guard = Some(handle);
        
        Ok(())
    }
    
    pub async fn stop_scheduling_loop(&self) -> Result<(), SchedulerError> {
        let mut handle_guard = self.scheduling_loop_handle.lock().await;
        
        // 如果正在运行，则停止
        if let Some(handle) = handle_guard.take() {
            handle.abort();
        }
        
        Ok(())
    }
    
    pub async fn start_maintenance_tasks(&self) -> Result<(), SchedulerError> {
        let mut handle_guard = self.maintenance_handle.lock().await;
        
        // 如果已经运行，则不做任何事
        if handle_guard.is_some() {
            return Ok(());
        }
        
        // 启动维护任务
        let state_manager = self.state_manager.clone();
        let node_id = self.node_id.clone();
        let maintenance_interval = self.config.maintenance_interval;
        let task_history_ttl = self.config.task_history_ttl;
        
        let handle = tokio::spawn(async move {
            let mut interval = tokio::time::interval(maintenance_interval);
            
            loop {
                interval.tick().await;
                
                // 清理过期的任务历史
                if let Err(e) = cleanup_task_history(&state_manager, task_history_ttl).await {
                    log::error!("Failed to clean up task history: {}", e);
                }
                
                // 检查并恢复卡住的任务
                if let Err(e) = recover_stuck_tasks(&state_manager).await {
                    log::error!("Failed to recover stuck tasks: {}", e);
                }
                
                // 同步调度元数据
                if let Err(e) = sync_schedule_metadata(&state_manager).await {
                    log::error!("Failed to sync schedule metadata: {}", e);
                }
            }
        });
        
        *handle_guard = Some(handle);
        
        Ok(())
    }
    
    pub async fn stop_maintenance_tasks(&self) -> Result<(), SchedulerError> {
        let mut handle_guard = self.maintenance_handle.lock().await;
        
        // 如果正在运行，则停止
        if let Some(handle) = handle_guard.take() {
            handle.abort();
        }
        
        Ok(())
    }
    
    pub async fn submit_task(&self, task: Task) -> Result<TaskId, SchedulerError> {
        // 生成任务ID
        let task_id = Uuid::new_v4().to_string();
        
        // 准备任务记录
        let task_record = TaskRecord {
            id: task_id.clone(),
            task,
            status: TaskStatus::Pending,
            created_at: Utc::now(),
            updated_at: Utc::now(),
            scheduled_at: None,
            started_at: None,
            completed_at: None,
            result: None,
            error: None,
            retry_count: 0,
            node_id: None,
        };
        
        // 存储任务
        self.state_manager.put(&format!("tasks/{}", task_id), &task_record).await
            .map_err(|e| SchedulerError::StateError(e.to_string()))?;
            
        log::info!("Task {} submitted", task_id);
        
        Ok(task_id)
    }
    
    pub async fn get_task_status(&self, task_id: &TaskId) -> Result<TaskStatus, SchedulerError> {
        // 获取任务记录
        let task_record: Option<TaskRecord> = self.state_manager.get(&format!("tasks/{}", task_id)).await
            .map_err(|e| SchedulerError::StateError(e.to_string()))?;
            
        match task_record {
            Some(record) => Ok(record.status),
            None => Err(SchedulerError::TaskNotFound(task_id.clone())),
        }
    }
    
    pub async fn cancel_task(&self, task_id: &TaskId) -> Result<(), SchedulerError> {
        // 获取任务记录
        let mut task_record: Option<TaskRecord> = self.state_manager.get(&format!("tasks/{}", task_id)).await
            .map_err(|e| SchedulerError::StateError(e.to_string()))?;
            
        match task_record {
            Some(mut record) => {
                // 如果任务还没有完成，则取消它
                if record.status == TaskStatus::Pending || record.status == TaskStatus::Scheduled || record.status == TaskStatus::Running {
                    record.status = TaskStatus::Cancelled;
                    record.updated_at = Utc::now();
                    
                    // 更新任务记录
                    self.state_manager.put(&format!("tasks/{}", task_id), &record).await
                        .map_err(|e| SchedulerError::StateError(e.to_string()))?;
                        
                    log::info!("Task {} cancelled", task_id);
                    
                    // 如果任务正在运行，还需要尝试终止它
                    if record.status == TaskStatus::Running {
                        if let Some(node_id) = &record.node_id {
                            // 向执行节点发送取消命令
                            if node_id == &self.node_id {
                                // 如果是当前节点，直接取消
                                self.task_executor.cancel_task(task_id).await?;
                            } else {
                                // 如果是其他节点，发送取消请求
                                self.send_cancel_request(node_id, task_id).await?;
                            }
                        }
                    }
                    
                    Ok(())
                } else {
                    // 如果任务已经完成，则不能取消
                    Err(SchedulerError::TaskAlreadyCompleted(task_id.clone()))
                }
            }
            None => Err(SchedulerError::TaskNotFound(task_id.clone())),
        }
    }
    
    async fn send_cancel_request(&self, node_id: &NodeId, task_id: &TaskId) -> Result<(), SchedulerError> {
        // 构建取消命令
        let cancel_command = CancelCommand {
            task_id: task_id.clone(),
            timestamp: Utc::now(),
        };
        
        // 发送到目标节点
        // 在实际实现中，这可能通过节点间通信机制实现
        
        log::info!("Sent cancel request for task {} to node {}", task_id, node_id);
        
        Ok(())
    }
}

/// 查找可运行的调度任务
async fn find_runnable_schedules(state_manager: &DistributedStateManager) -> Result<Vec<Schedule>, SchedulerError> {
    // 获取所有调度
    let schedules: Vec<Schedule> = state_manager.list("schedules/")
        .await
        .map_err(|e| SchedulerError::StateError(e.to_string()))?
        .iter()
        .filter_map(|key| {
            // 从键中提取调度ID
            let schedule_id = key.trim_start_matches("schedules/");
            // 获取调度详情
            state_manager.get::<Schedule>(&format!("schedules/{}", schedule_id))
                .map_or(None, |result| result.ok().flatten())
        })
        .collect();
        
    // 过滤出可运行的调度
    let now = Utc::now();
    let runnable = schedules.into_iter()
        .filter(|schedule| {
            // 检查调度是否启用
            if !schedule.enabled {
                return false;
            }
            
            // 检查下一次运行时间是否已到
            if let Some(next_run) = schedule.next_run {
                if next_run <= now {
                    return true;
                }
            }
            
            false
        })
        .collect();
        
    Ok(runnable)
}

/// 从调度创建任务
async fn create_task_from_schedule(
    state_manager: &DistributedStateManager,
    task_executor: &TaskExecutor,
    schedule: &Schedule,
) -> Result<TaskId, SchedulerError> {
    // 构建任务
    let task = Task {
        name: format!("{} (scheduled)", schedule.name),
        task_type: schedule.task_type.clone(),
        parameters: schedule.parameters.clone(),
        priority: schedule.priority,
        timeout: schedule.timeout,
        retry_policy: schedule.retry_policy.clone(),
    };
    
    // 提交任务
    let task_id = Uuid::new_v4().to_string();
    
    // 准备任务记录
    let task_record = TaskRecord {
        id: task_id.clone(),
        task,
        status: TaskStatus::Pending,
        created_at: Utc::now(),
        updated_at: Utc::now(),
        scheduled_at: Some(Utc::now()),
        started_at: None,
        completed_at: None,
        result: None,
        error: None,
        retry_count: 0,
        node_id: None,
    };
    
    // 存储任务
    state_manager.put(&format!("tasks/{}", task_id), &task_record).await
        .map_err(|e| SchedulerError::StateError(e.to_string()))?;
        
    log::info!("Created task {} from schedule {}", task_id, schedule.id);
    
    // 更新调度的下一次运行时间
    let mut updated_schedule = schedule.clone();
    updated_schedule.last_run = Some(Utc::now());
    updated_schedule.next_run = calculate_next_run_time(&updated_schedule);
    
    // 保存更新后的调度
    state_manager.put(&format!("schedules/{}", schedule.id), &updated_schedule).await
        .map_err(|e| SchedulerError::StateError(e.to_string()))?;
        
    Ok(task_id)
}

/// 计算下一次运行时间
fn calculate_next_run_time(schedule: &Schedule) -> Option<DateTime<Utc>> {
    match &schedule.schedule_type {
        ScheduleType::Cron(expression) => {
            // 解析cron表达式
            if let Ok(schedule) = cron::Schedule::from_str(expression) {
                // 获取下一次运行时间
                schedule.upcoming(Utc).next()
            } else {
                // 如果表达式无效，则不安排下一次运行
                None
            }
        }
        ScheduleType::Interval(duration) => {
            // 从当前时间加上间隔
            Some(Utc::now() + *duration)
        }
        ScheduleType::OneTime(datetime) => {
            // 一次性调度不会再次运行
            None
        }
    }
}

/// 查找可运行的任务
async fn find_runnable_tasks(state_manager: &DistributedStateManager) -> Result<Vec<TaskRecord>, SchedulerError> {
    // 获取所有任务
    let tasks: Vec<TaskRecord> = state_manager.list("tasks/")
        .await
        .map_err(|e| SchedulerError::StateError(e.to_string()))?
        .iter()
        .filter_map(|key| {
            // 从键中提取任务ID
            let task_id = key.trim_start_matches("tasks/");
            // 获取任务详情
            state_manager.get::<TaskRecord>(&format!("tasks/{}", task_id))
                .map_or(None, |result| result.ok().flatten())
        })
        .collect();
        
    // 过滤出可运行的任务
    let runnable = tasks.into_iter()
        .filter(|task| {
            // 只选择待处理的任务
            task.status == TaskStatus::Pending
        })
        .collect();
        
    Ok(runnable)
}

/// 执行任务
async fn execute_task(
    state_manager: &DistributedStateManager,
    task_executor: &TaskExecutor,
    task_record: &TaskRecord,
) -> Result<(), SchedulerError> {
    // 更新任务状态为运行中
    let mut updated_record = task_record.clone();
    updated_record.status = TaskStatus::Running;
    updated_record.started_at = Some(Utc::now());
    updated_record.updated_at = Utc::now();
    updated_record.node_id = Some(task_executor.node_id.clone());
    
    // 保存更新后的任务记录
    state_manager.put(&format!("tasks/{}", task_record.id), &updated_record).await
        .map_err(|e| SchedulerError::StateError(e.to_string()))?;
        
    log::info!("Started executing task {} on node {}", task_record.id, task_executor.node_id);
    
    // 创建任务执行上下文
    let context = TaskContext {
        task_id: task_record.id.clone(),
        created_at: task_record.created_at,
        retry_count: task_record.retry_count,
    };
    
    // 异步执行任务
    let task = task_record.task.clone();
    let task_id = task_record.id.clone();
    let state_manager_clone = state_manager.clone();
    
    tokio::spawn(async move {
        // 执行任务
        let result = task_executor.execute_task(&task_id, &task, context).await;
        
        // 更新任务状态
        let mut final_record: TaskRecord = match state_manager_clone.get(&format!("tasks/{}", task_id)).await {
            Ok(Some(record)) => record,
            _ => return, // 任务记录已不存在，可能已被删除
        };
        
        match result {
            Ok(output) => {
                final_record.status = TaskStatus::Completed;
                final_record.completed_at = Some(Utc::now());
                final_record.updated_at = Utc::now();
                final_record.result = Some(output);
            }
            Err(e) => {
                // 检查是否需要重试
                if should_retry(&final_record, &e) {
                    final_record.status = TaskStatus::Pending;
                    final_record.retry_count += 1;
                    final_record.updated_at = Utc::now();
                    final_record.error = Some(format!("Attempt {}: {}", final_record.retry_count, e));
                    
                    log::info!(
                        "Task {} failed but will retry (attempt {}/{}): {}",
                        task_id,
                        final_record.retry_count,
                        final_record.task.retry_policy.max_retries,
                        e
                    );
                } else {
                    final_record.status = TaskStatus::Failed;
                    final_record.completed_at = Some(Utc::now());
                    final_record.updated_at = Utc::now();
                    final_record.error = Some(e.to_string());
                    
                    log::error!("Task {} failed: {}", task_id, e);
                }
            }
        }
        
        // 保存最终任务记录
        if let Err(e) = state_manager_clone.put(&format!("tasks/{}", task_id), &final_record).await {
            log::error!("Failed to update task record {}: {}", task_id, e);
        }
    });
    
    Ok(())
}

/// 检查是否应该重试任务
fn should_retry(task_record: &TaskRecord, error: &TaskError) -> bool {
    // 检查重试策略
    let retry_policy = &task_record.task.retry_policy;
    
    // 如果已达到最大重试次数，则不重试
    if task_record.retry_count >= retry_policy.max_retries {
        return false;
    }
    
    // 检查错误是否可重试
    match &retry_policy.retry_on {
        RetryOn::All => true,
        RetryOn::Specific(error_types) => {
            error_types.contains(&error.error_type())
        }
        RetryOn::None => false,
    }
}

/// 清理过期的任务历史
async fn cleanup_task_history(
    state_manager: &DistributedStateManager,
    task_history_ttl: Duration,
) -> Result<(), SchedulerError> {
    // 获取所有已完成的任务
    let tasks: Vec<TaskRecord> = state_manager.list("tasks/")
        .await
        .map_err(|e| SchedulerError::StateError(e.to_string()))?
        .iter()
        .filter_map(|key| {
            // 从键中提取任务ID
            let task_id = key.trim_start_matches("tasks/");
            // 获取任务详情
            state_manager.get::<TaskRecord>(&format!("tasks/{}", task_id))
                .map_or(None, |result| result.ok().flatten())
        })
        .collect();
        
    // 过滤出已完成且过期的任务
    let now = Utc::now();
    let expired_tasks: Vec<_> = tasks.into_iter()
        .filter(|task| {
            // 检查任务是否已完成
            let completed = task.status == TaskStatus::Completed || 
                          task.status == TaskStatus::Failed || 
                          task.status == TaskStatus::Cancelled;
                          
            if !completed {
                return false;
            }
            
            // 检查任务是否已过期
            if let Some(completed_at) = task.completed_at {
                let age = now.signed_duration_since(completed_at);
                age > chrono::Duration::from_std(task_history_ttl).unwrap()
            } else {
                false
            }
        })
        .collect();
        
    // 删除过期任务
    for task in expired_tasks {
        log::info!("Cleaning up expired task history for task {}", task.id);
        
        if let Err(e) = state_manager.delete(&format!("tasks/{}", task.id)).await {
            log::error!("Failed to delete expired task {}: {}", task.id, e);
        }
    }
    
    Ok(())
}

/// 恢复卡住的任务
async fn recover_stuck_tasks(state_manager: &DistributedStateManager) -> Result<(), SchedulerError> {
    // 获取所有运行中的任务
    let tasks: Vec<TaskRecord> = state_manager.list("tasks/")
        .await
        .map_err(|e| SchedulerError::StateError(e.to_string()))?
        .iter()
        .filter_map(|key| {
            // 从键中提取任务ID
            let task_id = key.trim_start_matches("tasks/");
            // 获取任务详情
            state_manager.get::<TaskRecord>(&format!("tasks/{}", task_id))
                .map_or(None, |result| result.ok().flatten())
        })
        .filter(|task| task.status == TaskStatus::Running)
        .collect();
        
    // 检查是否有卡住的任务
    let now = Utc::now();
    let stuck_timeout = chrono::Duration::minutes(30); // 30分钟超时
    
    for mut task in tasks {
        // 检查任务是否卡住
        if let Some(started_at) = task.started_at {
            let running_time = now.signed_duration_since(started_at);
            
            // 如果任务已运行超过指定时间，则认为卡住
            if running_time > stuck_timeout {
                log::warn!("Detected stuck task {}, resetting to pending state", task.id);
                
                // 更新任务状态为待处理
                task.status = TaskStatus::Pending;
                task.updated_at = now;
                task.error = Some(format!("Task was stuck in running state for {} minutes", running_time.num_minutes()));
                
                // 保存更新后的任务记录
                if let Err(e) = state_manager.put(&format!("tasks/{}", task.id), &task).await {
                    log::error!("Failed to update stuck task {}: {}", task.id, e);
                }
            }
        }
    }
    
    Ok(())
}

/// 同步调度元数据
async fn sync_schedule_metadata(state_manager: &DistributedStateManager) -> Result<(), SchedulerError> {
    // 获取所有调度
    let schedules: Vec<Schedule> = state_manager.list("schedules/")
        .await
        .map_err(|e| SchedulerError::StateError(e.to_string()))?
        .iter()
        .filter_map(|key| {
            // 从键中提取调度ID
            let schedule_id = key.trim_start_matches("schedules/");
            // 获取调度详情
            state_manager.get::<Schedule>(&format!("schedules/{}", schedule_id))
                .map_or(None, |result| result.ok().flatten())
        })
        .collect();
        
    // 更新元数据索引
    let metadata = ScheduleMetadata {
        count: schedules.len(),
        active_count: schedules.iter().filter(|s| s.enabled).count(),
        last_update: Utc::now(),
    };
    
    // 保存元数据
    state_manager.put("schedules/_metadata", &metadata).await
        .map_err(|e| SchedulerError::StateError(e.to_string()))?;
        
    Ok(())
}

/// 任务执行器
pub struct TaskExecutor {
    node_id: NodeId,
    max_concurrent_tasks: usize,
    handlers: RwLock<HashMap<String, Box<dyn TaskHandler>>>,
    active_tasks: RwLock<HashMap<TaskId, AbortHandle>>,
    semaphore: Semaphore,
    metrics: Arc<TaskMetrics>,
}

impl TaskExecutor {
    pub fn new(node_id: NodeId, max_concurrent_tasks: usize) -> Self {
        Self {
            node_id,
            max_concurrent_tasks,
            handlers: RwLock::new(HashMap::new()),
            active_tasks: RwLock::new(HashMap::new()),
            semaphore: Semaphore::new(max_concurrent_tasks),
            metrics: Arc::new(TaskMetrics::new()),
        }
    }
    
    pub async fn register_handler(&self, task_type: &str, handler: Box<dyn TaskHandler>) -> Result<(), SchedulerError> {
        let mut handlers = self.handlers.write().await;
        handlers.insert(task_type.to_string(), handler);
        
        log::info!("Registered handler for task type '{}'", task_type);
        
        Ok(())
    }
    
    pub async fn execute_task(&self, task_id: &TaskId, task: &Task, context: TaskContext) -> Result<String, TaskError> {
        // 获取适当的处理程序
        let handler = {
            let handlers = self.handlers.read().await;
            match handlers.get(&task.task_type) {
                Some(h) => h.clone(),
                None => return Err(TaskError::new("no_handler", &format!("No handler found for task type '{}'", task.task_type))),
            }
        };
        
        // 记录指标
        self.metrics.record_task_started(&task.task_type);
        let start_time = Instant::now();
        
        // 获取信号量许可，以限制并发任务数
        let permit = self.semaphore.acquire().await.map_err(|e| {
            TaskError::new("semaphore_error", &format!("Failed to acquire semaphore: {}", e))
        })?;
        
        // 创建可取消的任务
        let (abort_handle, abort_registration) = AbortHandle::new_pair();
        
        // 存储活动任务
        {
            let mut active_tasks = self.active_tasks.write().await;
            active_tasks.insert(task_id.clone(), abort_handle);
        }
        
        // 创建timeout future，如果设置了超时
        let timeout_duration = task.timeout.map(|t| Duration::from_secs(t));
        
        // 执行任务
        let result = if let Some(duration) = timeout_duration {
            // 带超时的执行
            let future = Abortable::new(
                handler.execute(task, context.clone()),
                abort_registration
            );
            
            match tokio::time::timeout(duration, future).await {
                Ok(Ok(result)) => Ok(result),
                Ok(Err(_)) => Err(TaskError::new("aborted", "Task was aborted")),
                Err(_) => Err(TaskError::new("timeout", &format!("Task timed out after {} seconds", duration.as_secs()))),
            }
        } else {
            // 不带超时的执行
            let future = Abortable::new(
                handler.execute(task, context.clone()),
                abort_registration
            );
            
            match future.await {
                Ok(result) => Ok(result),
                Err(_) => Err(TaskError::new("aborted", "Task was aborted")),
            }
        };
        
        // 清理
        {
            let mut active_tasks = self.active_tasks.write().await;
            active_tasks.remove(task_id);
        }
        
        // 释放信号量
        drop(permit);
        
        // 记录指标
        let duration = start_time.elapsed();
        match &result {
            Ok(_) => self.metrics.record_task_success(&task.task_type, duration),
            Err(_) => self.metrics.record_task_failure(&task.task_type, duration),
        }
        
        result
    }
    
    pub async fn cancel_task(&self, task_id: &TaskId) -> Result<(), SchedulerError> {
        let active_tasks = self.active_tasks.read().await;
        
        // 查找任务并中止
        if let Some(abort_handle) = active_tasks.get(task_id) {
            abort_handle.abort();
            log::info!("Aborted task {}", task_id);
            Ok(())
        } else {
            Err(SchedulerError::TaskNotRunning(task_id.clone()))
        }
    }
}

/// 任务处理程序特征
#[async_trait]
pub trait TaskHandler: Send + Sync + 'static {
    async fn execute(&self, task: &Task, context: TaskContext) -> Result<String, TaskError>;
    fn clone_box(&self) -> Box<dyn TaskHandler>;
}

impl Clone for Box<dyn TaskHandler> {
    fn clone(&self) -> Self {
        self.clone_box()
    }
}

/// HTTP请求任务处理程序
pub struct HttpRequestTaskHandler {
    client: Client,
}

impl HttpRequestTaskHandler {
    pub fn new() -> Self {
        Self {
            client: Client::new(),
        }
    }
}

#[async_trait]
impl TaskHandler for HttpRequestTaskHandler {
    async fn execute(&self, task: &Task, context: TaskContext) -> Result<String, TaskError> {
        // 解析参数
        let url = task.parameters.get("url")
            .ok_or_else(|| TaskError::new("missing_parameter", "Missing required parameter 'url'"))?;
            
        let method = task.parameters.get("method")
            .map(|s| s.as_str())
            .unwrap_or("GET");
            
        let body = task.parameters.get("body").cloned();
        let headers: HashMap<String, String> = task.parameters.get("headers")
            .and_then(|h| serde_json::from_str(h).ok())
            .unwrap_or_default();
            
        // 构建请求
        let mut request_builder = match method {
            "GET" => self.client.get(url),
            "POST" => self.client.post(url),
            "PUT" => self.client.put(url),
            "DELETE" => self.client.delete(url),
            "PATCH" => self.client.patch(url),
            _ => return Err(TaskError::new("invalid_parameter", &format!("Unsupported HTTP method: {}", method))),
        };
        
        // 添加头部
        for (key, value) in headers {
            request_builder = request_builder.header(key, value);
        }
        
        // 添加正文
        if let Some(b) = body {
            request_builder = request_builder.body(b);
        }
        
        // 发送请求
        let response = request_builder.send().await
            .map_err(|e| TaskError::new("request_failed", &format!("HTTP request failed: {}", e)))?;
            
        // 处理响应
        let status = response.status();
        let body = response.text().await
            .map_err(|e| TaskError::new("response_error", &format!("Failed to read response body: {}", e)))?;
            
        // 检查状态码
        if !status.is_success() {
            return Err(TaskError::new("http_error", &format!("HTTP error: {} - {}", status, body)));
        }
        
        // 返回响应
        Ok(body)
    }
    
    fn clone_box(&self) -> Box<dyn TaskHandler> {
        Box::new(Self::new())
    }
}

/// 命令行任务处理程序
pub struct ShellCommandTaskHandler;

impl ShellCommandTaskHandler {
    pub fn new() -> Self {
        Self
    }
}

#[async_trait]
impl TaskHandler for ShellCommandTaskHandler {
    async fn execute(&self, task: &Task, context: TaskContext) -> Result<String, TaskError> {
        // 解析参数
        let command = task.parameters.get("command")
            .ok_or_else(|| TaskError::new("missing_parameter", "Missing required parameter 'command'"))?;
            
        let shell = task.parameters.get("shell")
            .map(|s| s.as_str())
            .unwrap_or("sh");
            
        // 创建命令
        let output = match shell {
            "sh" => Command::new("sh").arg("-c").arg(command).output().await,
            "bash" => Command::new("bash").arg("-c").arg(command).output().await,
            "powershell" => Command::new("powershell").arg("-Command").arg(command).output().await,
            "cmd" => Command::new("cmd").arg("/C").arg(command).output().await,
            _ => return Err(TaskError::new("invalid_parameter", &format!("Unsupported shell: {}", shell))),
        };
        
        // 处理输出
        match output {
            Ok(output) => {
                let stdout = String::from_utf8_lossy(&output.stdout).to_string();
                let stderr = String::from_utf8_lossy(&output.stderr).to_string();
                
                // 检查命令是否成功
                if !output.status.success() {
                    return Err(TaskError::new(
                        "command_failed",
                        &format!(
                            "Command failed with exit code {}: {}",
                            output.status.code().unwrap_or(-1),
                            stderr
                        )
                    ));
                }
                
                Ok(stdout)
            }
            Err(e) => {
                Err(TaskError::new("execution_error", &format!("Failed to execute command: {}", e)))
            }
        }
    }
    
    fn clone_box(&self) -> Box<dyn TaskHandler> {
        Box::new(Self::new())
    }
}

/// 数据处理任务处理程序
pub struct DataProcessingTaskHandler;

impl DataProcessingTaskHandler {
    pub fn new() -> Self {
        Self
    }
}

#[async_trait]
impl TaskHandler for DataProcessingTaskHandler {
    async fn execute(&self, task: &Task, context: TaskContext) -> Result<String, TaskError> {
        // 解析参数
        let input = task.parameters.get("input")
            .ok_or_else(|| TaskError::new("missing_parameter", "Missing required parameter 'input'"))?;
            
        let operation = task.parameters.get("operation")
            .ok_or_else(|| TaskError::new("missing_parameter", "Missing required parameter 'operation'"))?;
            
        // 执行操作
        match operation.as_str() {
            "count_words" => {
                // 计算单词数
                let words = input.split_whitespace().count();
                Ok(serde_json::json!({ "word_count": words }).to_string())
            }
            "reverse" => {
                // 反转文本
                let reversed: String = input.chars().rev().collect();
                Ok(serde_json::json!({ "reversed": reversed }).to_string())
            }
            "uppercase" => {
                // 转换为大写
                let uppercase = input.to_uppercase();
                Ok(serde_json::json!({ "uppercase": uppercase }).to_string())
            }
            "lowercase" => {
                // 转换为小写
                let lowercase = input.to_lowercase();
                Ok(serde_json::json!({ "lowercase": lowercase }).to_string())
            }
            "json_parse" => {
                // 解析JSON
                let parsed: serde_json::Value = serde_json::from_str(input)
                    .map_err(|e| TaskError::new("parse_error", &format!("Failed to parse JSON: {}", e)))?;
                Ok(serde_json::json!({ "parsed": parsed }).to_string())
            }
            _ => {
                Err(TaskError::new("invalid_parameter", &format!("Unsupported operation: {}", operation)))
            }
        }
    }
    
    fn clone_box(&self) -> Box<dyn TaskHandler> {
        Box::new(Self::new())
    }
}

/// API服务器
pub struct ApiServer {
    config: ApiConfig,
    scheduler: Arc<SchedulerCore>,
    server_handle: Mutex<Option<JoinHandle<()>>>,
}

impl ApiServer {
    pub fn new(config: ApiConfig, scheduler: Arc<SchedulerCore>) -> Result<Self, SchedulerError> {
        Ok(Self {
            config,
            scheduler,
            server_handle: Mutex::new(None),
        })
    }
    
    pub async fn start(&self) -> Result<(), SchedulerError> {
        let mut handle_guard = self.server_handle.lock().await;
        
        // 如果已经运行，则不做任何事
        if handle_guard.is_some() {
            return Ok(());
        }
        
        // 解析监听地址
        let addr = self.config.listen_address.parse()
            .map_err(|e| SchedulerError::ConfigError(format!("Invalid listen address: {}", e)))?;
            
        let scheduler = self.scheduler.clone();
        
        // 构建API路由
        let app = Router::new()
            // 任务API
            .route("/tasks", post(move |body: Json<Task>| {
                let scheduler = scheduler.clone();
                async move {
                    match scheduler.submit_task(body.0).await {
                        Ok(task_id) => Ok(Json(json!({ "task_id": task_id }))),
                        Err(e) => Err(StatusCode::INTERNAL_SERVER_ERROR),
                    }
                }
            }))
            .route("/tasks/:id", get(move |Path(task_id): Path<String>| {
                let scheduler = scheduler.clone();
                async move {
                    match scheduler.get_task_status(&task_id).await {
                        Ok(status) => Ok(Json(json!({ "status": status }))),
                        Err(SchedulerError::TaskNotFound(_)) => Err(StatusCode::NOT_FOUND),
                        Err(_) => Err(StatusCode::INTERNAL_SERVER_ERROR),
                    }
                }
            }))
            .route("/tasks/:id/cancel", post(move |Path(task_id): Path<String>| {
                let scheduler = scheduler.clone();
                async move {
                    match scheduler.cancel_task(&task_id).await {
                        Ok(()) => Ok(Json(json!({ "success": true }))),
                        Err(SchedulerError::TaskNotFound(_)) => Err(StatusCode::NOT_FOUND),
                        Err(SchedulerError::TaskAlreadyCompleted(_)) => Err(StatusCode::BAD_REQUEST),
                        Err(_) => Err(StatusCode::INTERNAL_SERVER_ERROR),
                    }
                }
            }));
            
        // 启动HTTP服务器
        let handle = tokio::spawn(async move {
            axum::Server::bind(&addr)
                .serve(app.into_make_service())
                .await
                .unwrap();
        });
        
        *handle_guard = Some(handle);
        
        log::info!("API server started on {}", self.config.listen_address);
        
        Ok(())
    }
}

/// 任务指标
pub struct TaskMetrics {
    tasks_started: AtomicU64,
    tasks_succeeded: AtomicU64,
    tasks_failed: AtomicU64,
    task_duration: Histogram,
    task_type_counters: Mutex<HashMap<String, AtomicU64>>,
    task_type_durations: Mutex<HashMap<String, Histogram>>,
}

impl TaskMetrics {
    pub fn new() -> Self {
        Self {
            tasks_started: AtomicU64::new(0),
            tasks_succeeded: AtomicU64::new(0),
            tasks_failed: AtomicU64::new(0),
            task_duration: Histogram::new(),
            task_type_counters: Mutex::new(HashMap::new()),
            task_type_durations: Mutex::new(HashMap::new()),
        }
    }
    
    pub fn record_task_started(&self, task_type: &str) {
        self.tasks_started.fetch_add(1, Ordering::Relaxed);
        
        // 更新任务类型计数器
        let mut counters = self.task_type_counters.lock().unwrap();
        let counter = counters.entry(task_type.to_string())
            .or_insert_with(|| AtomicU64::new(0));
            
        counter.fetch_add(1, Ordering::Relaxed);
    }
    
    pub fn record_task_success(&self, task_type: &str, duration: Duration) {
        self.tasks_succeeded.fetch_add(1, Ordering::Relaxed);
        self.task_duration.record(duration.as_millis() as u64);
        
        // 更新任务类型持续时间
        let mut durations = self.task_type_durations.lock().unwrap();
        let histogram = durations.entry(task_type.to_string())
            .or_insert_with(|| Histogram::new());
            
        histogram.record(duration.as_millis() as u64);
    }
    
    pub fn record_task_failure(&self, task_type: &str, duration: Duration) {
        self.tasks_failed.fetch_add(1, Ordering::Relaxed);
        self.task_duration.record(duration.as_millis() as u64);
        
        // 更新任务类型持续时间
        let mut durations = self.task_type_durations.lock().unwrap();
        let histogram = durations.entry(task_type.to_string())
            .or_insert_with(|| Histogram::new());
            
        histogram.record(duration.as_millis() as u64);
    }
}
```

## 16. 总结

本文详细探讨了基于Rust 2025生态系统构建现代分布式系统框架的各个方面。我们不仅分析了核心组件的设计和实现，还展示了如何将它们组合成一个完整的、可扩展的框架。

Rust语言的安全保证和性能特性使其成为分布式系统开发的绝佳选择。到2025年，Rust生态系统在分布式计算领域已经成熟，提供了丰富的库和工具，涵盖从共识算法、通信协议到状态管理、监控和调试等各个方面。

我们的框架设计遵循以下关键原则：

1. **模块化设计**：每个组件都有明确定义的接口，可以独立使用或组合使用。
2. **类型安全**：充分利用Rust的类型系统，在编译时捕获许多潜在错误。
3. **可扩展性**：设计允许轻松添加新功能或替换现有组件。
4. **性能优先**：优化关键路径，最小化资源使用。
5. **可观测性**：内置全面的监控和调试支持。

通过整合开源生态系统中的优秀库，我们可以构建一个功能丰富、性能可靠的分布式系统框架，为IoT、边缘计算、云原生应用等领域提供强大支持。随着Rust生态系统的不断发展，这样的框架将继续演进，提供更丰富的功能和更好的开发体验。

## *思维导图*

```text
Rust分布式系统框架 (2025)
│
├── 核心组件
│   ├── 共识层
│   │   ├── Raft/Paxos实现
│   │   ├── 日志复制
│   │   ├── 领导者选举
│   │   └── 状态机复制
│   │
│   ├── 通信层
│   │   ├── gRPC/Tonic
│   │   ├── QUIC/quinn
│   │   ├── 自适应传输协议
│   │   └── P2P网络 (libp2p)
│   │
│   ├── 状态管理
│   │   ├── 分布式KV存储
│   │   ├── CRDT冲突解决
│   │   ├── 多级缓存系统
│   │   └── 状态迁移/版本控制
│   │
│   ├── 调度与任务
│   │   ├── 分布式工作流引擎
│   │   ├── Actor模型实现
│   │   ├── 批处理系统
│   │   └── 动态负载均衡
│   │
│   └── 可观测性
│       ├── 分布式追踪
│       ├── 指标收集与导出
│       ├── 结构化日志
│       └── 健康检查与告警
│
├── 高级特性
│   ├── 容错模式
│   │   ├── 断路器模式
│   │   ├── 重试与退避策略
│   │   ├── 隔离层实现
│   │   └── 故障恢复机制
│   │
│   ├── 网络优化
│   │   ├── 本地性感知路由
│   │   ├── 批处理与压缩
│   │   ├── 通信模式自适应
│   │   └── 网格网络拓扑
│   │
│   ├── 数据分区
│   │   ├── 一致性哈希
│   │   ├── 动态分区策略
│   │   ├── 自动再平衡
│   │   └── 分片迁移
│   │
│   └── 安全特性
│       ├── 节点身份验证
│       ├── 数据加密传输
│       ├── 访问控制
│       └── 审计日志
│
├── 开发工具
│   ├── 调试支持
│   │   ├── 分布式日志查询
│   │   ├── 追踪可视化
│   │   ├── 网络模拟器
│   │   └── 故障注入
│   │
│   ├── 测试框架
│   │   ├── 分布式属性测试
│   │   ├── 混沌测试工具
│   │   ├── 性能基准测试
│   │   └── 一致性检查器
│   │
│   └── 部署与管理
│       ├── K8s Operator
│       ├── 声明式配置
│       ├── 滚动升级策略
│       └── 多区域部署
│
├── 应用场景
│   ├── 边缘计算
│   │   ├── IoT设备协调
│   │   ├── 本地优先处理
│   │   ├── 离线操作支持
│   │   └── 有限资源优化
│   │
│   ├── 微服务架构
│   │   ├── 服务发现与注册
│   │   ├── API网关集成
│   │   ├── 认证与授权
│   │   └── 请求-响应模式
│   │
│   ├── 分布式存储
│   │   ├── 对象存储系统
│   │   ├── 时序数据库
│   │   ├── 分布式文件系统
│   │   └── 多活数据中心
│   │
│   └── 实时处理
│       ├── 流处理引擎
│       ├── 事件溯源系统
│       ├── 实时分析平台
│       └── CEP复杂事件处理
│
└── 关键生态集成
    ├── 存储集成
    │   ├── sled/redb
    │   ├── RocksDB绑定
    │   ├── TiKV客户端
    │   └── S3兼容接口
    │
    ├── 云原生集成
    │   ├── Kubernetes API
    │   ├── Prometheus导出
    │   ├── OpenTelemetry
    │   └── Istio/Linkerd适配
    │
    ├── 大数据生态
    │   ├── Apache Arrow集成
    │   ├── Parquet/ORC支持
    │   ├── Polars分析引擎
    │   └── Kafka连接器
    │
    └── AI/ML集成
        ├── 分布式模型训练
        ├── 在线推理服务
        ├── 特征存储
        └── A/B测试框架
```

## 17. 开发路线图与生态融合

将Rust分布式系统框架从概念转变为强大的生产系统需要一个明确的路线图。以下是2025年前的发展路径:

### 17.1 近期目标 (2023-2024)

1. **核心抽象开发**
   - 完善共识协议接口
   - 建立可靠的通信层抽象
   - 开发基本的状态管理原语

2. **建立基础测试框架**
   - 网络分区模拟
   - 故障注入机制
   - 性能基准套件

3. **社区与文档**
   - API文档生成工具链
   - 架构决策记录(ADR)
   - 贡献指南与代码规范

### 17.2 中期目标 (2024-2025)

1. **高级特性实现**
   - 自适应分区策略
   - 高级调度算法
   - 缓存一致性协议

2. **工具生态系统**
   - 可视化监控套件
   - 集群管理CLI工具
   - 分布式调试器

3. **生产就绪性**
   - 安全审计与加固
   - 大规模部署指南
   - 性能优化与基准测试

### 17.3 长期愿景

1. **跨语言生态系统整合**
   - 标准化协议定义
   - 多语言客户端库
   - 与现有系统互操作性

2. **垂直行业解决方案**
   - 金融服务特定模块
   - 医疗健康数据处理
   - 工业物联网框架

3. **研究前沿整合**
   - 形式化验证集成
   - 量子安全加密选项
   - 边缘AI优化运行时

## 18. Rust分布式编程最佳实践

在构建分布式系统时，有一些特定于Rust的最佳实践可以帮助开发者提高效率和系统质量:

### 18.1 类型系统运用

1. **状态机建模**

   ```rust
   enum NodeState {
       Follower { leader_id: Option<NodeId>, term: u64 },
       Candidate { votes: HashSet<NodeId>, term: u64 },
       Leader { term: u64, heartbeat_time: Instant },
   }
   ```

2. **不可能状态排除**

   ```rust
   // 使用类型系统确保只有Leader可以提交日志
   struct Leader { /* ... */ }
   
   impl Leader {
       pub fn commit_log(&self, entry: LogEntry) -> Result<(), Error> {
           // 只有Leader类型才能访问此方法
       }
   }
   ```

### 18.2 错误处理策略

1. **层次化错误类型**

   ```rust
   #[derive(thiserror::Error, Debug)]
   pub enum ClusterError {
       #[error("Consensus error: {0}")]
       Consensus(#[from] ConsensusError),
       
       #[error("Network error: {0}")]
       Network(#[from] NetworkError),
       
       #[error("State error: {0}")]
       State(#[from] StateError),
   }
   ```

2. **错误上下文**

   ```rust
   use eyre::{Result, WrapErr};
   
   async fn process_request(req: Request) -> Result<Response> {
       let user = authenticate(req)
           .wrap_err_with(|| format!("Failed to authenticate request from {}", req.source_ip))?;
       
       // ...更多处理
   }
   ```

### 18.3 异步编程模式

1. **选择性任务取消**

   ```rust
   let (cancel_token, cancel_guard) = CancelToken::new();
   
   // 在一个地方使用token启动可取消的任务
   let task = spawn_with_cancel(async move { 
       // 长时间运行的操作
   }, cancel_token);
   
   // 在另一个地方决定是否取消
   if should_cancel {
       cancel_guard.cancel();
   }
   ```

2. **超时处理**

   ```rust
   async fn with_timeout<F, T, E>(duration: Duration, future: F) -> Result<T, TimeoutError<E>>
   where
       F: Future<Output = Result<T, E>>,
   {
       tokio::time::timeout(duration, future)
           .await
           .map_err(|_| TimeoutError::Elapsed)?
           .map_err(TimeoutError::Inner)
   }
   ```

### 18.4 性能优化

1. **批量处理**

   ```rust
   // 批量提交日志条目而不是逐个提交
   pub async fn append_entries(&self, entries: Vec<LogEntry>) -> Result<(), Error> {
       // 单次网络往返批量处理
   }
   ```

2. **零拷贝处理**

   ```rust
   // 使用Bytes类型避免不必要的复制
   pub async fn process_message(msg: Bytes) -> Result<Bytes, Error> {
       // 处理消息而不需要复制整个payload
   }
   ```

## 19. 现实世界应用案例

### 19.1 电子商务平台库存管理

```rust
/// 分布式库存管理系统
pub struct InventoryManager {
    state_manager: Arc<DistributedStateManager>,
    reservation_ttl: Duration,
    metrics: Arc<InventoryMetrics>,
}

impl InventoryManager {
    /// 预留库存（购物车）
    pub async fn reserve_inventory(&self, product_id: &str, quantity: u32, session_id: &str) -> Result<ReservationId, InventoryError> {
        // 使用乐观并发控制实现并发预留
        let reservation_id = Uuid::new_v4().to_string();
        
        // 使用分布式锁确保一致性
        let lock_key = format!("inventory:lock:{}", product_id);
        let _lock = self.state_manager.acquire_lock(&lock_key).await?;
        
        // 获取当前库存
        let inventory: ProductInventory = self.state_manager
            .get(&format!("inventory:{}", product_id))
            .await?
            .ok_or(InventoryError::ProductNotFound)?;
            
        // 检查可用库存
        if inventory.available < quantity {
            return Err(InventoryError::InsufficientInventory);
        }
        
        // 创建预留记录
        let reservation = InventoryReservation {
            id: reservation_id.clone(),
            product_id: product_id.to_string(),
            quantity,
            session_id: session_id.to_string(),
            created_at: Utc::now(),
            expires_at: Utc::now() + chrono::Duration::from_std(self.reservation_ttl).unwrap(),
            status: ReservationStatus::Active,
        };
        
        // 更新库存
        let mut updated_inventory = inventory.clone();
        updated_inventory.available -= quantity;
        updated_inventory.reserved += quantity;
        
        // 存储预留和更新的库存
        let mut batch = WriteOperation::batch();
        batch.put(&format!("reservations:{}", reservation_id), &reservation);
        batch.put(&format!("inventory:{}", product_id), &updated_inventory);
        
        self.state_manager.commit_batch(batch).await?;
        
        // 记录指标
        self.metrics.record_reservation(product_id, quantity);
        
        // 启动TTL超时任务
        self.schedule_reservation_expiry(reservation_id.clone(), self.reservation_ttl).await;
        
        Ok(reservation_id)
    }
    
    /// 确认库存预留（下单）
    pub async fn confirm_reservation(&self, reservation_id: &str) -> Result<(), InventoryError> {
        // 类似实现，使用分布式锁和事务
    }
    
    /// 释放预留（购物车移除）
    pub async fn release_reservation(&self, reservation_id: &str) -> Result<(), InventoryError> {
        // 类似实现，使用分布式锁和事务
    }
}
```

### 19.2 实时数据分析流水线

```rust
/// 分布式流处理引擎
pub struct StreamProcessor {
    topology: ProcessingTopology,
    state_store: Arc<dyn StateStore>,
    source_connectors: HashMap<String, Box<dyn SourceConnector>>,
    sink_connectors: HashMap<String, Box<dyn SinkConnector>>,
}

impl StreamProcessor {
    /// 部署新的流处理作业
    pub async fn deploy_job(&self, job_config: JobConfig) -> Result<JobId, StreamError> {
        // 验证处理拓扑
        self.topology.validate(&job_config.topology)?;
        
        // 创建作业实例
        let job_id = Uuid::new_v4().to_string();
        let job = Job {
            id: job_id.clone(),
            config: job_config.clone(),
            status: JobStatus::Initializing,
            created_at: Utc::now(),
            metrics: JobMetrics::new(),
        };
        
        // 保存作业配置
        self.state_store.put(&format!("jobs:{}", job_id), &job).await?;
        
        // 初始化源连接器
        for source in &job_config.sources {
            if let Some(connector) = self.source_connectors.get(&source.connector_type) {
                connector.initialize(source, job_id.clone()).await?;
            } else {
                return Err(StreamError::UnknownConnector(source.connector_type.clone()));
            }
        }
        
        // 初始化接收连接器
        for sink in &job_config.sinks {
            if let Some(connector) = self.sink_connectors.get(&sink.connector_type) {
                connector.initialize(sink, job_id.clone()).await?;
            } else {
                return Err(StreamError::UnknownConnector(sink.connector_type.clone()));
            }
        }
        
        // 部署拓扑
        self.topology.deploy(&job_config.topology, job_id.clone()).await?;
        
        // 更新作业状态
        self.update_job_status(&job_id, JobStatus::Running).await?;
        
        Ok(job_id)
    }
    
    /// 处理传入的事件
    pub async fn process_event(&self, job_id: &str, event: Event) -> Result<Vec<Event>, StreamError> {
        // 获取作业配置
        let job: Job = self.state_store.get(&format!("jobs:{}", job_id)).await?
            .ok_or(StreamError::JobNotFound(job_id.to_string()))?;
            
        if job.status != JobStatus::Running {
            return Err(StreamError::JobNotRunning(job_id.to_string()));
        }
        
        // 处理事件
        let processed = self.topology.process_event(job_id, event).await?;
        
        // 更新处理指标
        // ...
        
        Ok(processed)
    }
}
```

## 20. 结论与未来展望

Rust分布式系统框架在2025年已经成为构建高可靠、高性能分布式系统的首选工具之一。
随着云原生和边缘计算的持续发展，这些系统的重要性将继续增长。

Rust独特的安全保证、零成本抽象和不断成熟的生态系统共同创造了一个强大的基础，使开发者能够构建下一代分布式系统。
通过组合经过验证的共识算法、高效的通信层、灵活的状态管理和全面的可观测性，我们可以构建适应各种需求的系统。

随着量子计算、边缘AI和全球规模计算的崛起，
Rust分布式框架将继续演进，利用先进的安全技术、自适应算法和混合部署模型，以满足未来计算系统的需求。
通过坚实的类型系统和表达能力，
Rust提供了一个独特的舞台，让我们能够设计出安全、高效且具备高度适应性的分布式系统。
