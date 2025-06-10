# Rust分布式系统设计：从理论到实践

```text
<think>
用户希望我重新生成一份关于Rust分布式系统设计的内容，使用markdown格式并包含目录。
需要按照之前的风格和深度，但转向Rust分布式系统设计的主题。
我将保持中文回复，按照用户要求使用markdown格式，并在开头添加目录。

我将创建一个全面的指南，涵盖Rust在分布式系统中的应用，包括基础概念、设计模式、实现技术和实际案例。
内容需要有足够的技术深度，同时保持结构清晰。
</think>
```

## 目录

- [Rust分布式系统设计：从理论到实践](#rust分布式系统设计从理论到实践)
  - [目录](#目录)
  - [1. 分布式系统基础](#1-分布式系统基础)
    - [1.1 分布式系统的核心概念](#11-分布式系统的核心概念)
    - [1.2 CAP定理与系统设计权衡](#12-cap定理与系统设计权衡)
    - [1.3 一致性模型谱系](#13-一致性模型谱系)
    - [1.4 分布式系统中的时间与事件排序](#14-分布式系统中的时间与事件排序)
    - [1.5 Rust语言特性与分布式系统的契合点](#15-rust语言特性与分布式系统的契合点)
  - [2. Rust并发与分布式基础](#2-rust并发与分布式基础)
    - [2.1 所有权模型与并发安全](#21-所有权模型与并发安全)
    - [2.2 线程模型与异步编程](#22-线程模型与异步编程)
    - [2.3 Actor模型在Rust中的实现](#23-actor模型在rust中的实现)
    - [2.4 类型系统对分布式编程的支持](#24-类型系统对分布式编程的支持)
    - [2.5 错误处理与分布式系统的容错性](#25-错误处理与分布式系统的容错性)
  - [3. 分布式系统设计模式](#3-分布式系统设计模式)
    - [3.1 消息传递模式](#31-消息传递模式)
    - [3.2 状态复制与共识](#32-状态复制与共识)
    - [3.3 分区与数据分片](#33-分区与数据分片)
    - [3.4 故障检测与自愈](#34-故障检测与自愈)
    - [3.5 分布式事务模式](#35-分布式事务模式)
  - [4. Rust分布式系统组件](#4-rust分布式系统组件)
    - [4.1 网络库与协议实现](#41-网络库与协议实现)
    - [4.2 序列化与数据编码](#42-序列化与数据编码)
    - [4.3 分布式日志和监控](#43-分布式日志和监控)
    - [4.4 分布式配置管理](#44-分布式配置管理)
    - [4.5 分布式中间件集成](#45-分布式中间件集成)
    - [4.6 服务发现与注册](#46-服务发现与注册)
    - [4.7 分布式系统测试](#47-分布式系统测试)
    - [5. 总结与最佳实践](#5-总结与最佳实践)
      - [5.1 系统设计原则](#51-系统设计原则)
      - [5.2 Rust在分布式系统中的优势](#52-rust在分布式系统中的优势)
      - [5.3 常见陷阱与解决方法](#53-常见陷阱与解决方法)
      - [5.4 持续改进](#54-持续改进)

## 1. 分布式系统基础

### 1.1 分布式系统的核心概念

分布式系统是由多个独立计算节点组成的网络，这些节点通过消息传递进行通信和协调，共同完成特定的计算任务。与单机系统相比，分布式系统具有更高的可扩展性、容错性和可用性，但同时也面临着诸多挑战。

**分布式系统的基本特征：**

```rust
分布式系统 = {
    物理分布: "计算节点在地理位置上分散",
    通信延迟: "节点间通信存在不可忽略的延迟",
    独立故障: "部分节点故障不影响整体系统",
    并发操作: "多节点同时执行操作",
    无全局时钟: "缺乏精确统一的时间参考",
    异构环境: "不同节点可能有不同的硬件和软件配置"
}
```

**分布式系统的核心挑战：**

1. **一致性与可用性的权衡**：如何在保证数据一致性的同时维持系统的高可用性
2. **部分故障处理**：如何检测、隔离和恢复局部故障，而不影响整体系统功能
3. **网络分区容忍**：如何在网络分区情况下继续提供服务
4. **可扩展性维护**：如何设计系统使其能够平滑地扩展到更多节点
5. **分布式协调**：如何在无中心协调的情况下达成一致决策

在Rust语言环境下构建分布式系统有独特的优势：内存安全、并发安全、高效性能以及丰富的类型系统，这些特性使得Rust成为实现分布式系统的理想选择。

### 1.2 CAP定理与系统设计权衡

CAP定理是分布式系统设计中的基础理论，它指出在网络分区的情况下，系统不能同时保证一致性(Consistency)和可用性(Availability)。

**CAP定理的形式化表述：**

```rust
CAP定理 = {
    一致性(C): "所有节点在同一时间看到相同的数据",
    可用性(A): "每个请求都能收到响应，无论成功或失败",
    分区容忍性(P): "系统在网络分区的情况下仍能继续运行"
}

在网络分区(P)的情况下，系统设计者必须在一致性(C)和可用性(A)之间做出选择。
```

**CAP权衡的系统类型：**

1. **CP系统**：优先保证一致性，在网络分区时可能牺牲可用性
   - 例如：分布式数据库如PostgreSQL集群、ZooKeeper、etcd
   - Rust实现：`tikv`、`sled`

2. **AP系统**：优先保证可用性，在网络分区时可能牺牲一致性
   - 例如：NoSQL数据库如Cassandra、DynamoDB
   - Rust实现：`InfluxDB IOx`

3. **CA系统**：在不存在网络分区的环境中同时保证一致性和可用性
   - 注意：在实际的分布式环境中，网络分区总是可能发生的

在Rust中设计分布式系统时，可以利用类型系统明确表达CAP权衡：

```rust
// CAP权衡的类型表示示例
enum ConsistencyModel {
    Strong,     // 强一致性 (CP倾向)
    Eventual,   // 最终一致性 (AP倾向)
    Causal,     // 因果一致性 (AP与CP之间)
    // 其他一致性模型...
}

struct SystemConfig<C: ConsistencyPolicy, A: AvailabilityPolicy> {
    consistency_policy: C,
    availability_policy: A,
    network_partition_strategy: PartitionStrategy,
    // 其他配置...
}
```

在系统设计中，还需要考虑PACELC定理的扩展，即在没有分区(P)的情况下，系统仍然面临延迟(L)和一致性(C)之间的权衡。

### 1.3 一致性模型谱系

分布式系统中的一致性模型形成了一个从强到弱的谱系，不同的一致性模型适用于不同的应用场景。

**一致性模型谱系（从强到弱）：**

```rust
一致性模型谱系 = [
    线性一致性: {
        定义: "所有操作看起来是按照全局实时顺序执行的",
        特点: "最强的一致性保证，但成本最高",
        应用: "分布式锁、领导者选举"
    },
    
    顺序一致性: {
        定义: "所有进程看到的所有操作的顺序相同",
        特点: "比线性一致性稍弱，不要求与实时一致",
        应用: "共享内存系统"
    },
    
    因果一致性: {
        定义: "因果相关的操作在所有节点上以相同顺序观察到",
        特点: "只保证有因果关系的操作的顺序",
        应用: "分布式日志系统"
    },
    
    最终一致性: {
        定义: "在没有新更新的情况下，最终所有副本将收敛到相同状态",
        特点: "弱一致性保证，但高可用性和性能",
        应用: "DNS系统、社交媒体feed"
    }
]
```

在Rust中实现不同的一致性模型：

```rust
// 不同一致性模型的Rust表示
trait ConsistencyModel {
    fn validate_operation(&self, op: &Operation) -> bool;
    fn apply_operation(&mut self, op: Operation) -> Result<(), ConsistencyError>;
}

// 线性一致性模型实现
struct LinearizableConsistency {
    operations: Vec<TimestampedOperation>,
    lock: Arc<RwLock<()>>,
}

impl ConsistencyModel for LinearizableConsistency {
    fn validate_operation(&self, op: &Operation) -> bool {
        // 确保操作的时间戳晚于所有已应用的操作
        let guard = self.lock.read().unwrap();
        if let Some(last_op) = self.operations.last() {
            return op.timestamp > last_op.timestamp;
        }
        true
    }
    
    fn apply_operation(&mut self, op: Operation) -> Result<(), ConsistencyError> {
        let guard = self.lock.write().unwrap();
        if self.validate_operation(&op) {
            let timestamped_op = TimestampedOperation {
                operation: op,
                timestamp: SystemTime::now(),
            };
            self.operations.push(timestamped_op);
            Ok(())
        } else {
            Err(ConsistencyError::InvalidOperationOrder)
        }
    }
}

// 最终一致性模型实现
struct EventualConsistency {
    operations: Vec<Operation>,
    propagation_queue: AsyncQueue<Operation>,
}

impl ConsistencyModel for EventualConsistency {
    fn validate_operation(&self, _op: &Operation) -> bool {
        // 最终一致性接受所有操作
        true
    }
    
    fn apply_operation(&mut self, op: Operation) -> Result<(), ConsistencyError> {
        self.operations.push(op.clone());
        self.propagation_queue.push(op);
        Ok(())
    }
}
```

选择适当的一致性模型对分布式系统的性能和可用性至关重要。
Rust的类型系统可以帮助设计者在编译时捕获一致性违反问题。

### 1.4 分布式系统中的时间与事件排序

在分布式系统中，由于缺乏全局时钟，事件的排序成为一个基础性问题。正确的事件排序对于维护一致性、处理并发操作和检测因果关系至关重要。

**常见的时间和事件排序机制：**

1. **物理时钟**：
   - 使用NTP等协议同步节点时间
   - 存在精度限制和时钟漂移问题

2. **逻辑时钟**：
   - Lamport时钟：为每个事件分配单调递增的时间戳
   - 向量时钟：捕获事件间的因果关系

3. **混合时钟**：
   - TrueTime (Google Spanner)：物理时钟与不确定性界限相结合
   - Hybrid Logical Clocks：结合物理时钟和逻辑时钟的优点

在Rust中实现向量时钟：

```rust
use std::collections::HashMap;
use std::cmp::max;

#[derive(Clone, Debug, PartialEq, Eq)]
struct VectorClock {
    // 节点ID到逻辑时间的映射
    clock: HashMap<String, u64>,
    node_id: String,
}

impl VectorClock {
    pub fn new(node_id: String) -> Self {
        let mut clock = HashMap::new();
        clock.insert(node_id.clone(), 0);
        Self { clock, node_id }
    }
    
    // 本地事件发生时递增当前节点的计数器
    pub fn increment(&mut self) {
        let counter = self.clock.entry(self.node_id.clone()).or_insert(0);
        *counter += 1;
    }
    
    // 接收消息时合并向量时钟
    pub fn merge(&mut self, other: &VectorClock) {
        for (node, &time) in &other.clock {
            let entry = self.clock.entry(node.clone()).or_insert(0);
            *entry = max(*entry, time);
        }
    }
    
    // 检查因果关系
    pub fn happens_before(&self, other: &VectorClock) -> bool {
        // 检查self是否严格早于other
        let mut at_least_one_less = false;
        
        for (node, &self_time) in &self.clock {
            let other_time = other.clock.get(node).copied().unwrap_or(0);
            
            if self_time > other_time {
                return false;
            }
            
            if self_time < other_time {
                at_least_one_less = true;
            }
        }
        
        // 检查other中是否有self中不存在的节点
        for (node, &other_time) in &other.clock {
            if !self.clock.contains_key(node) && other_time > 0 {
                at_least_one_less = true;
            }
        }
        
        at_least_one_less
    }
    
    // 检查是否并发
    pub fn concurrent_with(&self, other: &VectorClock) -> bool {
        !self.happens_before(other) && !other.happens_before(self)
    }
}
```

向量时钟使我们能够检测分布式系统中事件的因果关系，这对于实现因果一致性和解决冲突至关重要。

**分布式系统中的逻辑时间应用**：

1. **冲突检测与解决**：在最终一致性系统中识别并发修改
2. **因果一致性实现**：确保因果相关的操作按正确顺序执行
3. **分布式快照**：捕获系统的一致性全局状态
4. **故障检测**：判断节点是否失效

### 1.5 Rust语言特性与分布式系统的契合点

Rust语言的多项特性使其成为构建分布式系统的理想选择。

**Rust对分布式系统的核心优势：**

```rust
Rust优势 = {
    内存安全: "无需垃圾收集的内存安全保证减少运行时故障",
    并发安全: "编译时防止数据竞争和死锁",
    性能高效: "接近C/C++的性能满足分布式系统的高吞吐需求",
    零成本抽象: "提供高级抽象而不牺牲性能",
    错误处理: "强制处理错误情况，提高系统可靠性",
    类型系统: "强大的类型系统捕获更多分布式编程错误",
    跨平台支持: "在不同节点环境中保持一致行为"
}
```

**具体特性与分布式场景的映射：**

1. **所有权系统与资源管理**：
   - 确保网络连接、文件句柄等资源的正确管理
   - 防止资源泄漏导致的系统退化

2. **错误处理机制与故障容忍**：
   - `Result`类型强制处理操作失败的可能性
   - `?`操作符简化错误传播，使代码更清晰

3. **类型系统与协议安全**：
   - 通过类型表达节点间通信协议
   - 在编译时捕获协议不匹配错误

4. **特质系统与组件抽象**：
   - 为分布式系统组件定义清晰的接口
   - 支持模块化和可替换的实现

5. **异步编程与高效I/O**：
   - 非阻塞I/O模型适合网络通信
   - 高效处理大量并发连接

Rust在分布式系统中的示例应用模式：

```rust
// 使用Rust特质定义分布式节点接口
trait DistributedNode {
    // 节点标识符
    fn id(&self) -> NodeId;
    
    // 处理接收到的消息
    async fn handle_message(&mut self, msg: Message) -> Result<Option<Message>, NodeError>;
    
    // 发送消息到其他节点
    async fn send_message(&self, to: NodeId, msg: Message) -> Result<(), NetworkError>;
    
    // 节点健康检查
    async fn health_check(&self) -> NodeStatus;
}

// 使用枚举表示分布式系统中的各种消息类型
#[derive(Debug, Clone, Serialize, Deserialize)]
enum Message {
    // 共识消息
    Propose { proposal_id: u64, value: Vec<u8> },
    Accept { proposal_id: u64 },
    Reject { proposal_id: u64, reason: String },
    
    // 数据复制消息
    Replicate { key: String, value: Vec<u8>, version: u64 },
    ReplicateAck { key: String, version: u64 },
    
    // 成员关系与发现消息
    Join { node_id: NodeId, address: SocketAddr },
    Leave { node_id: NodeId },
    HeartbeatRequest,
    HeartbeatResponse { status: NodeStatus },
    
    // 其他消息类型...
}

// 使用Result表达操作的成功或失败
type NodeResult<T> = Result<T, NodeError>;

// 详细的错误类型
#[derive(Debug, thiserror::Error)]
enum NodeError {
    #[error("网络错误: {0}")]
    Network(#[from] NetworkError),
    
    #[error("存储错误: {0}")]
    Storage(#[from] StorageError),
    
    #[error("共识错误: {0}")]
    Consensus(String),
    
    #[error("节点已停止")]
    NodeStopped,
    
    #[error("超时: {operation} after {timeout:?}")]
    Timeout { operation: String, timeout: Duration },
    
    // 其他错误类型...
}
```

这些示例展示了如何利用Rust的类型系统和错误处理来提高分布式系统的安全性和可靠性。通过在编译时捕获更多错误，Rust帮助开发者构建更健壮的分布式系统。

## 2. Rust并发与分布式基础

### 2.1 所有权模型与并发安全

Rust的所有权模型是其区别于其他语言的核心特性，它通过编译时检查确保内存安全和并发安全，无需垃圾收集器。在分布式系统中，这种安全保证尤为重要。

**所有权规则的基本原则：**

1. **每个值有唯一的所有者**
2. **所有权可以转移，但在同一时间只有一个所有者**
3. **当所有者离开作用域，值被丢弃**

这些规则如何支持分布式系统开发：

```rust
// 在节点间安全传输数据所有权
fn main() {
    // 创建数据，node1是所有者
    let mut node1 = DistributedNode::new("node1");
    let data = vec![1, 2, 3, 4, 5]; // node1拥有data
    
    // 将数据发送到node2，所有权转移
    // data不能再在node1中使用
    let node2 = node1.send_data("node2", data);
    
    // 错误：data的所有权已转移
    // println!("Data: {:?}", data);
    
    // node2可以安全地使用和修改数据
    let result = node2.process_data();
    println!("Result: {:?}", result);
}
```

**所有权与借用在分布式系统中的应用：**

1. **消息传递的所有权语义**：
   - 发送消息时转移所有权，确保消息不被重复发送
   - 接收方获得消息的所有权，可以安全处理

2. **共享状态的借用规则**：
   - 多个不可变引用（&T）允许并发读取
   - 单个可变引用（&mut T）确保独占写入
   - 防止数据竞争的并发访问模式

3. **线程间数据共享**：
   - `Arc<T>`：原子引用计数，安全共享不可变数据
   - `Mutex<T>`、`RwLock<T>`：安全共享可变数据
   - Channels：在线程间传递所有权

在分布式节点实现中应用所有权模型：

```rust
use std::sync::{Arc, Mutex};
use std::collections::HashMap;

// 分布式节点实现
struct Node {
    id: String,
    // 共享的不可变配置
    config: Arc<Config>,
    // 线程安全的可变状态
    state: Arc<Mutex<NodeState>>,
    // 与其他节点的连接
    connections: Arc<Mutex<HashMap<String, Connection>>>,
}

struct NodeState {
    is_leader: bool,
    term: u64,
    log: Vec<LogEntry>,
    // 其他状态...
}

impl Node {
    // 启动节点处理循环
    pub fn run(&self) -> Result<(), NodeError> {
        loop {
            // 接收消息（获得消息的所有权）
            let message = self.receive_message()?;
            
            // 处理消息并可能生成响应
            let response = self.process_message(message)?;
            
            // 发送响应（转移响应的所有权）
            if let Some(resp) = response {
                self.send_response(resp)?;
            }
        }
    }
    
    // 更新节点状态，使用互斥锁确保线程安全
    fn update_state<F, R>(&self, update_fn: F) -> R
    where
        F: FnOnce(&mut NodeState) -> R
    {
        let mut state = self.state.lock().unwrap();
        update_fn(&mut state)
    }
    
    // 处理选举请求
    fn handle_vote_request(&self, request: VoteRequest) -> Result<VoteResponse, NodeError> {
        self.update_state(|state| {
            if request.term > state.term {
                state.term = request.term;
                state.is_leader = false;
                
                // 授予投票
                Ok(VoteResponse {
                    term: state.term,
                    vote_granted: true,
                })
            } else {
                // 拒绝投票
                Ok(VoteResponse {
                    term: state.term,
                    vote_granted: false,
                })
            }
        })
    }
}
```

所有权模型通过在编译时防止数据竞争和悬垂指针，显著提高了分布式系统的可靠性。即使在多线程环境下，Rust程序员也能写出安全的代码，减少潜在的并发错误。

### 2.2 线程模型与异步编程

分布式系统需要高效处理并发任务和I/O操作。Rust提供了两种主要的并发模型：基于线程的并发和异步编程。

**线程模型**：

Rust的标准库提供了1:1的线程模型，每个Rust线程对应一个操作系统线程：

```rust
use std::thread;
use std::time::Duration;

fn main() {
    // 创建10个工作线程
    let mut handles = vec![];
    
    for i in 0..10 {
        // 创建线程并移动i的所有权到闭包中
        let handle = thread::spawn(move || {
            println!("Worker {i} started");
            // 模拟工作
            thread::sleep(Duration::from_millis(100 * i));
            println!("Worker {i} finished");
            
            // 返回结果
            i * i
        });
        
        handles.push(handle);
    }
    
    // 等待所有线程完成并收集结果
    let results: Vec<u64> = handles.into_iter()
        .map(|h| h.join().unwrap())
        .collect();
    
    println!("Results: {:?}", results);
}
```

**线程间通信**：

Rust提供多种机制用于线程间安全通信：

1. **通道(Channels)**：消息传递机制，适合生产者-消费者模式
2. **共享内存**：通过Arc和同步原语共享状态
3. **线程本地存储**：使用thread_local!宏实现线程局部变量

```rust
use std::sync::mpsc;
use std::thread;

fn main() {
    // 创建通道
    let (tx, rx) = mpsc::channel();
    
    // 创建多个发送者
    for i in 0..5 {
        let tx = tx.clone();
        thread::spawn(move || {
            // 生成任务
            let task = format!("Task from thread {}", i);
            // 发送任务
            tx.send(task).unwrap();
        });
    }
    
    // 丢弃原始发送者
    drop(tx);
    
    // 接收所有消息直到通道关闭
    while let Ok(message) = rx.recv() {
        println!("Received: {}", message);
    }
}
```

**异步编程**：

Rust的异步编程模型基于Future特质，这是一种表示尚未完成计算的抽象：

```rust
use tokio::net::{TcpListener, TcpStream};
use tokio::io::{AsyncReadExt, AsyncWriteExt};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建TCP监听器
    let listener = TcpListener::bind("127.0.0.1:8080").await?;
    println!("Server listening on port 8080");
    
    loop {
        // 异步等待连接
        let (socket, addr) = listener.accept().await?;
        println!("New client connected: {}", addr);
        
        // 为每个连接生成一个任务
        tokio::spawn(async move {
            // 处理连接
            if let Err(e) = handle_connection(socket).await {
                eprintln!("Error handling connection: {}", e);
            }
        });
    }
}

async fn handle_connection(mut socket: TcpStream) -> Result<(), Box<dyn std::error::Error>> {
    let mut buffer = vec![0; 1024];
    
    // 读取请求
    let n = socket.read(&mut buffer).await?;
    let request = String::from_utf8_lazy(&buffer[..n])?;
    
    // 处理请求...
    println!("Received request: {}", request);
    
    // 发送响应
    let response = "HTTP/1.1 200 OK\r\n\r\nHello, World!";
    socket.write_all(response.as_bytes()).await?;
    
    Ok(())
}
```

**异步运行时**：

Rust的异步编程需要运行时支持，常用的异步运行时包括：

1. **Tokio**：功能全面的异步运行时，适合网络编程
2. **async-std**：类似标准库API的异步运行时
3. **smol**：轻量级异步运行时

在分布式系统中，异步编程特别有价值，因为它能够：

- 以少量线程高效处理大量连接
- 降低上下文切换开销
- 提高I/O密集型应用的吞吐量
- 简化并发代码，避免回调地狱

**结合线程和异步的混合策略**：

在实际的分布式系统中，通常会结合使用线程和异步：

```rust
use tokio::sync::mpsc;
use tokio::task;

#[tokio::main]
async fn main() {
    // 创建通道
    let (tx, mut rx) = mpsc::channel(100);
    
    // 生成异步任务接收消息
    let processor = tokio::spawn(async move {
        while let Some(item) = rx.recv().await {
            println!("Processing item: {}", item);
            // 处理消息...
        }
    });
    
    // 生成多个任务发送消息
    let mut handles = vec![];
    for i in 0..10 {
        let tx = tx.clone();
        let handle = task::spawn(async move {
            for j in 0..5 {
                let msg = format!("Message {}-{}", i, j);
                tx.send(msg).await.unwrap();
                // 模拟一些工作
                tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
            }
        });
        handles.push(handle);
    }
    
    // 等待所有发送方完成
    for handle in handles {
        handle.await.unwrap();
    }
    
    // 关闭通道
    drop(tx);
    
    // 等待处理器完成
    processor.await.unwrap();
}
```

在分布式系统中，合理选择并发模型和线程策略对性能至关重要。Rust的安全并发模型使开发者能够编写高效、可靠的分布式系统代码。

### 2.3 Actor模型在Rust中的实现

Actor模型是分布式系统设计中的一种流行范式，它将系统构建为独立的计算单元（actors），这些单元通过消息传递进行通信。Rust的所有权系统和消息传递机制使其非常适合实现Actor模型。

**Actor模型的核心概念**：

```rust
Actor = {
    状态: "Actor的私有内部状态",
    行为: "处理接收消息的逻辑",
    通信: "通过消息与其他Actor交互",
    创建: "能够创建新的Actor",
    监督: "监控子Actor并处理失败"
}
```

**Rust中的Actor实现**：

1. **使用Actix框架**：

```rust
use actix::{Actor, Context, Handler, Message, System};

// 定义消息类型
#[derive(Message)]
#[rtype(result = "String")]
struct Ping {
    message: String,
}

// 定义Actor
struct PingActor {
    count: usize,
}

impl Actor for PingActor {
    type Context = Context<Self>;
    
    fn started(&mut self, ctx: &mut Self::Context) {
        println!("PingActor started");
    }
}

// 实现消息处理
impl Handler<Ping> for PingActor {
    type Result = String;
    
    fn handle(&mut self, msg: Ping, _ctx: &mut Context<Self>) -> Self::Result {
        self.count += 1;
        println!("Received ping: {}, count: {}", msg.message, self.count);
        format!("Pong: {}", msg.message)
    }
}

#[actix_rt::main]
async fn main() {
    // 创建actor
    let addr = PingActor { count: 0 }.start();
    
    // 发送消息并等待响应
    let result = addr.send(Ping {
        message: "Hello, Actor!".to_string()
    }).await;
    
    match result {
        Ok(response) => println!("Got response: {}", response),
        Err(e) => eprintln!("Error: {}", e),
    }
    
    // 再次发送消息
    if let Ok(response) = addr.send(Ping {
        message: "Second ping".to_string()
    }).await {
        println!("Got response: {}", response);
    }
    
    // 关闭系统
    System::current().stop();
}
```

1. **使用Tokio自行实现Actor模式**：

```rust
use tokio::sync::{mpsc, oneshot};
use std::collections::HashMap;
use std::error::Error;

// Actor消息类型
enum KeyValueMessage {
    Get {
        key: String,
        respond_to: oneshot::Sender<Option<String>>,
    },
    Set {
        key: String,
        value: String,
        respond_to: oneshot::Sender<bool>,
    },
    Delete {
        key: String,
        respond_to: oneshot::Sender<bool>,
    },
}

// KeyValue Actor实现
struct KeyValueActor {
    data: HashMap<String, String>,
    receiver: mpsc::Receiver<KeyValueMessage>,
}

impl KeyValueActor {
    fn new(receiver: mpsc::Receiver<KeyValueMessage>) -> Self {
        Self {
            data: HashMap::new(),
            receiver,
        }
    }
    
    // Actor的主循环
    async fn run(&mut self) {
        while let Some(msg) = self.receiver.recv().await {
            self.handle_message(msg).await;
        }
        println!("KeyValueActor stopped");
    }
    
    // 消息处理
    async fn handle_message(&mut self, msg: KeyValueMessage) {
        match msg {
            KeyValueMessage::Get { key, respond_to } => {
                let result = self.data.get(&key).cloned();
                // 忽略发送错误，意味着请求方已经放弃等待
                let _ = respond_to.send(result);
            }
            KeyValueMessage::Set { key, value, respond_to } => {
                self.data.insert(key, value);
                let _ = respond_to.send(true);
            }
            KeyValueMessage::Delete { key, respond_to } => {
                let existed = self.data.remove(&key).is_some();
                let _ = respond_to.send(existed);
            }
        }
    }
}

// Actor句柄，用于与Actor通信
#[derive(Clone)]
struct KeyValueHandle {
    sender: mpsc::Sender<KeyValueMessage>,
}

impl KeyValueHandle {
    fn new() -> Self {
        let (sender, receiver) = mpsc::channel(100);
        
        // 在后台任务中启动actor
        let mut actor = KeyValueActor::new(receiver);
        tokio::spawn(async move {
            actor.run().await;
        });
        
        Self { sender }
    }
    
    async fn get(&self, key: String) -> Result<Option<String>, Box<dyn Error>> {
        let (send, recv) = oneshot::channel();
        
        self.sender.send(KeyValueMessage::Get {
            key,
            respond_to: send,
        }).await?;
        
        Ok(recv.await?)
    }
    
    async fn set(&self, key: String, value: String) -> Result<bool, Box<dyn Error>> {
        let (send, recv) = oneshot::channel();
        
        self.sender.send(KeyValueMessage::Set {
            key,
            value,
            respond_to: send,
        }).await?;
        
        Ok(recv.await?)
    }
    
    async fn delete(&self, key: String) -> Result<bool, Box<dyn Error>> {
        let (send, recv) = oneshot::channel();
        
        self.sender.send(KeyValueMessage::Delete {
            key,
            respond_to: send,
        }).await?;
        
        Ok(recv.await?)
    }
}

// 使用示例
#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    // 创建KV Store Actor句柄
    let kv_store = KeyValueHandle::new();
    
    // 设置一些值
    kv_store.set("name".to_string(), "张三".to_string()).await?;
    kv_store.set("city".to_string(), "北京".to_string()).await?;
    
    // 获取值
    if let Some(name) = kv_store.get("name".to_string()).await? {
        println!("Name: {}", name);
    }
    
    // 删除值
    let deleted = kv_store.delete("city".to_string()).await?;
    println!("City deleted: {}", deleted);
    
    // 尝试获取已删除的值
    let city = kv_store.get("city".to_string()).await?;
    println!("City is now: {:?}", city);
    
    Ok(())
}
```

**Actor模型在分布式系统中的应用**：

1. **分布式计算**：将大型计算任务分解为可由不同节点上的actors执行的小型任务

```rust
// 分布式任务处理Actor
struct WorkerActor {
    worker_id: String,
    processed_count: usize,
}

impl Actor for WorkerActor {
    type Context = Context<Self>;
}

#[derive(Message)]
#[rtype(result = "TaskResult")]
struct Task {
    id: String,
    data: Vec<u8>,
}

struct TaskResult {
    task_id: String,
    result: Vec<u8>,
    worker_id: String,
}

impl Handler<Task> for WorkerActor {
    type Result = TaskResult;
    
    fn handle(&mut self, msg: Task, _ctx: &mut Context<Self>) -> Self::Result {
        // 处理任务
        println!("Worker {} processing task {}", self.worker_id, msg.id);
        
        // 模拟计算
        let result = msg.data.iter().map(|&x| x * 2).collect();
        self.processed_count += 1;
        
        TaskResult {
            task_id: msg.id,
            result,
            worker_id: self.worker_id.clone(),
        }
    }
}
```

1. **容错与监督**：通过监督策略处理actor失败

```rust
use actix::{Actor, Addr, Context, Supervised, SystemService};

// 实现可监督的Actor
impl Supervised for WorkerActor {
    fn restarting(&mut self, _: &mut Context<Self>) {
        println!("Worker {} is restarting", self.worker_id);
        self.processed_count = 0;
    }
}

// 实现系统服务，使Actor可以自动重启
impl SystemService for WorkerActor {}
```

1. **分布式状态管理**：使用actors维护分布式系统的状态

Actor模型的优势在分布式系统中尤为明显：

- **隔离性**：Actors之间相互隔离，故障不会扩散
- **位置透明**：Actors的物理位置对通信是透明的
- **可伸缩性**：可以轻松横向扩展Actor系统
- **容错性**：通过监督策略处理故障

在Rust中，Actor模型结合语言的所有权系统，为构建安全、高效的分布式系统提供了强大基础。

### 2.4 类型系统对分布式编程的支持

Rust的类型系统是其最强大的特性之一，可以帮助捕获许多分布式系统中常见的错误。类型系统的这些特性对分布式编程提供了显著支持：

**类型系统在分布式系统中的应用**：

1. **状态编码与状态机**：

使用类型系统表示分布式节点的状态，确保状态转换安全：

```rust
// 使用类型系统表示节点状态
enum NodeState {
    Follower { 
        current_term: u64,
        voted_for: Option<NodeId>,
    },
    Candidate { 
        current_term: u64,
        votes_received: HashSet<NodeId>,
        election_deadline: Instant,
    },
    Leader { 
        current_term: u64,
        next_index: HashMap<NodeId, u64>,
        match_index: HashMap<NodeId, u64>,
        heartbeat_deadline: Instant,
    },
}

struct ConsensusNode {
    id: NodeId,
    state: NodeState,
    log: Vec<LogEntry>,
    peers: HashSet<NodeId>,
}

impl ConsensusNode {
    // 类型安全的状态转换
    fn become_candidate(&mut self) -> Result<(), StateError> {
        match &self.state {
            NodeState::Follower { current_term, .. } => {
                let new_term = current_term + 1;
                let mut votes = HashSet::new();
                // 给自己投票
                votes.insert(self.id.clone());
                
                // 更新状态为候选人
                self.state = NodeState::Candidate {
                    current_term: new_term,
                    votes_received: votes,
                    election_deadline: Instant::now() + ELECTION_TIMEOUT,
                };
                
                // 向所有节点请求投票
                self.request_votes();
                Ok(())
            },
            NodeState::Candidate { .. } => {
                // 已经是候选人，重新开始选举
                self.restart_election();
                Ok(())
            },
            NodeState::Leader { .. } => {
                Err(StateError::InvalidTransition("Leader cannot become candidate".into()))
            }
        }
    }
    
    fn become_leader(&mut self) -> Result<(), StateError> {
        if let NodeState::Candidate { current_term, votes_received, .. } = &self.state {
            // 检查是否获得多数票
            if votes_received.len() * 2 > self.peers.len() + 1 {
                // 初始化leader状态
                let mut next_index = HashMap::new();
                let mut match_index = HashMap::new();
                
                for peer in &self.peers {
                    next_index.insert(peer.clone(), self.log.len() as u64 + 1);
                    match_index.insert(peer.clone(), 0);
                }
                
                self.state = NodeState::Leader {
                    current_term: *current_term,
                    next_index,
                    match_index,
                    heartbeat_deadline: Instant::now() + HEARTBEAT_INTERVAL,
                };
                
                // 发送初始心跳
                self.send_heartbeats();
                Ok(())
            } else {
                Err(StateError::InsufficientVotes)
            }
        } else {
            Err(StateError::InvalidTransition("Only candidate can become leader".into()))
        }
    }
}
```

1. **会话类型**：使用类型编码通信协议，确保消息交换遵循预定义序列：

```rust
use std::marker::PhantomData;

// 协议状态标记
struct Init;
struct Authenticated;
struct Ready;
struct Closed;

// 类型化会话
struct Session<S> {
    connection: TcpStream,
    state: PhantomData<S>,
}

impl Session<Init> {
    fn new(connection: TcpStream) -> Self {
        Session {
            connection,
            state: PhantomData,
        }
    }
    
    // 只有初始状态可以进行认证
    fn authenticate(self, credentials: Credentials) -> Result<Session<Authenticated>, AuthError> {
        // 发送认证请求
        self.connection.write_all(&serialize_auth_request(credentials))?;
        
        // 读取响应
        let response = read_response(&self.connection)?;
        
        if response.is_success() {
            // 转换到已认证状态
            Ok(Session {
                connection: self.connection,
                state: PhantomData,
            })
        } else {
            Err(AuthError::Failed(response.error_message()))
        }
    }
}

impl Session<Authenticated> {
    // 只有已认证状态可以准备会话
    fn prepare(self) -> Result<Session<Ready>, SessionError> {
        // 发送准备请求
        self.connection.write_all(&serialize_prepare_request())?;
        
        // 读取响应
        let response = read_response(&self.connection)?;
        
        if response.is_success() {
            // 转换到就绪状态
            Ok(Session {
                connection: self.connection,
                state: PhantomData,
            })
        } else {
            Err(SessionError::PreparationFailed(response.error_message()))
        }
    }
}

impl Session<Ready> {
    // 只有就绪状态可以发送命令
    fn send_command(&mut self, command: Command) -> Result<Response, CommandError> {
        // 发送命令
        self.connection.write_all(&serialize_command(command))?;
        
        // 读取响应
        let response = read_response(&self.connection)?;
        Ok(response)
    }
    
    // 只有就绪状态可以关闭会话
    fn close(self) -> Result<Session<Closed>, CloseError> {
        // 发送关闭请求
        self.connection.write_all(&serialize_close_request())?;
        
        // 读取响应
        let response = read_response(&self.connection)?;
        
        if response.is_success() {
            // 转换到关闭状态
            Ok(Session {
                connection: self.connection,
                state: PhantomData,
            })
        } else {
            Err(CloseError::FailedToClose(response.error_message()))
        }
    }
}

// 使用示例
fn main() -> Result<(), Box<dyn Error>> {
    let connection = TcpStream::connect("127.0.0.1:8080")?;
    
    // 创建初始会话
    let session = Session::<Init>::new(connection);
    
    // 认证
    let authenticated_session = session.authenticate(Credentials {
        username: "user".to_string(),
        password: "pass".to_string(),
    })?;
    
    // 准备会话
    let mut ready_session = authenticated_session.prepare()?;
    
    // 发送命令
    let response = ready_session.send_command(Command::Get { key: "foo".to_string() })?;
    println!("Response: {:?}", response);
    
    // 关闭会话
    let closed_session = ready_session.close()?;
    
    Ok(())
}
```

1. **类型级别编程**：使用泛型和类型特征实现更高级别的抽象：

```rust
// 使用类型级编程实现分布式一致性保证
trait ConsistencyLevel {
    fn min_replicas() -> usize;
    fn check_success(total: usize, successful: usize) -> bool;
}

// 强一致性
struct StrongConsistency;
impl ConsistencyLevel for StrongConsistency {
    fn min_replicas() -> usize { 3 }
    fn check_success(total: usize, successful: usize) -> bool {
        successful > total / 2  // 多数写入成功
    }
}

// 读写仲裁一致性
struct QuorumConsistency;
impl ConsistencyLevel for QuorumConsistency {
    fn min_replicas() -> usize { 2 }
    fn check_success(total: usize, successful: usize) -> bool {
        successful >= (total / 2) + 1  // 至少一半以上成功
    }
}

// 最终一致性
struct EventualConsistency;
impl ConsistencyLevel for EventualConsistency {
    fn min_replicas() -> usize { 1 }
    fn check_success(_total: usize, successful: usize) -> bool {
        successful >= 1  // 至少有一个成功
    }
}

// 分布式键值存储
struct DistributedKVStore<C: ConsistencyLevel> {
    nodes: Vec<NodeClient>,
    _consistency: PhantomData<C>,
}

impl<C: ConsistencyLevel> DistributedKVStore<C> {
    fn new(nodes: Vec<NodeClient>) -> Result<Self, StoreError> {
        if nodes.len() < C::min_replicas() {
            return Err(StoreError::InsufficientReplicas {
                required: C::min_replicas(),
                available: nodes.len(),
            });
        }
        
        Ok(Self {
            nodes,
            _consistency: PhantomData,
        })
    }
    
    async fn put(&self, key: String, value: Vec<u8>) -> Result<(), StoreError> {
        let mut successful = 0;
        let total = self.nodes.len();
        
        let futures: Vec<_> = self.nodes.iter()
            .map(|node| node.put(key.clone(), value.clone()))
            .collect();
        
        let results = futures::future::join_all(futures).await;
        
        for result in results {
            if result.is_ok() {
                successful += 1;
            }
        }
        
        if C::check_success(total, successful) {
            Ok(())
        } else {
            Err(StoreError::WriteFailed {
                successful,
                required: format!("{} consistency", std::any::type_name::<C>()),
            })
        }
    }
    
    async fn get(&self, key: String) -> Result<Option<Vec<u8>>, StoreError> {
        // 类似实现...
        todo!()
    }
}

// 使用不同一致性级别
async fn consistency_examples() -> Result<(), Box<dyn Error>> {
    // 强一致性存储
    let strong_store = DistributedKVStore::<StrongConsistency>::new(
        vec![client1.clone(), client2.clone(), client3.clone()]
    )?;
    
    // 仲裁一致性存储
    let quorum_store = DistributedKVStore::<QuorumConsistency>::new(
        vec![client1.clone(), client2.clone()]
    )?;
    
    // 最终一致性存储
    let eventual_store = DistributedKVStore::<EventualConsistency>::new(
        vec![client1.clone()]
    )?;
    
    // 使用强一致性写入关键数据
    strong_store.put("critical_data".to_string(), b"value".to_vec()).await?;
    
    // 使用仲裁一致性写入重要但非关键数据
    quorum_store.put("important_data".to_string(), b"value".to_vec()).await?;
    
    // 使用最终一致性写入非关键数据
    eventual_store.put("non_critical_data".to_string(), b"value".to_vec()).await?;
    
    Ok(())
}
```

1. **类型安全的序列化与反序列化**：

```rust
use serde::{Serialize, Deserialize};

// 使用类型系统保证序列化安全
#[derive(Serialize, Deserialize, Debug)]
struct NodeMessage<T> {
    source_id: String,
    target_id: String,
    message_id: u64,
    payload: T,
}

#[derive(Serialize, Deserialize, Debug)]
enum ConsensusPayload {
    VoteRequest {
        term: u64,
        last_log_index: u64,
        last_log_term: u64,
    },
    VoteResponse {
        term: u64,
        vote_granted: bool,
    },
    AppendEntries {
        term: u64,
        prev_log_index: u64,
        prev_log_term: u64,
        entries: Vec<LogEntry>,
        leader_commit: u64,
    },
    AppendEntriesResponse {
        term: u64,
        success: bool,
        match_index: Option<u64>,
    },
}

#[derive(Serialize, Deserialize, Debug, Clone)]
struct LogEntry {
    term: u64,
    index: u64,
    data: Vec<u8>,
}

impl<T: Serialize> NodeMessage<T> {
    fn new(source_id: String, target_id: String, message_id: u64, payload: T) -> Self {
        Self {
            source_id,
            target_id,
            message_id,
            payload,
        }
    }
    
    fn serialize(&self) -> Result<Vec<u8>, SerializeError> {
        bincode::serialize(self).map_err(|e| SerializeError::EncodingFailed(e.to_string()))
    }
}

impl<T: DeserializeOwned> NodeMessage<T> {
    fn deserialize(data: &[u8]) -> Result<Self, SerializeError> {
        bincode::deserialize(data).map_err(|e| SerializeError::DecodingFailed(e.to_string()))
    }
}

// 使用示例
fn send_vote_request(network: &mut Network, source: &str, target: &str, term: u64)
    -> Result<(), NetworkError> 
{
    let payload = ConsensusPayload::VoteRequest {
        term,
        last_log_index: 100,
        last_log_term: 5,
    };
    
    let message = NodeMessage::new(
        source.to_string(),
        target.to_string(),
        generate_message_id(),
        payload
    );
    
    let data = message.serialize()?;
    network.send(target, data)?;
    
    Ok(())
}

fn handle_message(data: &[u8]) -> Result<(), MessageError> {
    // 类型安全地反序列化消息
    let message = NodeMessage::<ConsensusPayload>::deserialize(data)?;
    
    // 根据消息类型处理
    match message.payload {
        ConsensusPayload::VoteRequest { term, last_log_index, last_log_term } => {
            println!(
                "Received vote request from {}: term={}, last_index={}, last_term={}",
                message.source_id, term, last_log_index, last_log_term
            );
            // 处理投票请求...
        },
        ConsensusPayload::AppendEntries { term, entries, .. } => {
            println!(
                "Received {} entries from {} at term {}",
                entries.len(), message.source_id, term
            );
            // 处理日志条目...
        },
        // 处理其他消息类型...
        _ => println!("Received other message type from {}", message.source_id),
    }
    
    Ok(())
}
```

Rust的类型系统通过捕获各种潜在错误，显著提高了分布式系统的可靠性：

- **类型不匹配**：防止不兼容消息类型的序列化/反序列化
- **状态错误**：确保只能在正确的状态下执行特定操作
- **协议违反**：捕获违反通信协议的操作
- **资源管理**：通过所有权确保资源的正确管理

这种类型级别的安全性使得许多常见的分布式系统错误可以在编译时被发现，而不是在生产环境中出现。

### 2.5 错误处理与分布式系统的容错性

在分布式系统中，错误不是例外而是常态。Rust的错误处理机制非常适合分布式系统的需求，它强制开发者明确处理各种错误情况。

**Rust错误处理的核心特点**：

1. **两种错误类型**：
   - `Result<T, E>`：用于可恢复的错误
   - `panic!`：用于不可恢复的错误

2. **错误传播**：
   - `?` 操作符简化错误传播
   - 链式错误提供详细的错误上下文

3. **自定义错误类型**：
   - 细粒度的错误分类
   - 使用 `thiserror` 和 `anyhow` 简化错误处理

**分布式系统中的错误类型和处理策略**：

```rust
use thiserror::Error;
use std::time::Duration;

// 分布式系统中的错误类别
#[derive(Error, Debug)]
enum DistributedError {
    #[error("网络错误: {0}")]
    Network(#[from] NetworkError),
    
    #[error("节点错误: {0}")]
    Node(#[from] NodeError),
    
    #[error("共识错误: {0}")]
    Consensus(#[from] ConsensusError),
    
    #[error("存储错误: {0}")]
    Storage(#[from] StorageError),
    
    #[error("超时错误: 操作 {operation} 在 {timeout:?} 后超时")]
    Timeout { operation: String, timeout: Duration },
    
    #[error("不一致状态: {0}")]
    InconsistentState(String),
    
    #[error("集群配置错误: {0}")]
    ClusterConfig(String),
}

#[derive(Error, Debug)]
enum NetworkError {
    #[error("连接失败: {0}")]
    ConnectionFailed(String),
    
    #[error("连接断开: {0}")]
    Disconnected(String),
    
    #[error("消息发送失败: {0}")]
    SendFailed(String),
    
    #[error("消息接收失败: {0}")]
    ReceiveFailed(String),
}

#[derive(Error, Debug)]
enum ConsensusError {
    #[error("选举失败: {0}")]
    ElectionFailed(String),
    
    #[error("日志复制失败: {0}")]
    ReplicationFailed(String),
    
    #[error("提交失败: {0}")]
    CommitFailed(String),
    
    #[error("任期冲突: 当前={current}, 收到={received}")]
    TermConflict { current: u64, received: u64 },
}

// 分布式节点的错误处理
struct DistributedNode {
    id: String,
    peers: Vec<PeerConnection>,
    storage: Box<dyn Storage>,
    // 其他字段...
}

impl DistributedNode {
    // 发送消息给所有节点，带有重试逻辑
    async fn broadcast_with_retry<T: Serialize>(
        &self,
        message: &T,
        max_retries: usize,
        retry_delay: Duration
    ) -> Result<Vec<NodeId>, DistributedError> {
        let mut successful = Vec::new();
        let mut failed = Vec::new();
        
        // 首次广播尝试
        for peer in &self.peers {
            match peer.send(message).await {
                Ok(_) => successful.push(peer.id.clone()),
                Err(err) => {
                    log::warn!("Failed to send to {}: {}", peer.id, err);
                    failed.push((peer, err));
                }
            }
        }
        
        // 对失败的节点进行重试
        for retry in 1..=max_retries {
            if failed.is_empty() {
                break;
            }
            
            // 等待重试延迟
            tokio::time::sleep(retry_delay).await;
            
            let mut still_failed = Vec::new();
            
            for (peer, prev_err) in failed {
                log::info!("Retry {}/{} sending to {}", retry, max_retries, peer.id);
                
                match peer.send(message).await {
                    Ok(_) => successful.push(peer.id.clone()),
                    Err(err) => {
                        log::warn!("Still failed to send to {}: {}", peer.id, err);
                        still_failed.push((peer, err));
                    }
                }
            }
            
            failed = still_failed;
        }
        
        // 记录持续失败的节点
        for (peer, err) in &failed {
            log::error!(
                "Permanently failed to send to {} after {} retries: {}",
                peer.id, max_retries, err
            );
        }
        
        // 返回成功发送的节点列表
        Ok(successful)
    }
    
    // 处理共识消息，展示不同类型错误的处理
    async fn handle_consensus_message(
        &mut self,
        message: ConsensusMessage
    ) -> Result<(), DistributedError> {
        match message {
            ConsensusMessage::AppendEntries { term, entries, .. } => {
                // 验证任期
                if term < self.current_term() {
                    return Err(ConsensusError::TermConflict {
                        current: self.current_term(),
                        received: term,
                    }.into());
                }
                
                // 尝试将日志条目写入存储
                for entry in entries {
                    self.storage.append_log(entry.clone()).await
                        .map_err(|e| {
                            // 增加详细上下文
                            log::error!("Failed to append log entry: {}", e);
                            DistributedError::Storage(StorageError::WriteError(
                                format!("Failed to append entry at index {}: {}", entry.index, e)
                            ))
                        })?;
                }
                
                // 更新提交索引
                self.update_commit_index(leader_commit)
                    .map_err(|e| {
                        log::warn!("Failed to update commit index: {}", e);
                        DistributedError::from(e)
                    })?;
                
                Ok(())
            },
            
            ConsensusMessage::RequestVote { term, candidate_id, .. } => {
                // 处理投票请求...
                
                // 使用超时错误
                let vote_result = tokio::time::timeout(
                    Duration::from_millis(500),
                    self.process_vote_request(term, candidate_id)
                ).await
                    .map_err(|_| DistributedError::Timeout {
                        operation: "process_vote_request".to_string(),
                        timeout: Duration::from_millis(500),
                    })?;
                
                // 处理投票结果...
                
                Ok(())
            },
            
            // 处理其他消息类型...
            _ => Ok(()),
        }
    }
    
    // 容错策略 - 断路器模式
    async fn with_circuit_breaker<F, T, E>(
        &self,
        operation: &str,
        f: F,
        max_failures: usize,
        reset_timeout: Duration
    ) -> Result<T, DistributedError>
    where
        F: Fn() -> Future<Output = Result<T, E>>,
        E: Into<DistributedError>,
    {
        // 断路器状态检查
        if !self.circuit_breaker.can_execute(operation) {
            return Err(DistributedError::Network(
                NetworkError::ConnectionFailed(
                    format!("Circuit breaker open for {}", operation)
                )
            ));
        }
        
        // 尝试执行操作
        match f().await {
            Ok(result) => {
                // 成功后重置断路器
                self.circuit_breaker.record_success(operation);
                Ok(result)
            },
            Err(e) => {
                // 记录失败
                let is_open = self.circuit_breaker.record_failure(
                    operation, max_failures, reset_timeout
                );
                
                if is_open {
                    log::warn!("Circuit breaker opened for {}", operation);
                }
                
                Err(e.into())
            }
        }
    }
}
```

**分布式系统中的容错策略**：

1. **重试机制**：

```rust
async fn with_retry<F, Fut, T, E>(
    operation: F,
    max_retries: usize,
    backoff: ExponentialBackoff
) -> Result<T, E>
where
    F: Fn() -> Fut,
    Fut: Future<Output = Result<T, E>>,
    E: std::fmt::Display,
{
    let mut retries = 0;
    let mut delay = backoff.initial_interval;
    
    loop {
        match operation().await {
            Ok(result) => return Ok(result),
            Err(e) => {
                retries += 1;
                if retries > max_retries {
                    return Err(e);
                }
                
                log::warn!(
                    "Operation failed (attempt {}/{}), retrying in {:?}: {}",
                    retries, max_retries, delay, e
                );
                
                tokio::time::sleep(delay).await;
                
                // 指数退避
                delay = std::cmp::min(
                    delay * backoff.multiplier,
                    backoff.max_interval
                );
                
                // 添加随机抖动以避免雷鸣群效应
                if backoff.randomization_factor > 0.0 {
                    let delta = backoff.randomization_factor * delay.as_secs_f64();
                    let jitter = rand::random::<f64>() * delta * 2.0 - delta;
                    delay = Duration::from_secs_f64(
                        (delay.as_secs_f64() + jitter).max(0.0)
                    );
                }
            }
        }
    }
}
```

1. **断路器模式**：

```rust
struct CircuitBreaker {
    failure_counts: DashMap<String, usize>,
    open_circuits: DashMap<String, Instant>,
}

impl CircuitBreaker {
    fn new() -> Self {
        Self {
            failure_counts: DashMap::new(),
            open_circuits: DashMap::new(),
        }
    }
    
    fn can_execute(&self, operation: &str) -> bool {
        if let Some(opened_at) = self.open_circuits.get(operation) {
            // 检查断路器是否可以重置
            if opened_at.elapsed() >= self.reset_timeout {
                // 允许一次尝试
                self.open_circuits.remove(operation);
                return true;
            }
            return false;
        }
        true
    }
    
    fn record_success(&self, operation: &str) {
        self.failure_counts.remove(operation);
        self.open_circuits.remove(operation);
    }
    
    fn record_failure(
        &self,
        operation: &str,
        threshold: usize,
        reset_timeout: Duration
    ) -> bool {
        let count = self.failure_counts
            .entry(operation.to_string())
            .or_insert(0);
            
        *count += 1;
        
        if *count >= threshold {
            self.open_circuits.insert(operation.to_string(), Instant::now());
            return true;
        }
        
        false
    }
}
```

1. **超时控制**：

```rust
async fn with_timeout<F, T, E>(
    operation: F,
    timeout: Duration,
    operation_name: &str
) -> Result<T, DistributedError>
where
    F: Future<Output = Result<T, E>>,
    E: Into<DistributedError>,
{
    match tokio::time::timeout(timeout, operation).await {
        Ok(result) => result.map_err(|e| e.into()),
        Err(_) => Err(DistributedError::Timeout {
            operation: operation_name.to_string(),
            timeout,
        }),
    }
}

// 使用示例
async fn fetch_data_with_timeout(client: &Client, key: &str) -> Result<Vec<u8>, DistributedError> {
    with_timeout(
        client.fetch(key),
        Duration::from_secs(5),
        &format!("fetch_data:{}", key)
    ).await
}
```

1. **降级策略**：

```rust
enum FallbackStrategy<T> {
    // 返回缓存结果
    CachedValue(T),
    // 返回默认值
    DefaultValue(T),
    // 重定向到备用服务
    Redirect(ServiceEndpoint),
}

async fn with_fallback<F, T, E>(
    operation: F,
    fallback: FallbackStrategy<T>,
    metrics: &Metrics
) -> Result<T, E>
where
    F: Future<Output = Result<T, E>>,
{
    match operation.await {
        Ok(result) => Ok(result),
        Err(err) => {
            // 记录降级指标
            metrics.increment("fallback_activations");
            
            // 根据降级策略返回结果
            match fallback {
                FallbackStrategy::CachedValue(cached) => {
                    log::warn!("Using cached value due to error: {}", err);
                    metrics.increment("fallback_cached_used");
                    Ok(cached)
                },
                FallbackStrategy::DefaultValue(default) => {
                    log::warn!("Using default value due to error: {}", err);
                    metrics.increment("fallback_default_used");
                    Ok(default)
                },
                FallbackStrategy::Redirect(endpoint) => {
                    log::warn!("Redirecting to backup service due to error: {}", err);
                    metrics.increment("fallback_redirect_used");
                    // 实际重定向逻辑...
                    todo!()
                }
            }
        }
    }
}
```

1. **舱壁模式**：

```rust
struct Bulkhead {
    name: String,
    semaphore: Arc<Semaphore>,
    metrics: Arc<Metrics>,
}

impl Bulkhead {
    fn new(name: String, max_concurrent: usize, metrics: Arc<Metrics>) -> Self {
        Self {
            name: name.clone(),
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
            metrics,
        }
    }
    
    async fn execute<F, T, E>(&self, operation: F) -> Result<T, BulkheadError<E>>
    where
        F: Future<Output = Result<T, E>>,
    {
        // 尝试获取许可
        let permit = match self.semaphore.try_acquire() {
            Ok(permit) => permit,
            Err(_) => {
                self.metrics.increment(&format!("{}.rejected", self.name));
                return Err(BulkheadError::TooManyConcurrentCalls);
            }
        };
        
        self.metrics.increment(&format!("{}.active", self.name));
        
        // 执行操作并确保释放许可
        let start = Instant::now();
        let result = operation.await;
        let duration = start.elapsed();
        
        self.metrics.record(&format!("{}.duration", self.name), duration);
        self.metrics.decrement(&format!("{}.active", self.name));
        
        // 许可在这里被丢弃，自动释放
        drop(permit);
        
        // 返回结果或转换错误
        result.map_err(BulkheadError::OperationFailed)
    }
}

enum BulkheadError<E> {
    TooManyConcurrentCalls,
    OperationFailed(E),
}
```

这些容错策略可以组合使用，创建一个健壮的错误处理系统：

```rust
async fn resilient_operation<T, E>(
    operation_name: &str,
    operation: impl Fn() -> impl Future<Output = Result<T, E>>,
    circuit_breaker: &CircuitBreaker,
    bulkhead: &Bulkhead,
    retry_config: RetryConfig,
    timeout: Duration,
    fallback: Option<FallbackStrategy<T>>,
    metrics: &Metrics,
) -> Result<T, DistributedError>
where
    E: Into<DistributedError> + std::fmt::Display,
    T: Clone,
{
    // 断路器检查
    if !circuit_breaker.can_execute(operation_name) {
        return Err(DistributedError::ServiceUnavailable(
            format!("Circuit broken for {}", operation_name)
        ));
    }
    
    // 舱壁保护
    let bulkhead_protected = bulkhead.execute(
        async {
            // 超时保护
            let timeout_protected = with_timeout(
                // 重试机制
                with_retry(
                    || operation(),
                    retry_config.max_retries,
                    retry_config.backoff.clone()
                ),
                timeout,
                operation_name
            ).await;
            
            // 记录结果
            match &timeout_protected {
                Ok(_) => {
                    metrics.increment(&format!("{}.success", operation_name));
                    circuit_breaker.record_success(operation_name);
                },
                Err(e) => {
                    metrics.increment(&format!("{}.failure", operation_name));
                    circuit_breaker.record_failure(
                        operation_name,
                        retry_config.circuit_break_threshold,
                        retry_config.circuit_reset_timeout
                    );
                    log::error!("Operation {} failed: {}", operation_name, e);
                }
            }
            
            timeout_protected
        }
    ).await;
    
    // 处理舱壁错误
    let operation_result = match bulkhead_protected {
        Ok(result) => result,
        Err(BulkheadError::TooManyConcurrentCalls) => {
            return Err(DistributedError::ResourceExhausted(
                format!("Too many concurrent calls to {}", operation_name)
            ));
        },
        Err(BulkheadError::OperationFailed(e)) => e,
    };
    
    // 应用降级策略
    if let Some(fallback_strategy) = fallback {
        match operation_result {
            Ok(result) => Ok(result),
            Err(err) => {
                // 使用降级策略
                Ok(match fallback_strategy {
                    FallbackStrategy::CachedValue(cached) => {
                        log::warn!("Using cached value for {} due to error: {:?}", operation_name, err);
                        metrics.increment(&format!("{}.fallback.cache", operation_name));
                        cached
                    },
                    FallbackStrategy::DefaultValue(default) => {
                        log::warn!("Using default value for {} due to error: {:?}", operation_name, err);
                        metrics.increment(&format!("{}.fallback.default", operation_name));
                        default
                    },
                    // 其他降级策略...
                    _ => return Err(err),
                })
            }
        }
    } else {
        operation_result
    }
}
```

使用合适的错误处理和容错策略，Rust可以构建出极其健壮的分布式系统，即使在面对各种故障和错误情况时仍能保持可用性和数据一致性。

## 3. 分布式系统设计模式

### 3.1 消息传递模式

消息传递是分布式系统中节点间通信的基础。Rust强大的类型系统和所有权模型让消息传递更加安全和高效。

**常见的消息传递模式**：

1. **请求-响应**：

```rust
use tokio::sync::oneshot;

// 请求-响应模式
struct RequestResponsePattern {
    client: Client,
}

impl RequestResponsePattern {
    async fn send_request<Req, Resp>(&self, request: Req, target: NodeId) -> Result<Resp, RequestError>
    where
        Req: Serialize + Send + 'static,
        Resp: DeserializeOwned + Send + 'static,
    {
        // 创建一次性通道接收响应
        let (sender, receiver) = oneshot::channel();
        
        // 生成请求ID
        let request_id = generate_request_id();
        
        // 注册响应处理器
        self.client.register_response_handler(request_id, sender);
        
        // 发送请求
        self.client.send_message(
            target,
            Message {
                id: request_id,
                payload: request,
                message_type: MessageType::Request,
            }
        ).await?;
        
        // 等待响应或超时
        match tokio::time::timeout(Duration::from_secs(10), receiver).await {
            Ok(Ok(response)) => Ok(response),
            Ok(Err(_)) => Err(RequestError::ResponseChannelClosed),
            Err(_) => Err(RequestError::Timeout),
        }
    }
    
    async fn handle_request<Req, Resp, F>(&self, handler: F)
    where
        F: Fn(Req) -> Resp + Send + Sync + 'static,
        Req: DeserializeOwned + Send + 'static,
        Resp: Serialize + Send + 'static,
    {
        self.client.set_request_handler(move |request_id, request: Req| {
            // 处理请求
            let response = handler(request);
            
            // 发送响应
            self.client.send_message(
                request.source,
                Message {
                    id: request_id,
                    payload: response,
                    message_type: MessageType::Response,
                }
            );
        });
    }
}
```

1. **发布-订阅**：

```rust
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::{mpsc, RwLock};

// 主题消息
struct TopicMessage<T> {
    topic: String,
    payload: T,
    timestamp: chrono::DateTime<chrono::Utc>,
}

// 发布-订阅系统
struct PubSubSystem<T: Clone + Send + 'static> {
    topics: Arc<RwLock<HashMap<String, Vec<mpsc::Sender<TopicMessage<T>>>>>>,
}

impl<T: Clone + Send + 'static> PubSubSystem<T> {
    fn new() -> Self {
        Self {
            topics: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    // 发布消息到主题
    async fn publish(&self, topic: &str, message: T) -> Result<(), PubSubError> {
        let topics = self.topics.read().await;
        
        if let Some(subscribers) = topics.get(topic) {
            let topic_message = TopicMessage {
                topic: topic.to_string(),
                payload: message,
                timestamp: chrono::Utc::now(),
            };
            
            // 向所有订阅者发送消息
            for subscriber in subscribers {
                if let Err(_) = subscriber.send(topic_message.clone()).await {
                    // 订阅者可能已经断开，忽略错误
                    continue;
                }
            }
        }
        
        Ok(())
    }
    
    // 订阅主题
    async fn subscribe(&self, topic: &str) -> mpsc::Receiver<TopicMessage<T>> {
        let (tx, rx) = mpsc::channel(100);
        
        let mut topics = self.topics.write().await;
        
        topics.entry(topic.to_string())
            .or_insert_with(Vec::new)
            .push(tx);
            
        rx
    }
    
    // 取消订阅（通过丢弃接收者实现）
    async fn cleanup_dead_subscribers(&self) {
        let mut topics = self.topics.write().await;
        
        // 清理已关闭的发送者
        for subscribers in topics.values_mut() {
            subscribers.retain(|sender| !sender.is_closed());
        }
        
        // 移除没有订阅者的主题
        topics.retain(|_, subscribers| !subscribers.is_empty());
    }
}

// 使用示例
async fn pubsub_example() {
    let pubsub = PubSubSystem::<String>::new();
    
    // 订阅主题
    let mut rx1 = pubsub.subscribe("notifications").await;
    let mut rx2 = pubsub.subscribe("notifications").await;
    
    // 发布消息
    tokio::spawn(async move {
        loop {
            pubsub.publish("notifications", "Hello subscribers!".to_string()).await.unwrap();
            tokio::time::sleep(Duration::from_secs(1)).await;
        }
    });
    
    // 处理接收到的消息
    tokio::spawn(async move {
        while let Some(message) = rx1.recv().await {
            println!("Subscriber 1 received: {}", message.payload);
        }
    });
    
    tokio::spawn(async move {
        while let Some(message) = rx2.recv().await {
            println!("Subscriber 2 received: {}", message.payload);
        }
    });
    
    // 定期清理死亡订阅者
    tokio::spawn(async move {
        loop {
            tokio::time::sleep(Duration::from_secs(60)).await;
            pubsub.cleanup_dead_subscribers().await;
        }
    });
}
```

1. **流处理模式**：

```rust
use tokio_stream::{Stream, StreamExt};
use futures::stream::StreamExt as FuturesStreamExt;

// 数据流处理
struct StreamProcessor<T> {
    name: String,
    processing_fn: Box<dyn Fn(T) -> Result<T, ProcessingError> + Send + Sync>,
}

impl<T: Clone + Send + Sync + 'static> StreamProcessor<T> {
    fn new<F>(name: String, processing_fn: F) -> Self
    where
        F: Fn(T) -> Result<T, ProcessingError> + Send + Sync + 'static,
    {
        Self {
            name,
            processing_fn: Box::new(processing_fn),
        }
    }
    
    // 处理流
    async fn process<S>(&self, input_stream: S) -> impl Stream<Item = Result<T, ProcessingError>>
    where
        S: Stream<Item = T>,
    {
        let processor_name = self.name.clone();
        let processing_fn = self.processing_fn.clone();
        
        input_stream
            .map(move |item| {
                let result = (processing_fn)(item.clone());
                
                match &result {
                    Ok(_) => {
                        log::debug!("Processor {} successfully processed item", processor_name);
                    },
                    Err(e) => {
                        log::error!("Processor {} failed to process item: {}", processor_name, e);
                    }
                }
                
                result
            })
    }
}

// 流处理管道
struct StreamPipeline<T> {
    processors: Vec<StreamProcessor<T>>,
}

impl<T: Clone + Send + Sync + 'static> StreamPipeline<T> {
    fn new() -> Self {
        Self {
            processors: Vec::new(),
        }
    }
    
    // 添加处理器
    fn add_processor<F>(&mut self, name: &str, processing_fn: F) -> &mut Self
    where
        F: Fn(T) -> Result<T, ProcessingError> + Send + Sync + 'static,
    {
        self.processors.push(
            StreamProcessor::new(name.to_string(), processing_fn)
        );
        self
    }
    
    // 执行管道
    async fn execute<S>(&self, input_stream: S) -> impl Stream<Item = Result<T, PipelineError>>
    where
        S: Stream<Item = T>,
    {
        let mut current_stream = Box::pin(input_stream.map(Ok));
        
        // 串联所有处理器
        for processor in &self.processors {
            let processor_name = processor.name.clone();
            
            current_stream = Box::pin(
                current_stream
                    .filter_map(|result| async move {
                        match result {
                            Ok(item) => Some(item),
                            Err(e) => {
                                log::error!("Item dropped before reaching processor {}: {}", processor_name, e);
                                None
                            }
                        }
                    })
                    .map(Ok)
                    .forward(processor.process())
                    .map_err(|e| PipelineError::ProcessorError {
                        processor: processor_name,
                        error: e.to_string(),
                    })
            );
        }
        
        current_stream
    }
}

// 使用示例
async fn stream_processing_example() {
    // 创建流处理管道
    let mut pipeline = StreamPipeline::new();
    
    // 添加处理器
    pipeline
        .add_processor("validate", |data: EventData| {
            // 验证数据
            if data.timestamp <= 0 {
                return Err(ProcessingError::ValidationFailed("Invalid timestamp".into()));
            }
            Ok(data)
        })
        .add_processor("enrich", |mut data: EventData| {
            // 丰富数据
            data.enriched = true;
            data.processing_time = chrono::Utc::now().timestamp();
            Ok(data)
        })
        .add_processor("transform", |mut data: EventData| {
            // 转换数据
            data.value *= 2.0;
            Ok(data)
        });
    
    // 创建输入流
    let input_data = vec![
        EventData { id: 1, value: 10.0, timestamp: 1626100000, enriched: false, processing_time: 0 },
        EventData { id: 2, value: 20.0, timestamp: 1626200000, enriched: false, processing_time: 0 },
        EventData { id: 3, value: 30.0, timestamp: 0, enriched: false, processing_time: 0 }, // 将被过滤
        EventData { id: 4, value: 40.0, timestamp: 1626400000, enriched: false, processing_time: 0 },
    ];
    
    let input_stream = tokio_stream::iter(input_data);
    
    // 执行管道
    let output_stream = pipeline.execute(input_stream).await;
    
    // 收集结果
    let results: Vec<_> = output_stream.collect().await;
    
    for result in results {
        match result {
            Ok(data) => println!("Processed: id={}, value={}, enriched={}", data.id, data.value, data.enriched),
            Err(e) => println!("Error: {}", e),
        }
    }
}
```

1. **命令查询责任分离（CQRS）**：

```rust
// 命令消息
enum Command {
    CreateProduct { id: String, name: String, price: f64 },
    UpdatePrice { id: String, new_price: f64 },
    DeleteProduct { id: String },
}

// 查询消息
enum Query {
    GetProduct { id: String },
    ListProducts { category: Option<String> },
    GetProductPrice { id: String },
}

// 命令处理器
struct CommandHandler {
    write_store: Arc<RwLock<WriteStore>>,
    event_publisher: EventPublisher,
}

impl CommandHandler {
    async fn handle(&self, command: Command) -> Result<(), CommandError> {
        match command {
            Command::CreateProduct { id, name, price } => {
                // 业务逻辑验证
                if price < 0.0 {
                    return Err(CommandError::ValidationFailed("Price must be positive".into()));
                }
                
                // 执行命令
                let mut store = self.write_store.write().await;
                if store.products.contains_key(&id) {
                    return Err(CommandError::DuplicateEntity(format!("Product {} already exists", id)));
                }
                
                // 更新写模型
                store.products.insert(id.clone(), Product {
                    id: id.clone(),
                    name: name.clone(),
                    price,
                    created_at: chrono::Utc::now(),
                    updated_at: chrono::Utc::now(),
                });
                
                // 发布事件
                self.event_publisher.publish(Event::ProductCreated {
                    id: id.clone(),
                    name,
                    price,
                    timestamp: chrono::Utc::now(),
                }).await?;
                
                Ok(())
            },
            // 其他命令处理...
            _ => todo!(),
        }
    }
}

// 查询处理器
struct QueryHandler {
    read_store: Arc<ReadStore>,
}

impl QueryHandler {
    async fn handle(&self, query: Query) -> Result<QueryResponse, QueryError> {
        match query {
            Query::GetProduct { id } => {
                if let Some(product) = self.read_store.products.get(&id) {
                    Ok(QueryResponse::Product(product.clone()))
                } else {
                    Err(QueryError::NotFound(format!("Product {} not found", id)))
                }
            },
            // 其他查询处理...
            _ => todo!(),
        }
    }
}

// 事件处理器（更新读模型）
struct EventHandler {
    read_store: Arc<RwLock<ReadStore>>,
}

impl EventHandler {
    async fn handle(&self, event: Event) -> Result<(), EventError> {
        match event {
            Event::ProductCreated { id, name, price, timestamp } => {
                let mut read_store = self.read_store.write().await;
                
                // 更新读模型
                read_store.products.insert(id.clone(), ProductReadModel {
                    id,
                    name,
                    price,
                    created_at: timestamp,
                });
                
                Ok(())
            },
            // 其他事件处理...
            _ => todo!(),
        }
    }
}

// CQRS服务
struct CqrsService {
    command_handler: Arc<CommandHandler>,
    query_handler: Arc<QueryHandler>,
    event_handler: Arc<EventHandler>,
}

impl CqrsService {
    // 处理命令
    async fn execute(&self, command: Command) -> Result<(), CommandError> {
        self.command_handler.handle(command).await
    }
    
    // 处理查询
    async fn query(&self, query: Query) -> Result<QueryResponse, QueryError> {
        self.query_handler.handle(query).await
    }
}
```

这些消息传递模式构成了分布式系统设计的基础。Rust的类型安全和并发模型使得实现这些模式更加健壮和高效。

### 3.2 状态复制与共识

在分布式系统中，为了保证高可用性和一致性，通常需要在多个节点之间复制状态。共识算法确保即使在出现故障的情况下，各节点也能对系统状态达成一致。

**状态复制的核心挑战**：

```rust
StateReplication = {
    一致性保证: "确保所有副本最终达到相同状态",
    顺序执行: "保证操作按相同顺序执行",
    失败处理: "处理节点故障和网络分区",
    冲突解决: "解决并发更新冲突",
    性能影响: "最小化复制对性能的影响"
}
```

**Rust中的状态机复制实现**：

```rust
// 可复制状态机
trait StateMachine: Clone + Send + Sync + 'static {
    type Command: Serialize + DeserializeOwned + Clone + Send + Sync;
    type Result: Serialize + DeserializeOwned + Clone + Send + Sync;
    
    // 应用命令到状态机
    fn apply(&mut self, command: &Self::Command) -> Self::Result;
    
    // 创建状态机快照
    fn create_snapshot(&self) -> Vec<u8>;
    
    // 从快照恢复状态机
    fn restore_from_snapshot(snapshot: &[u8]) -> Result<Self, RestoreError>;
}

// 复制日志条目
#[derive(Clone, Serialize, Deserialize)]
struct LogEntry<C> {
    term: u64,
    index: u64,
    command: Option<C>,
    // 条目类型（正常命令、配置变更等）
    entry_type: LogEntryType,
}

#[derive(Clone, Serialize, Deserialize)]
enum LogEntryType {
    Command,
    Configuration,
    NoOp,
}

// 复制日志
struct ReplicatedLog<C> {
    entries: Vec<LogEntry<C>>,
    commit_index: u64,
    last_applied: u64,
}

impl<C: Clone + Send + Sync + 'static> ReplicatedLog<C> {
    fn new() -> Self {
        Self {
            entries: vec![
                // 起始空条目（索引0）
                LogEntry {
                    term: 0,
                    index: 0,
                    command: None,
                    entry_type: LogEntryType::NoOp,
                }
            ],
            commit_index: 0,
            last_applied: 0,
        }
    }
    
    // 添加条目到日志
    fn append(&mut self, term: u64, command: Option<C>, entry_type: LogEntryType) -> u64 {
        let index = self.entries.len() as u64;
        
        self.entries.push(LogEntry {
            term,
            index,
            command,
            entry_type,
        });
        
        index
    }
    
    // 获取指定索引的条目
    fn get(&self, index: u64) -> Option<&LogEntry<C>> {
        if index < self.entries.len() as u64 {
            Some(&self.entries[index as usize])
        } else {
            None
        }
    }
    
    // 截断日志（删除给定索引及之后的所有条目）
    fn truncate(&mut self, index: u64) {
        if index < self.entries.len() as u64 {
            self.entries.truncate((index + 1) as usize);
        }
    }
    
    // 更新提交索引
    fn update_commit_index(&mut self, index: u64) {
        if index > self.commit_index {
            self.commit_index = index;
        }
    }
    
    // 获取未应用的已提交条目
    fn get_unapplied_entries(&self) -> Vec<&LogEntry<C>> {
        self.entries
            .iter()
            .skip((self.last_applied + 1) as usize)
            .take((self.commit_index - self.last_applied) as usize)
            .collect()
    }
    
    // 更新上次应用索引
    fn update_last_applied(&mut self, index: u64) {
        if index > self.last_applied {
            self.last_applied = index;
        }
    }
}

// 基于Raft的状态机复制实现
struct RaftNode<S: StateMachine> {
    id: NodeId,
    state: Arc<RwLock<NodeState>>,
    log: Arc<RwLock<ReplicatedLog<S::Command>>>,
    state_machine: Arc<RwLock<S>>,
    peers: HashMap<NodeId, PeerClient>,
    // 其他Raft状态...
}

impl<S: StateMachine> RaftNode<S> {
    // 客户端命令入口
    async fn submit_command(&self, command: S::Command) -> Result<S::Result, CommandError> {
        // 只有领导者可以接受命令
        let is_leader = {
            let state = self.state.read().await;
            matches!(state.role, NodeRole::Leader { .. })
        };
        
        if !is_leader {
            return Err(CommandError::NotLeader {
                leader_hint: self.get_current_leader().await,
            });
        }
        
        // 创建完成通道
        let (tx, rx) = oneshot::channel();
        
        // 追加命令到日志
        let index = {
            let mut log = self.log.write().await;
            let mut state = self.state.write().await;
            
            let index = log.append(
                state.current_term,
                Some(command),
                LogEntryType::Command
            );
            
            // 注册回调
            state.pending_responses.insert(index, tx);
            
            index
        };
        
        // 复制日志到其他节点
        self.replicate_logs().await;
        
        // 等待命令提交并应用
        match tokio::time::timeout(Duration::from_secs(10), rx).await {
            Ok(Ok(result)) => Ok(result),
            Ok(Err(_)) => Err(CommandError::InternalError("Response channel closed".into())),
            Err(_) => Err(CommandError::Timeout),
        }
    }
    
    // 将提交的命令应用到状态机
    async fn apply_committed_entries(&self) {
        let mut entries_to_apply = {
            let log = self.log.read().await;
            log.get_unapplied_entries()
        };
        
        if entries_to_apply.is_empty() {
            return;
        }
        
        let mut state = self.state.write().await;
        let mut log = self.log.write().await;
        let mut state_machine = self.state_machine.write().await;
        
        for entry in entries_to_apply {
            if let Some(command) = &entry.command {
                // 应用命令到状态机
                let result = state_machine.apply(command);
                
                // 通知等待的客户端
                if let Some(response_sender) = state.pending_responses.remove(&entry.index) {
                    let _ = response_sender.send(result);
                }
            }
            
            // 更新已应用索引
            log.update_last_applied(entry.index);
        }
    }
    
    // 将日志复制到追随者
    async fn replicate_logs(&self) {
        let state = self.state.read().await;
        
        if !matches!(state.role, NodeRole::Leader { .. }) {
            return;
        }
        
        for (peer_id, peer) in &self.peers {
            let peer_id = peer_id.clone();
            let peer = peer.clone();
            let self_clone = self.clone();
            
            tokio::spawn(async move {
                self_clone.replicate_to_follower(peer_id, peer).await;
            });
        }
    }
    
    // 复制日志到单个追随者
    async fn replicate_to_follower(&self, peer_id: NodeId, peer: PeerClient) {
        // 获取要发送的日志条目
        let (term, prev_log_index, prev_log_term, entries, commit_index) = {
            let state = self.state.read().await;
            let log = self.log.read().await;
            
            let next_index = if let NodeRole::Leader { ref next_indices, .. } = state.role {
                next_indices.get(&peer_id).cloned().unwrap_or(1)
            } else {
                return;
            };
            
            // 获取前一个日志条目的索引和任期
            let prev_log_index = next_index - 1;
            let prev_log_term = if prev_log_index == 0 {
                0
            } else {
                log.get(prev_log_index)
                    .map(|entry| entry.term)
                    .unwrap_or(0)
            };
            
            // 获取要发送的条目
            let entries: Vec<_> = log.entries
                .iter()
                .skip(next_index as usize)
                .cloned()
                .collect();
            
            (state.current_term, prev_log_index, prev_log_term, entries, log.commit_index)
        };
        
        // 发送AppendEntries请求
        match peer.append_entries(
            term,
            self.id.clone(),
            prev_log_index,
            prev_log_term,
            entries.clone(),
            commit_index
        ).await {
            Ok(response) => {
                if response.success {
                    // 更新follower的进度
                    let mut state = self.state.write().await;
                    
                    if let NodeRole::Leader { ref mut next_indices, ref mut match_indices, .. } = state.role {
                        let new_next_index = prev_log_index + entries.len() as u64 + 1;
                        let new_match_index = prev_log_index + entries.len() as u64;
                        
                        next_indices.insert(peer_id.clone(), new_next_index);
                        match_indices.insert(peer_id.clone(), new_match_index);
                        
                        // 更新提交索引
                        self.update_commit_index().await;
                    }
                } else {
                    // 日志不匹配，减少nextIndex并重试
                    let mut state = self.state.write().await;
                    
                    if let NodeRole::Leader { ref mut next_indices, .. } = state.role {
                        if let Some(next_index) = next_indices.get_mut(&peer_id) {
                            *next_index = (*next_index - 1).max(1);
                        }
                    }
                }
            },
            Err(e) => {
                log::error!("Failed to send AppendEntries to {}: {}", peer_id, e);
            }
        }
    }
    
    // 更新提交索引
    async fn update_commit_index(&self) {
        let (leader_term, match_indices) = {
            let state = self.state.read().await;
            
            if let NodeRole::Leader { ref match_indices, .. } = state.role {
                (state.current_term, match_indices.clone())
            } else {
                return;
            }
        };
        
        // 收集所有复制进度
        let mut indices: Vec<u64> = match_indices.values().cloned().collect();
        indices.push(self.log.read().await.entries.len() as u64 - 1); // 包括leader自己
        
        // 排序以找到中位数（大多数节点已复制的索引）
        indices.sort_unstable();
        let majority_index = indices[indices.len() / 2];
        
        // 验证此索引的任期是否为当前任期
        let can_commit = {
            let log = self.log.read().await;
            if let Some(entry) = log.get(majority_index) {
                entry.term == leader_term
            } else {
                false
            }
        };
        
        if can_commit {
            // 更新提交索引
            let mut log = self.log.write().await;
            log.update_commit_index(majority_index);
            
            // 应用已提交的条目
            drop(log);
            self.apply_committed_entries().await;
        }
    }
}
```

**共识协议的实现考虑**：

1. **领导者选举**：
   - 选举超时和心跳机制
   - 预投票阶段减少不必要的选举
   - 领导者转移优化

2. **日志复制**：
   - 批量复制优化以减少网络开销
   - 流水线复制提高吞吐量
   - 日志压缩减少存储需求

```rust
// 日志压缩/快照实现
impl<S: StateMachine> RaftNode<S> {
    // 创建快照
    async fn create_snapshot(&self) -> Result<(), SnapshotError> {
        let snapshot_index = {
            let log = self.log.read().await;
            log.last_applied
        };
        
        if snapshot_index == 0 {
            return Ok(());  // 没有需要快照的内容
        }
        
        // 创建状态机快照
        let snapshot_data = {
            let state_machine = self.state_machine.read().await;
            state_machine.create_snapshot()
        };
        
        // 获取最后应用条目的任期
        let snapshot_term = {
            let log = self.log.read().await;
            log.get(snapshot_index)
                .map(|entry| entry.term)
                .unwrap_or(0)
        };
        
        // 保存快照元数据和数据
        let snapshot_meta = SnapshotMetadata {
            index: snapshot_index,
            term: snapshot_term,
            cluster_config: self.get_cluster_config().await,
        };
        
        self.storage.save_snapshot(&snapshot_meta, &snapshot_data).await?;
        
        // 压缩日志（删除已快照的条目）
        let mut log = self.log.write().await;
        
        // 保留一个条目用于一致性检查
        let compact_index = if snapshot_index > 0 { snapshot_index - 1 } else { 0 };
        
        // 移除已保存在快照中的条目
        let new_entries = log.entries
            .drain((compact_index + 1) as usize..)
            .collect::<Vec<_>>();
        
        log.entries = vec![
            // 保留一个空条目作为新日志的起点
            LogEntry {
                term: snapshot_term,
                index: snapshot_index,
                command: None,
                entry_type: LogEntryType::NoOp,
            }
        ];
        
        // 将compact_index之后的条目重新添加回来
        log.entries.extend(new_entries);
        
        Ok(())
    }
    
    // 安装快照到follower
    async fn install_snapshot_to_follower(
        &self,
        follower_id: NodeId,
        peer: PeerClient
    ) -> Result<(), SnapshotError> {
        let (term, snapshot_meta, snapshot_data) = {
            let state = self.state.read().await;
            let snapshot_meta = self.storage.get_snapshot_metadata().await?;
            let snapshot_data = self.storage.get_snapshot_data().await?;
            
            (state.current_term, snapshot_meta, snapshot_data)
        };
        
        // 分块发送快照
        const CHUNK_SIZE: usize = 1024 * 1024;  // 1MB
        let total_chunks = (snapshot_data.len() + CHUNK_SIZE - 1) / CHUNK_SIZE;
        
        for chunk_id in 0..total_chunks {
            let start = chunk_id * CHUNK_SIZE;
            let end = (start + CHUNK_SIZE).min(snapshot_data.len());
            let chunk = &snapshot_data[start..end];
            let is_last = chunk_id == total_chunks - 1;
            
            let response = peer.install_snapshot(
                term,
                self.id.clone(),
                snapshot_meta.clone(),
                chunk_id as u64,
                chunk.to_vec(),
                is_last
            ).await?;
            
            if !response.success {
                if response.term > term {
                    // 发现更高任期，转为follower
                    let mut state = self.state.write().await;
                    if response.term > state.current_term {
                        state.current_term = response.term;
                        self.become_follower(None).await;
                    }
                }
                
                return Err(SnapshotError::InstallationRejected);
            }
        }
        
        Ok(())
    }
    
    // 从快照恢复
    async fn restore_from_snapshot(&self) -> Result<(), SnapshotError> {
        let snapshot_meta = self.storage.get_snapshot_metadata().await?;
        let snapshot_data = self.storage.get_snapshot_data().await?;
        
        // 恢复状态机
        let restored_state_machine = S::restore_from_snapshot(&snapshot_data)?;
        
        {
            let mut state_machine = self.state_machine.write().await;
            *state_machine = restored_state_machine;
        }
        
        // 重置日志
        {
            let mut log = self.log.write().await;
            log.entries = vec![
                LogEntry {
                    term: snapshot_meta.term,
                    index: snapshot_meta.index,
                    command: None,
                    entry_type: LogEntryType::NoOp,
                }
            ];
            
            log.commit_index = snapshot_meta.index;
            log.last_applied = snapshot_meta.index;
        }
        
        // 更新集群配置
        self.apply_cluster_config(snapshot_meta.cluster_config).await;
        
        Ok(())
    }
}
```

1. **成员变更**：
   - 安全的集群配置变更
   - 联合共识方法
   - 单服务器变更方法

```rust
// 集群配置变更
impl<S: StateMachine> RaftNode<S> {
    // 添加节点
    async fn add_node(&self, node_id: NodeId, address: String) -> Result<(), ConfigError> {
        let is_leader = {
            let state = self.state.read().await;
            matches!(state.role, NodeRole::Leader { .. })
        };
        
        if !is_leader {
            return Err(ConfigError::NotLeader);
        }
        
        // 获取当前配置
        let current_config = self.get_cluster_config().await;
        
        // 检查节点是否已存在
        if current_config.nodes.contains_key(&node_id) {
            return Err(ConfigError::NodeAlreadyExists);
        }
        
        // 创建新配置
        let mut new_config = current_config.clone();
        new_config.nodes.insert(node_id.clone(), address);
        
        // 创建配置变更日志条目
        self.append_config_change(ConfigChange::AddNode {
            node_id: node_id.clone(),
            address: address.clone(),
        }).await?;
        
        // 等待配置变更提交
        self.wait_for_config_commit().await?;
        
        // 创建与新节点的连接
        let peer_client = PeerClient::connect(address).await?;
        
        // 更新peers
        {
            let mut state = self.state.write().await;
            if let NodeRole::Leader { ref mut next_indices, ref mut match_indices, .. } = state.role {
                // 初始化新节点的复制状态
                let next_index = self.log.read().await.entries.len() as u64;
                next_indices.insert(node_id.clone(), next_index);
                match_indices.insert(node_id.clone(), 0);
            }
            
            // 添加新peer客户端
            self.peers.insert(node_id, peer_client);
        }
        
        Ok(())
    }
    
    // 移除节点
    async fn remove_node(&self, node_id: NodeId) -> Result<(), ConfigError> {
        let is_leader = {
            let state = self.state.read().await;
            matches!(state.role, NodeRole::Leader { .. })
        };
        
        if !is_leader {
            return Err(ConfigError::NotLeader);
        }
        
        // 获取当前配置
        let current_config = self.get_cluster_config().await;
        
        // 检查节点是否存在
        if !current_config.nodes.contains_key(&node_id) {
            return Err(ConfigError::NodeNotFound);
        }
        
        // 创建新配置
        let mut new_config = current_config.clone();
        new_config.nodes.remove(&node_id);
        
        // 检查移除节点后是否仍有多数节点
        if new_config.nodes.len() < 2 {
            return Err(ConfigError::InsufficientNodes);
        }
        
        // 创建配置变更日志条目
        self.append_config_change(ConfigChange::RemoveNode {
            node_id: node_id.clone(),
        }).await?;
        
        // 等待配置变更提交
        self.wait_for_config_commit().await?;
        
        // 更新peers
        {
            let mut state = self.state.write().await;
            if let NodeRole::Leader { ref mut next_indices, ref mut match_indices, .. } = state.role {
                // 移除节点的复制状态
                next_indices.remove(&node_id);
                match_indices.remove(&node_id);
            }
            
            // 移除peer客户端
            self.peers.remove(&node_id);
        }
        
        Ok(())
    }
    
    // 追加配置变更日志条目
    async fn append_config_change(&self, change: ConfigChange) -> Result<u64, ConfigError> {
        let (term, index) = {
            let mut state = self.state.write().await;
            let mut log = self.log.write().await;
            
            if !matches!(state.role, NodeRole::Leader { .. }) {
                return Err(ConfigError::NotLeader);
            }
            
            let term = state.current_term;
            let index = log.append(
                term,
                Some(S::Command::from_config_change(change)?),
                LogEntryType::Configuration
            );
            
            (term, index)
        };
        
        // 触发日志复制
        self.replicate_logs().await;
        
        Ok(index)
    }
    
    // 等待配置变更提交
    async fn wait_for_config_commit(&self) -> Result<(), ConfigError> {
        // 创建一个超时跟踪器
        let timeout = tokio::time::sleep(Duration::from_secs(10));
        tokio::pin!(timeout);
        
        loop {
            // 检查配置是否已提交
            let (last_config_index, commit_index) = {
                let log = self.log.read().await;
                
                // 找到最后一个配置变更条目
                let last_config_index = log.entries.iter()
                    .rev()
                    .find(|entry| matches!(entry.entry_type, LogEntryType::Configuration))
                    .map(|entry| entry.index)
                    .unwrap_or(0);
                
                (last_config_index, log.commit_index)
            };
            
            if commit_index >= last_config_index {
                return Ok(());  // 配置已提交
            }
            
            // 检查超时
            tokio::select! {
                _ = &mut timeout => {
                    return Err(ConfigError::Timeout);
                }
                _ = tokio::time::sleep(Duration::from_millis(100)) => {
                    // 继续等待
                }
            }
        }
    }
}
```

1. **正确性与安全性**：
   - 选举约束和日志匹配
   - 幂等操作
   - 单调读取和线性化读取

```rust
// 实现线性化读取
impl<S: StateMachine> RaftNode<S> {
    // 线性化读取实现
    async fn linearizable_read<F, R>(&self, read_fn: F) -> Result<R, ReadError>
    where
        F: FnOnce(&S) -> R,
        R: Clone + Send + 'static,
    {
        // 检查是否是领导者
        if !self.is_leader().await {
            return Err(ReadError::NotLeader {
                leader_hint: self.get_current_leader().await,
            });
        }
        
        // 方法1: 读取屏障（将空日志条目提交）
        let read_barrier_result = self.read_barrier().await;
        
        if let Err(e) = read_barrier_result {
            return Err(ReadError::BarrierFailed(e.to_string()));
        }
        
        // 方法2: 领导者租约（确保在租约期间没有新的领导者）
        if !self.check_leadership_lease().await {
            return Err(ReadError::LeaseExpired);
        }
        
        // 执行读取操作
        let state_machine = self.state_machine.read().await;
        let result = read_fn(&*state_machine);
        
        Ok(result)
    }
    
    // 读取屏障：提交一个空日志条目确保之前的日志都已应用
    async fn read_barrier(&self) -> Result<(), BarrierError> {
        // 创建并复制一个NoOp条目
        let (term, index) = {
            let mut state = self.state.write().await;
            let mut log = self.log.write().await;
            
            if !matches!(state.role, NodeRole::Leader { .. }) {
                return Err(BarrierError::NotLeader);
            }
            
            let term = state.current_term;
            let index = log.append(
                term,
                None,  // 无命令
                LogEntryType::NoOp
            );
            
            (term, index)
        };
        
        // 等待NoOp条目提交
        self.replicate_logs().await;
        
        // 创建一个超时
        let timeout = tokio::time::sleep(Duration::from_secs(5));
        tokio::pin!(timeout);
        
        loop {
            // 检查条目是否已提交
            let commit_index = self.log.read().await.commit_index;
            
            if commit_index >= index {
                return Ok(());  // 屏障已通过
            }
            
            // 检查是否仍然是领导者
            if !self.is_leader().await {
                return Err(BarrierError::LeadershipLost);
            }
            
            // 检查超时
            tokio::select! {
                _ = &mut timeout => {
                    return Err(BarrierError::Timeout);
                }
                _ = tokio::time::sleep(Duration::from_millis(100)) => {
                    // 继续等待
                }
            }
        }
    }
    
    // 检查领导者租约
    async fn check_leadership_lease(&self) -> bool {
        let state = self.state.read().await;
        
        if let NodeRole::Leader { lease_expiration, .. } = &state.role {
            // 检查租约是否有效
            let now = Instant::now();
            *lease_expiration > now
        } else {
            false
        }
    }
    
    // 续约领导者租约
    async fn renew_leadership_lease(&self) {
        let mut state = self.state.write().await;
        
        if let NodeRole::Leader { ref mut lease_expiration, .. } = state.role {
            // 计算最晚的心跳响应时间
            let min_response_time = self.calculate_min_response_time().await;
            
            // 计算新的租约过期时间
            // 租约时间 = 最晚心跳响应时间 + (心跳间隔 / 2)
            let now = Instant::now();
            let half_heartbeat = Duration::from_millis(HEARTBEAT_INTERVAL_MS / 2);
            
            if let Some(response_time) = min_response_time {
                let new_expiration = response_time + half_heartbeat;
                if new_expiration > *lease_expiration {
                    *lease_expiration = new_expiration;
                }
            }
        }
    }
    
    // 计算最晚的心跳响应时间
    async fn calculate_min_response_time(&self) -> Option<Instant> {
        let state = self.state.read().await;
        
        if let NodeRole::Leader { ref heartbeat_responses, .. } = state.role {
            // 找到超过半数节点的心跳响应时间
            let mut response_times: Vec<_> = heartbeat_responses.values().cloned().collect();
            
            if response_times.is_empty() {
                return None;
            }
            
            // 排序并取中位数（确保超过半数节点的响应时间）
            response_times.sort();
            let majority_index = response_times.len() / 2;
            
            Some(response_times[majority_index])
        } else {
            None
        }
    }
}
```

这些实现展示了分布式共识系统中关键的功能和优化，包括日志压缩、安全的配置变更和线性化读取。在实际系统中，这些组件协同工作，确保分布式状态复制的一致性和可靠性。

### 3.3 分区与数据分片

在大规模分布式系统中，单个节点通常无法处理或存储所有数据。分区和分片技术允许将数据分散到多个节点，实现水平扩展。

**分区与分片的核心概念**：

```rust
DataPartitioning = {
    分区策略: "决定如何将数据分布到不同节点",
    分片负载均衡: "确保数据均匀分布",
    分片迁移: "在不停机的情况下重新分配数据",
    跨分片操作: "处理涉及多个分片的操作",
    分片路由: "将请求正确路由到拥有数据的分片"
}
```

**Rust中的分区实现**：

1. **一致性哈希分区**：

```rust
use std::collections::{BTreeMap, HashMap};
use std::hash::{Hash, Hasher};
use std::sync::Arc;
use tokio::sync::RwLock;

// 一致性哈希环
struct ConsistentHash<T: Clone + Send + Sync + 'static> {
    // 虚拟节点到实际节点的映射
    ring: Arc<RwLock<BTreeMap<u64, T>>>,
    // 节点到其虚拟节点列表的映射
    node_to_vnodes: Arc<RwLock<HashMap<T, Vec<u64>>>>,
    // 每个节点的虚拟节点数量
    vnode_count: usize,
    // 哈希函数
    hash_fn: Arc<dyn Fn(&[u8]) -> u64 + Send + Sync>,
}

impl<T: Clone + Send + Sync + Hash + Eq + 'static> ConsistentHash<T> {
    // 创建新的一致性哈希环
    fn new(vnode_count: usize, hash_fn: impl Fn(&[u8]) -> u64 + Send + Sync + 'static) -> Self {
        Self {
            ring: Arc::new(RwLock::new(BTreeMap::new())),
            node_to_vnodes: Arc::new(RwLock::new(HashMap::new())),
            vnode_count,
            hash_fn: Arc::new(hash_fn),
        }
    }
    
    // 添加节点及其虚拟节点
    async fn add_node(&self, node: T) {
        let mut ring = self.ring.write().await;
        let mut node_to_vnodes = self.node_to_vnodes.write().await;
        
        // 为节点创建虚拟节点
        let mut vnodes = Vec::with_capacity(self.vnode_count);
        
        for i in 0..self.vnode_count {
            // 为每个虚拟节点计算哈希值
            let key = format!("{:?}:{}", node, i);
            let hash = (self.hash_fn)(key.as_bytes());
            
            // 将虚拟节点添加到环
            ring.insert(hash, node.clone());
            vnodes.push(hash);
        }
        
        // 保存节点的虚拟节点列表
        node_to_vnodes.insert(node, vnodes);
    }
    
    // 移除节点及其虚拟节点
    async fn remove_node(&self, node: &T) {
        let mut ring = self.ring.write().await;
        let mut node_to_vnodes = self.node_to_vnodes.write().await;
        
        // 获取节点的虚拟节点列表
        if let Some(vnodes) = node_to_vnodes.remove(node) {
            // 从环中移除所有虚拟节点
            for vnode in vnodes {
                ring.remove(&vnode);
            }
        }
    }
    
    // 获取键应该位于的节点
    async fn get_node(&self, key: &[u8]) -> Option<T> {
        let ring = self.ring.read().await;
        
        if ring.is_empty() {
            return None;
        }
        
        let hash = (self.hash_fn)(key);
        
        // 找到大于等于哈希值的第一个虚拟节点
        if let Some((_, node)) = ring.range(hash..).next() {
            return Some(node.clone());
        }
        
        // 如果没有找到大于等于的虚拟节点，返回环的第一个节点
        if let Some((_, node)) = ring.iter().next() {
            return Some(node.clone());
        }
        
        None
    }
    
    // 获取键的所有副本位置（用于复制）
    async fn get_replica_nodes(&self, key: &[u8], replica_count: usize) -> Vec<T> {
        let ring = self.ring.read().await;
        
        if ring.is_empty() || replica_count == 0 {
            return Vec::new();
        }
        
        let hash = (self.hash_fn)(key);
        let mut result = Vec::with_capacity(replica_count);
        let mut seen_nodes = std::collections::HashSet::new();
        
        // 从哈希值开始遍历环
        let mut iter = ring.range(hash..);
        
        // 收集唯一节点直到达到副本数量
        while result.len() < replica_count {
            // 如果到达环的末尾，从头开始
            if iter.clone().next().is_none() {
                iter = ring.range(..);
                if iter.clone().next().is_none() {
                    break;  // 环为空
                }
            }
            
            if let Some((_, node)) = iter.next() {
                // 只添加未见过的节点
                if seen_nodes.insert(node.clone()) {
                    result.push(node.clone());
                }
            } else {
                break;  // 不应该到达这里
            }
        }
        
        result
    }
    
    // 获取环中的所有节点
    async fn get_all_nodes(&self) -> Vec<T> {
        let node_to_vnodes = self.node_to_vnodes.read().await;
        node_to_vnodes.keys().cloned().collect()
    }
    
    // 计算节点拥有的键范围百分比（用于负载分析）
    async fn node_ownership_percentage(&self, node: &T) -> f64 {
        let ring = self.ring.read().await;
        let node_to_vnodes = self.node_to_vnodes.read().await;
        
        let total_vnodes = ring.len();
        
        if total_vnodes == 0 {
            return 0.0;
        }
        
        // 获取节点的虚拟节点数量
        let node_vnodes = node_to_vnodes.get(node).map_or(0, |v| v.len());
        
        (node_vnodes as f64 / total_vnodes as f64) * 100.0
    }
}

// 使用示例
async fn consistent_hash_example() {
    // 创建一致性哈希环
    let hasher = ConsistentHash::new(100, |data| {
        use std::collections::hash_map::DefaultHasher;
        let mut hasher = DefaultHasher::new();
        data.hash(&mut hasher);
        hasher.finish()
    });
    
    // 添加节点
    hasher.add_node("node1".to_string()).await;
    hasher.add_node("node2".to_string()).await;
    hasher.add_node("node3".to_string()).await;
    
    // 获取键的位置
    let node = hasher.get_node("user:1001".as_bytes()).await.unwrap();
    println!("Key 'user:1001' is located at: {}", node);
    
    // 获取副本位置
    let replicas = hasher.get_replica_nodes("product:2002".as_bytes(), 2).await;
    println!("Replicas for 'product:2002': {:?}", replicas);
    
    // 分析负载分布
    for node in hasher.get_all_nodes().await {
        let percentage = hasher.node_ownership_percentage(&node).await;
        println!("Node {} owns {:.2}% of the keyspace", node, percentage);
    }
    
    // 模拟节点失败
    println!("Removing node2...");
    hasher.remove_node(&"node2".to_string()).await;
    
    // 重新检查键的位置
    let new_node = hasher.get_node("user:1001".as_bytes()).await.unwrap();
    println!("After node removal, key 'user:1001' is now at: {}", new_node);
}
```

1. **范围分区**：

```rust
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::ops::Range;
use std::sync::Arc;
use tokio::sync::RwLock;

// 范围分区管理器
struct RangePartitionManager<K: Ord + Clone + Send + Sync, N: Clone + Send + Sync> {
    // 分区范围到节点的映射
    partitions: Arc<RwLock<BTreeMap<K, N>>>,
}

impl<K: Ord + Clone + Send + Sync + 'static, N: Clone + Send + Sync + 'static> RangePartitionManager<K, N> {
    fn new() -> Self {
        Self {
            partitions: Arc::new(RwLock::new(BTreeMap::new())),
        }
    }
    
    // 添加分区
    async fn add_partition(&self, start_key: K, node: N) {
        let mut partitions = self.partitions.write().await;
        partitions.insert(start_key, node);
    }
    
    // 移除分区
    async fn remove_partition(&self, start_key: &K) {
        let mut partitions = self.partitions.write().await;
        partitions.remove(start_key);
    }
    
    // 获取键所在的节点
    async fn get_node_for_key(&self, key: &K) -> Option<N> {
        let partitions = self.partitions.read().await;
        
        if partitions.is_empty() {
            return None;
        }
        
        // 找到小于等于key的最大start_key
        let partition = partitions.range(..=key).next_back();
        
        partition.map(|(_, node)| node.clone())
    }
    
    // 获取范围查询涉及的所有节点
    async fn get_nodes_for_range(&self, range: Range<K>) -> Vec<N> {
        let partitions = self.partitions.read().await;
        
        if partitions.is_empty() {
            return Vec::new();
        }
        
        let mut result = Vec::new();
        let mut seen_nodes = std::collections::HashSet::new();
        
        // 找到范围起始位置所在的分区
        if let Some((_, first_node)) = partitions.range(..=range.start).next_back() {
            seen_nodes.insert(first_node.clone());
            result.push(first_node.clone());
        }
        
        // 找到范围内的所有分区
        for (_, node) in partitions.range(range) {
            if seen_nodes.insert(node.clone()) {
                result.push(node.clone());
            }
        }
        
        result
    }
    
    // 获取所有分区信息
    async fn get_all_partitions(&self) -> Vec<(K, N)> {
        let partitions = self.partitions.read().await;
        partitions.iter().map(|(k, n)| (k.clone(), n.clone())).collect()
    }
    
    // 拆分分区
    async fn split_partition(&self, old_key: &K, new_key: K, new_node: N) -> Result<(), PartitionError> {
        let mut partitions = self.partitions.write().await;
        
        // 检查old_key是否存在
        if !partitions.contains_key(old_key) {
            return Err(PartitionError::PartitionNotFound);
        }
        
        // 检查新键是否已存在
        if partitions.contains_key(&new_key) {
            return Err(PartitionError::PartitionAlreadyExists);
        }
        
        // 找到old_key的下一个键
        let mut next_key = None;
        for k in partitions.keys() {
            if k > old_key {
                next_key = Some(k.clone());
                break;
            }
        }
        
        // 验证new_key在有效范围内
        if let Some(next) = next_key {
            if new_key >= next {
                return Err(PartitionError::InvalidPartitionKey);
            }
        }
        
        // 添加新分区
        partitions.insert(new_key, new_node);
        
        Ok(())
    }
    
    // 合并分区
    async fn merge_partitions(&self, key1: &K, key2: &K) -> Result<(), PartitionError> {
        let mut partitions = self.partitions.write().await;
        
        // 检查两个键是否都存在
        if !partitions.contains_key(key1) || !partitions.contains_key(key2) {
            return Err(PartitionError::PartitionNotFound);
        }
        
        // 检查key2是否是key1的直接后继
        let mut is_direct_successor = false;
        let mut prev_key = None;
        
        for k in partitions.keys() {
            if prev_key.as_ref() == Some(key1) && k == key2 {
                is_direct_successor = true;
                break;
            }
            prev_key = Some(k);
        }
        
        if !is_direct_successor {
            return Err(PartitionError::NotAdjacentPartitions);
        }
        
        // 移除第二个分区
        partitions.remove(key2);
        
        Ok(())
    }
}

// 分区错误类型
enum PartitionError {
    PartitionNotFound,
    PartitionAlreadyExists,
    InvalidPartitionKey,
    NotAdjacentPartitions,
}

// 使用示例
async fn range_partition_example() {
    // 创建范围分区管理器
    let manager = RangePartitionManager::<String, String>::new();
    
    // 添加分区
    manager.add_partition("A".to_string(), "node1".to_string()).await;
    manager.add_partition("N".to_string(), "node2".to_string()).await;
    manager.add_partition("Z".to_string(), "node3".to_string()).await;
    
    // 查找键所在节点
    let node1 = manager.get_node_for_key(&"G".to_string()).await;
    println!("Key 'G' is on node: {:?}", node1);  // node1
    
    let node2 = manager.get_node_for_key(&"P".to_string()).await;
    println!("Key 'P' is on node: {:?}", node2);  // node2
    
    // 处理范围查询
    let range_nodes = manager.get_nodes_for_range("H".to_string().."T".to_string()).await;
    println!("Range 'H' to 'T' spans nodes: {:?}", range_nodes);  // [node1, node2]
    
    // 拆分分区
    manager.split_partition(
        &"N".to_string(), 
        "Q".to_string(), 
        "node4".to_string()
    ).await.unwrap();
    
    println!("\nAfter splitting at 'Q':");
    
    // 显示所有分区
    let partitions = manager.get_all_partitions().await;
    for (key, node) in partitions {
        println!("Partition starting at '{}' is on node '{}'", key, node);
    }
    
    // 重新检查键的位置
    let node_p = manager.get_node_for_key(&"P".to_string()).await;
    println!("After split, key 'P' is on node: {:?}", node_p);  // node2
    
    let node_r = manager.get_node_for_key(&"R".to_string()).await;
    println!("After split, key 'R' is on node: {:?}", node_r);  // node4
}
```

1. **分片路由与代理**：

```rust
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::{RwLock, mpsc, oneshot};
use serde::{Serialize, Deserialize};

// 分片操作
#[derive(Debug, Clone, Serialize, Deserialize)]
enum ShardOperation<K, V> {
    Get { key: K },
    Put { key: K, value: V },
    Delete { key: K },
    Range { start: K, end: K },
}

// 分片响应
#[derive(Debug, Clone, Serialize, Deserialize)]
enum ShardResponse<V> {
    Value(Option<V>),
    Success(bool),
    Values(Vec<V>),
    Error(String),
}

// 分片路由器
struct ShardRouter<K, V, S>
where
    K: Clone + Send + Sync + Ord + 'static,
    V: Clone + Send + Sync + 'static,
    S: ShardLocator<K> + Send + Sync + 'static,
{
    // 分片定位器
    locator: S,
    // 分片客户端
    shard_clients: Arc<RwLock<HashMap<String, ShardClient<K, V>>>>,
}

// 分片定位器接口
trait ShardLocator<K> {
    fn locate(&self, key: &K) -> Result<String, ShardError>;
    fn locate_range(&self, start: &K, end: &K) -> Result<Vec<String>, ShardError>;
}

// 分片客户端
struct ShardClient<K, V>
where
    K: Clone + Send + Sync + 'static,
    V: Clone + Send + Sync + 'static,
{
    shard_id: String,
    // 发送通道，发送操作到分片处理器
    sender: mpsc::Sender<(ShardOperation<K, V>, oneshot::Sender<ShardResponse<V>>)>,
}

impl<K, V> ShardClient<K, V>
where
    K: Clone + Send + Sync + 'static,
    V: Clone + Send + Sync + 'static,
{
    // 创建新的分片客户端
    fn new(shard_id: String, sender: mpsc::Sender<(ShardOperation<K, V>, oneshot::Sender<ShardResponse<V>>)>) -> Self {
        Self { shard_id, sender }
    }
    
    // 执行获取操作
    async fn get(&self, key: K) -> Result<Option<V>, ShardError> {
        let (tx, rx) = oneshot::channel();
        
        self.sender.send((ShardOperation::Get { key }, tx)).await
            .map_err(|_| ShardError::ConnectionError)?;
        
        match rx.await.map_err(|_| ShardError::ResponseError)? {
            ShardResponse::Value(value) => Ok(value),
            ShardResponse::Error(err) => Err(ShardError::OperationFailed(err)),
            _ => Err(ShardError::UnexpectedResponse),
        }
    }
    
    // 执行放置操作
    async fn put(&self, key: K, value: V) -> Result<bool, ShardError> {
        let (tx, rx) = oneshot::channel();
        
        self.sender.send((ShardOperation::Put { key, value }, tx)).await
            .map_err(|_| ShardError::ConnectionError)?;
        
        match rx.await.map_err(|_| ShardError::ResponseError)? {
            ShardResponse::Success(success) => Ok(success),
            ShardResponse::Error(err) => Err(ShardError::OperationFailed(err)),
            _ => Err(ShardError::UnexpectedResponse),
        }
    }
    
    // 执行删除操作
    async fn delete(&self, key: K) -> Result<bool, ShardError> {
        let (tx, rx) = oneshot::channel();
        
        self.sender.send((ShardOperation::Delete { key }, tx)).await
            .map_err(|_| ShardError::ConnectionError)?;
        
        match rx.await.map_err(|_| ShardError::ResponseError)? {
            ShardResponse::Success(success) => Ok(success),
            ShardResponse::Error(err) => Err(ShardError::OperationFailed(err)),
            _ => Err(ShardError::UnexpectedResponse),
        }
    }
    
    // 执行范围查询操作
    async fn range(&self, start: K, end: K) -> Result<Vec<V>, ShardError> {
        let (tx, rx) = oneshot::channel();
        
        self.sender.send((ShardOperation::Range { start, end }, tx)).await
            .map_err(|_| ShardError::ConnectionError)?;
        
        match rx.await.map_err(|_| ShardError::ResponseError)? {
            ShardResponse::Values(values) => Ok(values),
            ShardResponse::Error(err) => Err(ShardError::OperationFailed(err)),
            _ => Err(ShardError::UnexpectedResponse),
        }
    }
}

// 分片错误类型
#[derive(Debug, thiserror::Error)]
enum ShardError {
    #[error("分片操作失败: {0}")]
    OperationFailed(String),
    
    #[error("连接错误")]
    ConnectionError,
    
    #[error("响应错误")]
    ResponseError,
    
    #[error("未预期的响应类型")]
    UnexpectedResponse,
    
    #[error("分片不存在")]
    ShardNotFound,
    
    #[error("无效的键范围")]
    InvalidKeyRange,
}

// 分片路由器实现
impl<K, V, S> ShardRouter<K, V, S>
where
    K: Clone + Send + Sync + Ord + 'static,
    V: Clone + Send + Sync + 'static,
    S: ShardLocator<K> + Send + Sync + 'static,
{
    // 创建新的分片路由器
    fn new(locator: S) -> Self {
        Self {
            locator,
            shard_clients: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    // 注册分片客户端
    async fn register_shard(&self, shard_id: String, client: ShardClient<K, V>) {
        let mut clients = self.shard_clients.write().await;
        clients.insert(shard_id, client);
    }
    
    // 路由获取操作到正确的分片
    async fn get(&self, key: K) -> Result<Option<V>, ShardError> {
        // 定位分片
        let shard_id = self.locator.locate(&key)?;
        
        // 获取分片客户端
        let clients = self.shard_clients.read().await;
        let client = clients.get(&shard_id)
            .ok_or(ShardError::ShardNotFound)?;
        
        // 执行操作
        client.get(key).await
    }
    
    // 路由放置操作到正确的分片
    async fn put(&self, key: K, value: V) -> Result<bool, ShardError> {
        // 定位分片
        let shard_id = self.locator.locate(&key)?;
        
        // 获取分片客户端
        let clients = self.shard_clients.read().await;
        let client = clients.get(&shard_id)
            .ok_or(ShardError::ShardNotFound)?;
        
        // 执行操作
        client.put(key, value).await
    }
    
    // 路由删除操作到正确的分片
    async fn delete(&self, key: K) -> Result<bool, ShardError> {
        // 定位分片
        let shard_id = self.locator.locate(&key)?;
        
        // 获取分片客户端
        let clients = self.shard_clients.read().await;
        let client = clients.get(&shard_id)
            .ok_or(ShardError::ShardNotFound)?;
        
        // 执行操作
        client.delete(key).await
    }
    
    // 处理跨分片范围查询
    async fn range(&self, start: K, end: K) -> Result<Vec<V>, ShardError> {
        if start > end {
            return Err(ShardError::InvalidKeyRange);
        }
        
        // 定位涉及的所有分片
        let shard_ids = self.locator.locate_range(&start, &end)?;
        
        // 获取分片客户端
        let clients = self.shard_clients.read().await;
        
        // 并行执行跨分片查询
        let mut tasks = Vec::new();
        
        for shard_id in shard_ids {
            let client = match clients.get(&shard_id) {
                Some(client) => client,
                None => continue, // 跳过不存在的分片
            };
            
            let start_clone = start.clone();
            let end_clone = end.clone();
            
            // 为每个分片创建一个异步任务
            let task = tokio::spawn(async move {
                client.range(start_clone, end_clone).await
            });
            
            tasks.push(task);
        }
        
        // 等待所有查询完成并合并结果
        let mut all_values = Vec::new();
        
        for task in tasks {
            match task.await {
                Ok(Ok(values)) => {
                    all_values.extend(values);
                },
                Ok(Err(e)) => {
                    log::warn!("分片范围查询失败: {}", e);
                    // 继续处理其他分片结果
                },
                Err(e) => {
                    log::error!("分片查询任务失败: {}", e);
                    // 继续处理其他分片结果
                }
            }
        }
        
        // 排序结果（可选，取决于应用需求）
        // all_values.sort_by(|a, b| /* 自定义排序逻辑 */);
        
        Ok(all_values)
    }
}

// 基于范围的分片定位器实现
struct RangeShardLocator<K: Ord + Clone> {
    partitions: Arc<RwLock<BTreeMap<K, String>>>,
}

impl<K: Ord + Clone + Send + Sync + 'static> RangeShardLocator<K> {
    fn new() -> Self {
        Self {
            partitions: Arc::new(RwLock::new(BTreeMap::new())),
        }
    }
    
    // 添加分片范围
    async fn add_partition(&self, start_key: K, shard_id: String) {
        let mut partitions = self.partitions.write().await;
        partitions.insert(start_key, shard_id);
    }
    
    // 移除分片范围
    async fn remove_partition(&self, start_key: &K) {
        let mut partitions = self.partitions.write().await;
        partitions.remove(start_key);
    }
}

impl<K: Ord + Clone + Send + Sync + 'static> ShardLocator<K> for RangeShardLocator<K> {
    fn locate(&self, key: &K) -> Result<String, ShardError> {
        let partitions = self.partitions.blocking_read();
        
        if partitions.is_empty() {
            return Err(ShardError::ShardNotFound);
        }
        
        // 找到小于等于key的最大start_key
        let partition = partitions.range(..=key).next_back();
        
        match partition {
            Some((_, shard_id)) => Ok(shard_id.clone()),
            None => Err(ShardError::ShardNotFound),
        }
    }
    
    fn locate_range(&self, start: &K, end: &K) -> Result<Vec<String>, ShardError> {
        let partitions = self.partitions.blocking_read();
        
        if partitions.is_empty() {
            return Err(ShardError::ShardNotFound);
        }
        
        let mut result = Vec::new();
        let mut seen_shards = std::collections::HashSet::new();
        
        // 找到范围起始位置所在的分片
        if let Some((_, first_shard)) = partitions.range(..=start).next_back() {
            seen_shards.insert(first_shard.clone());
            result.push(first_shard.clone());
        }
        
        // 找到范围内的所有分片
        for (_, shard_id) in partitions.range((std::ops::Bound::Excluded(start), std::ops::Bound::Included(end))) {
            if seen_shards.insert(shard_id.clone()) {
                result.push(shard_id.clone());
            }
        }
        
        if result.is_empty() {
            Err(ShardError::ShardNotFound)
        } else {
            Ok(result)
        }
    }
}

// 使用示例
async fn sharding_example() {
    // 创建分片定位器
    let locator = RangeShardLocator::<String>::new();
    
    // 配置分片范围
    locator.add_partition("A".to_string(), "shard1".to_string()).await;
    locator.add_partition("N".to_string(), "shard2".to_string()).await;
    locator.add_partition("Z".to_string(), "shard3".to_string()).await;
    
    // 创建分片路由器
    let router = ShardRouter::new(locator);
    
    // 创建分片处理器和客户端
    for shard_id in &["shard1", "shard2", "shard3"] {
        let (tx, mut rx) = mpsc::channel(100);
        let client = ShardClient::new(shard_id.to_string(), tx);
        
        // 注册客户端
        router.register_shard(shard_id.to_string(), client).await;
        
        // 启动分片处理器
        let shard_id = shard_id.to_string();
        tokio::spawn(async move {
            // 模拟分片存储
            let mut storage = HashMap::<String, String>::new();
            
            while let Some((op, resp_tx)) = rx.recv().await {
                match op {
                    ShardOperation::Get { key } => {
                        println!("[{}] 处理获取操作: {}", shard_id, key);
                        let value = storage.get(&key).cloned();
                        let _ = resp_tx.send(ShardResponse::Value(value));
                    },
                    ShardOperation::Put { key, value } => {
                        println!("[{}] 处理放置操作: {} = {}", shard_id, key, value);
                        storage.insert(key, value);
                        let _ = resp_tx.send(ShardResponse::Success(true));
                    },
                    ShardOperation::Delete { key } => {
                        println!("[{}] 处理删除操作: {}", shard_id, key);
                        let existed = storage.remove(&key).is_some();
                        let _ = resp_tx.send(ShardResponse::Success(existed));
                    },
                    ShardOperation::Range { start, end } => {
                        println!("[{}] 处理范围操作: {} 到 {}", shard_id, start, end);
                        let values: Vec<_> = storage.iter()
                            .filter(|(k, _)| **k >= start && **k <= end)
                            .map(|(_, v)| v.clone())
                            .collect();
                        let _ = resp_tx.send(ShardResponse::Values(values));
                    },
                }
            }
        });
    }
    
    // 使用路由器进行操作
    router.put("C".to_string(), "value1".to_string()).await.unwrap();
    router.put("P".to_string(), "value2".to_string()).await.unwrap();
    router.put("Z".to_string(), "value3".to_string()).await.unwrap();
    
    // 获取值
    let v1 = router.get("C".to_string()).await.unwrap();
    println!("C = {:?}", v1);  // 应该在shard1
    
    let v2 = router.get("P".to_string()).await.unwrap();
    println!("P = {:?}", v2);  // 应该在shard2
    
    // 范围查询（跨分片）
    let values = router.range("O".to_string(), "Z".to_string()).await.unwrap();
    println!("Range O-Z: {:?}", values);  // 应该包含来自shard2和shard3的结果
}
```

1. **分片迁移**：

```rust
// 分片迁移管理器
struct ShardMigrationManager<K, V>
where
    K: Clone + Send + Sync + Ord + Serialize + DeserializeOwned + 'static,
    V: Clone + Send + Sync + Serialize + DeserializeOwned + 'static,
{
    active_migrations: Arc<RwLock<HashMap<String, MigrationStatus>>>,
    locator: Arc<RangeShardLocator<K>>,
    shard_clients: Arc<RwLock<HashMap<String, ShardClient<K, V>>>>,
}

// 迁移状态
#[derive(Clone, Debug)]
enum MigrationStatus {
    Preparing,
    Copying { progress: f64 },
    Verifying,
    Switching,
    Completed,
    Failed { reason: String },
}

impl<K, V> ShardMigrationManager<K, V>
where
    K: Clone + Send + Sync + Ord + Serialize + DeserializeOwned + 'static,
    V: Clone + Send + Sync + Serialize + DeserializeOwned + 'static,
{
    fn new(
        locator: Arc<RangeShardLocator<K>>,
        shard_clients: Arc<RwLock<HashMap<String, ShardClient<K, V>>>>
    ) -> Self {
        Self {
            active_migrations: Arc::new(RwLock::new(HashMap::new())),
            locator,
            shard_clients,
        }
    }
    
    // 开始分片迁移
    async fn start_migration(
        &self,
        migration_id: String,
        source_shard: String,
        target_shard: String,
        key_range: (K, K)
    ) -> Result<(), MigrationError> {
        // 检查源分片和目标分片是否存在
        {
            let clients = self.shard_clients.read().await;
            if !clients.contains_key(&source_shard) {
                return Err(MigrationError::ShardNotFound(source_shard));
            }
            if !clients.contains_key(&target_shard) {
                return Err(MigrationError::ShardNotFound(target_shard));
            }
        }
        
        // 检查迁移ID是否已存在
        {
            let migrations = self.active_migrations.read().await;
            if migrations.contains_key(&migration_id) {
                return Err(MigrationError::MigrationAlreadyExists);
            }
        }
        
        // 注册迁移
        {
            let mut migrations = self.active_migrations.write().await;
            migrations.insert(migration_id.clone(), MigrationStatus::Preparing);
        }
        
        // 启动迁移任务
        let self_clone = self.clone();
        tokio::spawn(async move {
            if let Err(e) = self_clone.execute_migration(
                migration_id.clone(),
                source_shard,
                target_shard,
                key_range
            ).await {
                // 更新迁移状态为失败
                let mut migrations = self_clone.active_migrations.write().await;
                migrations.insert(
                    migration_id,
                    MigrationStatus::Failed { reason: e.to_string() }
                );
            }
        });
        
        Ok(())
    }
    
    // 执行迁移过程
    async fn execute_migration(
        &self,
        migration_id: String,
        source_shard: String,
        target_shard: String,
        (start_key, end_key): (K, K)
    ) -> Result<(), MigrationError> {
        // 更新状态为复制
        {
            let mut migrations = self.active_migrations.write().await;
            migrations.insert(migration_id.clone(), MigrationStatus::Copying { progress: 0.0 });
        }
        
        // 从源分片获取数据
        let data = self.copy_data_from_source(
            &source_shard,
            &start_key,
            &end_key,
            &migration_id
        ).await?;
        
        // 更新状态为验证
        {
            let mut migrations = self.active_migrations.write().await;
            migrations.insert(migration_id.clone(), MigrationStatus::Verifying);
        }
        
        // 验证复制的数据
        self.verify_copied_data(&source_shard, &target_shard, &data).await?;
        
        // 更新状态为切换
        {
            let mut migrations = self.active_migrations.write().await;
            migrations.insert(migration_id.clone(), MigrationStatus::Switching);
        }
        
        // 更新分片路由，将流量切换到新分片
        self.update_routing(&start_key, &target_shard).await?;
        
        // 更新状态为完成
        {
            let mut migrations = self.active_migrations.write().await;
            migrations.insert(migration_id, MigrationStatus::Completed);
        }
        
        Ok(())
    }
    
    // 从源分片复制数据
    async fn copy_data_from_source(
        &self,
        source_shard: &str,
        start_key: &K,
        end_key: &K,
        migration_id: &str
    ) -> Result<HashMap<K, V>, MigrationError> {
        let clients = self.shard_clients.read().await;
        let source_client = clients.get(source_shard)
            .ok_or(MigrationError::ShardNotFound(source_shard.to_string()))?;
        
        // 获取源分片中的数据
        let values = source_client.range(start_key.clone(), end_key.clone()).await
            .map_err(|e| MigrationError::DataAccessError(e.to_string()))?;
        
        // 构建键值映射（这是简化实现，实际需要包含键）
        let mut data = HashMap::new();
        // ... 假设我们有方法从values构建完整的键值映射
        
        // 更新进度
        {
            let mut migrations = self.active_migrations.write().await;
            migrations.insert(
                migration_id.to_string(),
                MigrationStatus::Copying { progress: 100.0 }
            );
        }
        
        Ok(data)
    }
    
    // 将数据写入目标分片并验证
    async fn verify_copied_data(
        &self,
        source_shard: &str,
        target_shard: &str,
        data: &HashMap<K, V>
    ) -> Result<(), MigrationError> {
        let clients = self.shard_clients.read().await;
        let target_client = clients.get(target_shard)
            .ok_or(MigrationError::ShardNotFound(target_shard.to_string()))?;
        
        // 写入目标分片
        for (key, value) in data {
            target_client.put(key.clone(), value.clone()).await
                .map_err(|e| MigrationError::DataWriteError(e.to_string()))?;
        }
        
        // 验证写入的数据
        // ... 验证逻辑，比较源和目标数据
        
        Ok(())
    }
    
    // 更新路由配置
    async fn update_routing(
        &self,
        split_key: &K,
        target_shard: &str
    ) -> Result<(), MigrationError> {
        // 添加新的分片分区点
        self.locator.add_partition(split_key.clone(), target_shard.to_string()).await;
        
        Ok(())
    }
    
    // 获取迁移状态
    async fn get_migration_status(&self, migration_id: &str) -> Option<MigrationStatus> {
        let migrations = self.active_migrations.read().await;
        migrations.get(migration_id).cloned()
    }
    
    // 取消迁移
    async fn cancel_migration(&self, migration_id: &str) -> Result<(), MigrationError> {
        let mut migrations = self.active_migrations.write().await;
        
        if !migrations.contains_key(migration_id) {
            return Err(MigrationError::MigrationNotFound);
        }
        
        // 检查是否可以取消
        match migrations.get(migration_id) {
            Some(MigrationStatus::Switching) | Some(MigrationStatus::Completed) => {
                return Err(MigrationError::CannotCancelMigration);
            }
            _ => {
                migrations.insert(
                    migration_id.to_string(),
                    MigrationStatus::Failed { reason: "Migration cancelled".to_string() }
                );
            }
        }
        
        Ok(())
    }
}

// 迁移错误类型
#[derive(Debug, thiserror::Error)]
enum MigrationError {
    #[error("分片未找到: {0}")]
    ShardNotFound(String),
    
    #[error("迁移已存在")]
    MigrationAlreadyExists,
    
    #[error("迁移未找到")]
    MigrationNotFound,
    
    #[error("无法取消迁移")]
    CannotCancelMigration,
    
    #[error("数据访问错误: {0}")]
    DataAccessError(String),
    
    #[error("数据写入错误: {0}")]
    DataWriteError(String),
    
    #[error("数据验证错误: {0}")]
    DataVerificationError(String),
    
    #[error("路由更新错误: {0}")]
    RoutingUpdateError(String),
}

// 实现Clone
impl<K, V> Clone for ShardMigrationManager<K, V>
where
    K: Clone + Send + Sync + Ord + Serialize + DeserializeOwned + 'static,
    V: Clone + Send + Sync + Serialize + DeserializeOwned + 'static,
{
    fn clone(&self) -> Self {
        Self {
            active_migrations: self.active_migrations.clone(),
            locator: self.locator.clone(),
            shard_clients: self.shard_clients.clone(),
        }
    }
}
```

分区和数据分片是构建可扩展分布式系统的关键技术。通过这些技术，系统可以水平扩展以处理更多数据和请求，同时维持性能和可靠性。Rust的类型系统和并发安全特性使这些实现更加健壮和高效。

### 3.4 故障检测与自愈

在分布式系统中，故障是常态而非异常。设计健壮的故障检测和自动恢复机制对于保持系统可用性至关重要。

**故障检测与自愈的核心概念**：

```rust
FaultDetectionAndRecovery = {
    故障检测: "识别系统组件何时发生故障",
    心跳机制: "通过定期信号检测节点活性",
    故障分类: "区分暂时性故障和永久性故障",
    自动恢复: "系统自动从故障中恢复",
    过载保护: "防止恢复操作导致级联故障"
}
```

**Rust中的故障检测与自愈实现**：

1. **故障检测器**：

```rust
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;
use tokio::time::interval;

// 节点状态
#[derive(Debug, Clone, PartialEq, Eq)]
enum NodeStatus {
    Alive,
    Suspected,
    Confirmed,
}

// 故障检测器
struct FailureDetector {
    // 节点状态
    nodes: Arc<RwLock<HashMap<String, NodeStatus>>>,
    // 最后一次心跳时间
    last_heartbeat: Arc<RwLock<HashMap<String, Instant>>>,
    // 心跳超时设置
    heartbeat_timeout: Duration,
    // 怀疑超时设置（怀疑到确认的时间）
    suspicion_timeout: Duration,
    // 故障监听器
    failure_listeners: Arc<RwLock<Vec<Box<dyn FailureListener + Send + Sync>>>>,
    // 恢复监听器
    recovery_listeners: Arc<RwLock<Vec<Box<dyn RecoveryListener + Send + Sync>>>>,
}

// 故障监听器接口
trait FailureListener: Send + Sync {
    fn on_node_failure(&self, node_id: &str, time: Instant);
}

// 恢复监听器接口
trait RecoveryListener: Send + Sync {
    fn on_node_recovery(&self, node_id: &str, time: Instant);
}

impl FailureDetector {
    // 创建新的故障检测器
    fn new(
        heartbeat_timeout: Duration,
        suspicion_timeout: Duration
    ) -> Self {
        Self {
            nodes: Arc::new(RwLock::new(HashMap::new())),
            last_heartbeat: Arc::new(RwLock::new(HashMap::new())),
            heartbeat_timeout,
            suspicion_timeout,
            failure_listeners: Arc::new(RwLock::new(Vec::new())),
            recovery_listeners: Arc::new(RwLock::new(Vec::new())),
        }
    }
    
    // 添加节点
    async fn add_node(&self, node_id: String) {
        let mut nodes = self.nodes.write().await;
        let mut heartbeats = self.last_heartbeat.write().await;
        
        nodes.insert(node_id.clone(), NodeStatus::Alive);
        heartbeats.insert(node_id, Instant::now());
    }
    
    // 移除节点
    async fn remove_node(&self, node_id: &str) {
        let mut nodes = self.nodes.write().await;
        let mut heartbeats = self.last_heartbeat.write().await;
        
        nodes.remove(node_id);
        heartbeats.remove(node_id);
    }
    
    // 记录心跳
    async fn record_heartbeat(&self, node_id: &str) {
        let mut nodes = self.nodes.write().await;
        let mut heartbeats = self.last_heartbeat.write().await;
        
        let now = Instant::now();
        
        // 更新最后心跳时间
        heartbeats.insert(node_id.to_string(), now);
        
        // 如果节点之前被怀疑故障，现在恢复
        if let Some(status) = nodes.get_mut(node_id) {
            if *status != NodeStatus::Alive {
                *status = NodeStatus::Alive;
                
                // 触发恢复监听器
                let recovery_listeners = self.recovery_listeners.read().await;
                for listener in &*recovery_listeners {
                    listener.on_node_recovery(node_id, now);
                }
            }
        } else {
            // 如果节点不存在，添加它
            nodes.insert(node_id.to_string(), NodeStatus::Alive);
        }
    }
    
    // 检查节点状态
    async fn check_nodes(&self) {
        let now = Instant::now();
        let mut suspected = Vec::new();
        let mut confirmed = Vec::new();
        
        // 检查所有节点
        {
            let mut nodes = self.nodes.write().await;
            let heartbeats = self.last_heartbeat.read().await;
            
            for (node_id, status) in nodes.iter_mut() {
                if let Some(last_time) = heartbeats.get(node_id) {
                    let elapsed = now.duration_since(*last_time);
                    
                    match *status {
                        NodeStatus::Alive => {
                            if elapsed > self.heartbeat_timeout {
                                // 节点超时，标记为怀疑
                                *status = NodeStatus::Suspected;
                                suspected.push(node_id.clone());
                            }
                        },
                        NodeStatus::Suspected => {
                            if elapsed > self.heartbeat_timeout + self.suspicion_timeout {
                                // 怀疑超时，确认为故障
                                *status = NodeStatus::Confirmed;
                                confirmed.push(node_id.clone());
                            }
                        },
                        NodeStatus::Confirmed => {
                            // 已确认故障，无需操作
                        }
                    }
                }
            }
        }
        
        // 触发故障监听器
        if !confirmed.is_empty() {
            let failure_listeners = self.failure_listeners.read().await;
            
            for node_id in confirmed {
                for listener in &*failure_listeners {
                    listener.on_node_failure(&node_id, now);
                }
            }
        }
        
        // 记录怀疑的节点
        if !suspected.is_empty() {
            log::warn!("怀疑节点故障: {:?}", suspected);
        }
    }
    
    // 启动检测循环
    async fn start(&self) {
        let self_clone = self.clone();
        
        tokio::spawn(async move {
            let mut check_interval = interval(Duration::from_millis(500));
            
            loop {
                check_interval.tick().await;
                self_clone.check_nodes().await;
            }
        });
    }
    
    // 添加故障监听器
    async fn add_failure_listener(&self, listener: Box<dyn FailureListener + Send + Sync>) {
        let mut listeners = self.failure_listeners.write().await;
        listeners.push(listener);
    }
    
    // 添加恢复监听器
    async fn add_recovery_listener(&self, listener: Box<dyn RecoveryListener + Send + Sync>) {
        let mut listeners = self.recovery_listeners.write().await;
        listeners.push(listener);
    }
    
    // 获取节点状态
    async fn get_node_status(&self, node_id: &str) -> Option<NodeStatus> {
        let nodes = self.nodes.read().await;
        nodes.get(node_id).cloned()
    }
    
    // 获取所有活跃节点
    async fn get_alive_nodes(&self) -> HashSet<String> {
        let nodes = self.nodes.read().await;
        nodes.iter()
            .filter(|(_, status)| **status == NodeStatus::Alive)
            .map(|(id, _)| id.clone())
            .collect()
    }
}

// 实现Clone
impl Clone for FailureDetector {
    fn clone(&self) -> Self {
        Self {
            nodes: self.nodes.clone(),
            last_heartbeat: self.last_heartbeat.clone(),
            heartbeat_timeout: self.heartbeat_timeout,
            suspicion_timeout: self.suspicion_timeout,
            failure_listeners: self.failure_listeners.clone(),
            recovery_listeners: self.recovery_listeners.clone(),
        }
    }
}

// 日志监听器示例
struct LoggingListener;

impl FailureListener for LoggingListener {
    fn on_node_failure(&self, node_id: &str, time: Instant) {
        log::error!("节点故障确认: {} 在 {:?}", node_id, time);
    }
}

impl RecoveryListener for LoggingListener {
    fn on_node_recovery(&self, node_id: &str, time: Instant) {
        log::info!("节点恢复: {} 在 {:?}", node_id, time);
    }
}

// 使用示例
async fn failure_detection_example() {
    // 创建故障检测器
    let detector = FailureDetector::new(
        Duration::from_secs(5),   // 心跳超时
        Duration::from_secs(10)   // 怀疑超时
    );
    
    // 添加监听器
    detector.add_failure_listener(Box::new(LoggingListener)).await;
    detector.add_recovery_listener(Box::new(LoggingListener)).await;
    
    // 添加节点
    detector.add_node("node1".to_string()).await;
    detector.add_node("node2".to_string()).await;
    detector.add_node("node3".to_string()).await;
    
    // 启动检测
    detector.start().await;
    
    // 模拟心跳
    let detector_clone = detector.clone();
    tokio::spawn(async move {
        let mut interval = interval(Duration::from_secs(2));
        
        loop {
            interval.tick().await;
            
            // node1 和 node2 定期发送心跳
            detector_clone.record_heartbeat("node1").await;
            detector_clone.record_heartbeat("node2").await;
            
            // node3 不发送心跳，将被检测为故障
        }
    });
    
    // 等待一段时间后检查状态
    tokio::time::sleep(Duration::from_secs(20)).await;
    
    // 检查节点状态
    let status1 = detector.get_node_status("node1").await;
    let status2 = detector.get_node_status("node2").await;
    let status3 = detector.get_node_status("node3").await;
    
    println!("Node1 status: {:?}", status1);  // 应该是 Alive
    println!("Node2 status: {:?}", status2);  // 应该是 Alive
    println!("Node3 status: {:?}", status3);  // 应该是 Confirmed (故障)
    
    // 获取活跃节点
    let alive_nodes = detector.get_alive_nodes().await;
    println!("活跃节点: {:?}", alive_nodes);  // 应该包含 node1 和 node2
}
```

1. **自愈系统**：

```rust
// 自愈行动类型
enum HealingAction {
    RestartNode { node_id: String },
    ReplicateData { source: String, target: String },
    RedirectTraffic { from: String, to: String },
    AddReplica { node_id: String },
    RemoveNode { node_id: String },
}

// 自愈决策器
struct HealingStrategy {
    min_replicas: usize,
    max_recovery_attempts: usize,
    recovery_backoff: Duration,
}

// 自愈系统
struct SelfHealingSystem {
    failure_detector: Arc<FailureDetector>,
    cluster_state: Arc<RwLock<ClusterState>>,
    healing_strategy: HealingStrategy,
    recovery_history: Arc<RwLock<HashMap<String, Vec<RecoveryAttempt>>>>,
    action_executor: Arc<dyn ActionExecutor + Send + Sync>,
}

// 集群状态
struct ClusterState {
    nodes: HashMap<String, NodeInfo>,
    services: HashMap<String, ServiceInfo>,
    replicas: HashMap<String, HashSet<String>>,  // 服务ID到节点ID的映射
}

// 节点信息
struct NodeInfo {
    id: String,
    status: NodeStatus,
    resources: Resources,
    last_status_change: Instant,
}

// 服务信息
struct ServiceInfo {
    id: String,
    required_replicas: usize,
    active_replicas: HashSet<String>,  // 节点ID
    dependencies: HashSet<String>,      // 服务ID
}

// 资源信息
struct Resources {
    cpu: f64,    // CPU使用率
    memory: f64, // 内存使用率
    disk: f64,   // 磁盘使用率
}

// 恢复尝试记录
struct RecoveryAttempt {
    timestamp: Instant,
    action: HealingAction,
    result: RecoveryResult,
}

// 恢复结果
enum RecoveryResult {
    Success,
    Failure { reason: String },
    Pending,
}

// 动作执行器接口
trait ActionExecutor: Send + Sync {
    fn execute(&self, action: HealingAction) -> impl Future<Output = Result<(), ActionError>> + Send;
}

// 操作错误
#[derive(Debug, thiserror::Error)]
enum ActionError {
    #[error("节点不可达: {0}")]
    NodeUnreachable(String),
    
    #[error("资源不足: {0}")]
    InsufficientResources(String),
    
    #[error("服务错误: {0}")]
    ServiceError(String),
    
    #[error("超时: {0}")]
    Timeout(String),
    
    #[error("权限被拒绝")]
    PermissionDenied,
}

impl SelfHealingSystem {
    // 创建新的自愈系统
    fn new(
        failure_detector: Arc<FailureDetector>,
        healing_strategy: HealingStrategy,
        action_executor: Arc<dyn ActionExecutor + Send + Sync>,
    ) -> Self {
        Self {
            failure_detector,
            cluster_state: Arc::new(RwLock::new(ClusterState {
                nodes: HashMap::new(),
                services: HashMap::new(),
                replicas: HashMap::new(),
            })),
            healing_strategy,
            recovery_history: Arc::new(RwLock::new(HashMap::new())),
            action_executor,
        }
    }
    
    // 启动自愈系统
    async fn start(&self) {
        // 添加故障监听器
        let self_clone = self.clone();
        
        struct HealingListener {
            system: SelfHealingSystem,
        }
        
        impl FailureListener for HealingListener {
            fn on_node_failure(&self, node_id: &str, time: Instant) {
                let system = self.system.clone();
                let node_id = node_id.to_string();
                
                tokio::spawn(async move {
                    system.handle_node_failure(&node_id).await;
                });
            }
        }
        
        self.failure_detector.add_failure_listener(Box::new(HealingListener {
            system: self_clone,
        })).await;
        
        // 定期检查系统状态
        let self_clone = self.clone();
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_secs(30));
            
            loop {
                interval.tick().await;
                self_clone.check_system_health().await;
            }
        });
    }
    
    // 处理节点故障
    async fn handle_node_failure(&self, node_id: &str) {
        log::info!("处理节点故障: {}", node_id);
        
        // 更新集群状态
        {
            let mut state = self.cluster_state.write().await;
            
            if let Some(node) = state.nodes.get_mut(node_id) {
                node.status = NodeStatus::Confirmed;
                node.last_status_change = Instant::now();
            }
            
            // 查找受影响的服务
            let affected_services: Vec<_> = state.replicas.iter()
                .filter(|(_, nodes)| nodes.contains(node_id))
                .map(|(service_id, _)| service_id.clone())
                .collect();
                
            // 更新服务状态
            for service_id in &affected_services {
                if let Some(service) = state.services.get_mut(service_id) {
                    service.active_replicas.remove(node_id);
                }
            }
            
            // 释放故障节点上的资源引用
            for (_, nodes) in state.replicas.iter_mut() {
                nodes.remove(node_id);
            }
        }
        
        // 尝试恢复受影响的服务
        self.heal_affected_services(node_id).await;
    }
    
    // 恢复受影响的服务
    async fn heal_affected_services(&self, failed_node_id: &str) {
        // 找出需要恢复的服务
        let affected_services = {
            let state = self.cluster_state.read().await;
            
            state.services.iter()
                .filter(|(_, service)| {
                    service.active_replicas.len() < service.required_replicas
                })
                .map(|(id, _)| id.clone())
                .collect::<Vec<_>>()
        };
        
        for service_id in affected_services {
            self.heal_service(&service_id).await;
        }
    }
    
    // 恢复单个服务
    async fn heal_service(&self, service_id: &str) {
        log::info!("尝试恢复服务: {}", service_id);
        
        // 获取服务信息
        let (service, current_replicas, available_nodes) = {
            let state = self.cluster_state.read().await;
            
            let service = match state.services.get(service_id) {
                Some(s) => s.clone(),
                None => {
                    log::warn!("无法恢复未知服务: {}", service_id);
                    return;
                }
            };
            
            let current_replicas = match state.replicas.get(service_id) {
                Some(r) => r.clone(),
                None => HashSet::new(),
            };
            
            // 找出可用的健康节点
            let available_nodes: Vec<_> = state.nodes.iter()
                .filter(|(_, node)| node.status == NodeStatus::Alive)
                .filter(|(node_id, _)| !current_replicas.contains(*node_id))
                .map(|(id, node)| (id.clone(), node.resources.clone()))
                .collect();
                
            (service, current_replicas, available_nodes)
        };
        
        // 计算需要添加的副本数
        let replicas_needed = service.required_replicas.saturating_sub(current_replicas.len());
        
        if replicas_needed == 0 {
            log::info!("服务 {} 拥有足够的副本，无需恢复", service_id);
            return;
        }
        
        log::info!("服务 {} 需要 {} 个额外副本", service_id, replicas_needed);
        
        // 如果没有可用节点，记录错误
        if available_nodes.is_empty() {
            log::error!("没有可用节点来恢复服务 {}", service_id);
            return;
        }
        
        // 选择最佳节点来部署新副本
        // 这里使用简单的算法：选择资源利用率最低的节点
        let mut candidate_nodes: Vec<_> = available_nodes;
        candidate_nodes.sort_by(|(_, res_a), (_, res_b)| {
            let a_load = res_a.cpu + res_a.memory + res_a.disk;
            let b_load = res_b.cpu + res_b.memory + res_b.disk;
            a_load.partial_cmp(&b_load).unwrap_or(std::cmp::Ordering::Equal)
        });
        
        // 尝试在选定节点上添加副本
        for i in 0..replicas_needed.min(candidate_nodes.len()) {
            let (node_id, _) = &candidate_nodes[i];
            
            // 检查恢复历史，避免频繁在同一节点上重试
            let should_skip = {
                let history = self.recovery_history.read().await;
                
                if let Some(attempts) = history.get(service_id) {
                    // 检查最近的尝试
                    let recent_attempts: Vec<_> = attempts.iter()
                        .filter(|attempt| {
                            if let HealingAction::AddReplica { node_id: attempted_node } = &attempt.action {
                                attempted_node == node_id
                            } else {
                                false
                            }
                        })
                        .filter(|attempt| {
                            attempt.timestamp.elapsed() < self.healing_strategy.recovery_backoff
                        })
                        .collect();
                    
                    !recent_attempts.is_empty()
                } else {
                    false
                }
            };
            
            if should_skip {
                log::info!("跳过节点 {} 因为最近尝试过", node_id);
                continue;
            }
            
            // 执行恢复操作
            let action = HealingAction::AddReplica {
                node_id: node_id.clone(),
            };
            
            log::info!("在节点 {} 上添加服务 {} 的副本", node_id, service_id);
            
            match self.action_executor.execute(action.clone()).await {
                Ok(_) => {
                    log::info!("成功在节点 {} 上添加服务 {} 的副本", node_id, service_id);
                    
                    // 更新集群状态
                    {
                        let mut state = self.cluster_state.write().await;
                        
                        if let Some(replicas) = state.replicas.get_mut(service_id) {
                            replicas.insert(node_id.clone());
                        } else {
                            let mut new_replicas = HashSet::new();
                            new_replicas.insert(node_id.clone());
                            state.replicas.insert(service_id.to_string(), new_replicas);
                        }
                        
                        if let Some(service) = state.services.get_mut(service_id) {
                            service.active_replicas.insert(node_id.clone());
                        }
                    }
                    
                    // 记录成功的恢复尝试
                    self.record_recovery_attempt(
                        service_id,
                        RecoveryAttempt {
                            timestamp: Instant::now(),
                            action,
                            result: RecoveryResult::Success,
                        }
                    ).await;
                },
                Err(e) => {
                    log::error!("无法在节点 {} 上添加服务 {} 的副本: {}", node_id, service_id, e);
                    
                    // 记录失败的恢复尝试
                    self.record_recovery_attempt(
                        service_id,
                        RecoveryAttempt {
                            timestamp: Instant::now(),
                            action,
                            result: RecoveryResult::Failure {
                                reason: e.to_string(),
                            },
                        }
                    ).await;
                }
            }
        }
    }
    
    // 记录恢复尝试
    async fn record_recovery_attempt(&self, service_id: &str, attempt: RecoveryAttempt) {
        let mut history = self.recovery_history.write().await;
        
        history.entry(service_id.to_string())
            .or_insert_with(Vec::new)
            .push(attempt);
    }
    
    // 检查系统整体健康状态
    async fn check_system_health(&self) {
        log::debug!("检查系统健康状态");
        
        // 获取所有服务状态
        let services_to_heal = {
            let state = self.cluster_state.read().await;
            
            state.services.iter()
                .filter(|(_, service)| {
                    service.active_replicas.len() < service.required_replicas
                })
                .map(|(id, _)| id.clone())
                .collect::<Vec<_>>()
        };
        
        // 尝试恢复所有需要恢复的服务
        for service_id in services_to_heal {
            self.heal_service(&service_id).await;
        }
        
        // 检查节点负载是否均衡，必要时进行负载均衡
        self.balance_load().await;
    }
    
    // 负载均衡
    async fn balance_load(&self) {
        log::debug!("执行负载均衡检查");
        
        // 获取节点负载信息
        let (overloaded_nodes, underloaded_nodes) = {
            let state = self.cluster_state.read().await;
            
            let mut overloaded = Vec::new();
            let mut underloaded = Vec::new();
            
            // 计算平均负载
            let total_nodes = state.nodes.iter()
                .filter(|(_, node)| node.status == NodeStatus::Alive)
                .count();
                
            if total_nodes == 0 {
                return;
            }
            
            let total_load: f64 = state.nodes.iter()
                .filter(|(_, node)| node.status == NodeStatus::Alive)
                .map(|(_, node)| node.resources.cpu + node.resources.memory)
                .sum();
                
            let avg_load = total_load / (total_nodes as f64);
            let high_threshold = avg_load * 1.2;  // 20% 以上平均值视为过载
            let low_threshold = avg_load * 0.8;   // 20% 以下平均值视为负载不足
            
            for (id, node) in &state.nodes {
                if node.status != NodeStatus::Alive {
                    continue;
                }
                
                let load = node.resources.cpu + node.resources.memory;
                
                if load > high_threshold {
                    overloaded.push(id.clone());
                } else if load < low_threshold {
                    underloaded.push(id.clone());
                }
            }
            
            (overloaded, underloaded)
        };
        
        // 如果没有负载不平衡的情况，直接返回
        if overloaded_nodes.is_empty() || underloaded_nodes.is_empty() {
            return;
        }
        
        log::info!(
            "检测到负载不平衡：{} 个过载节点，{} 个低负载节点",
            overloaded_nodes.len(),
            underloaded_nodes.len()
        );
        
        // 尝试从过载节点迁移服务到低负载节点
        for overloaded_node in &overloaded_nodes {
            // 获取此节点上的服务
            let services_on_node = {
                let state = self.cluster_state.read().await;
                
                state.replicas.iter()
                    .filter(|(_, nodes)| nodes.contains(overloaded_node))
                    .map(|(service_id, _)| service_id.clone())
                    .collect::<Vec<_>>()
            };
            
            // 选择一个低负载节点迁移一个服务
            if let Some(target_node) = underloaded_nodes.first() {
                if let Some(service_id) = services_on_node.first() {
                    self.migrate_service(service_id, overloaded_node, target_node).await;
                }
            }
        }
    }
    
    // 迁移服务
    async fn migrate_service(&self, service_id: &str, from_node: &str, to_node: &str) {
        log::info!("尝试将服务 {} 从节点 {} 迁移到节点 {}", service_id, from_node, to_node);
        
        // 首先在目标节点上添加新副本
        let add_action = HealingAction::AddReplica {
            node_id: to_node.to_string(),
        };
        
        match self.action_executor.execute(add_action.clone()).await {
            Ok(_) => {
                log::info!("成功在节点 {} 上添加服务 {} 的副本", to_node, service_id);
                
                // 更新集群状态
                {
                    let mut state = self.cluster_state.write().await;
                    
                    if let Some(replicas) = state.replicas.get_mut(service_id) {
                        replicas.insert(to_node.to_string());
                    }
                    
                    if let Some(service) = state.services.get_mut(service_id) {
                        service.active_replicas.insert(to_node.to_string());
                    }
                }
                
                // 等待新副本完全启动和同步
                tokio::time::sleep(Duration::from_secs(5)).await;
                
                // 从源节点移除副本
                let remove_action = HealingAction::RedirectTraffic {
                    from: from_node.to_string(),
                    to: to_node.to_string(),
                };
                
                match self.action_executor.execute(remove_action.clone()).await {
                    Ok(_) => {
                        log::info!("成功将服务 {} 的流量从节点 {} 重定向到节点 {}", service_id, from_node, to_node);
                        
                        // 最后移除旧副本
                        let remove_replica_action = HealingAction::RemoveNode {
                            node_id: from_node.to_string(),
                        };
                        
                        match self.action_executor.execute(remove_replica_action.clone()).await {
                            Ok(_) => {
                                log::info!("成功从节点 {} 移除服务 {} 的副本", from_node, service_id);
                                
                                // 更新集群状态
                                {
                                    let mut state = self.cluster_state.write().await;
                                    
                                    if let Some(replicas) = state.replicas.get_mut(service_id) {
                                        replicas.remove(from_node);
                                    }
                                    
                                    if let Some(service) = state.services.get_mut(service_id) {
                                        service.active_replicas.remove(from_node);
                                    }
                                }
                            },
                            Err(e) => {
                                log::error!("无法从节点 {} 移除服务 {} 的副本: {}", from_node, service_id, e);
                            }
                        }
                    },
                    Err(e) => {
                        log::error!("无法重定向服务 {} 的流量: {}", service_id, e);
                    }
                }
            },
            Err(e) => {
                log::error!("无法在节点 {} 上添加服务 {} 的副本: {}", to_node, service_id, e);
            }
        }
    }
}

// 实现Clone
impl Clone for SelfHealingSystem {
    fn clone(&self) -> Self {
        Self {
            failure_detector: self.failure_detector.clone(),
            cluster_state: self.cluster_state.clone(),
            healing_strategy: HealingStrategy {
                min_replicas: self.healing_strategy.min_replicas,
                max_recovery_attempts: self.healing_strategy.max_recovery_attempts,
                recovery_backoff: self.healing_strategy.recovery_backoff,
            },
            recovery_history: self.recovery_history.clone(),
            action_executor: self.action_executor.clone(),
        }
    }
}

// 示例动作执行器
struct SimpleActionExecutor;

impl ActionExecutor for SimpleActionExecutor {
    async fn execute(&self, action: HealingAction) -> Result<(), ActionError> {
        match action {
            HealingAction::RestartNode { node_id } => {
                log::info!("模拟重启节点: {}", node_id);
                
                // 模拟一些延迟
                tokio::time::sleep(Duration::from_secs(2)).await;
                
                // 90%的概率成功
                let random = rand::random::<f64>();
                if random < 0.9 {
                    Ok(())
                } else {
                    Err(ActionError::NodeUnreachable(format!("无法连接到节点 {}", node_id)))
                }
            },
            HealingAction::ReplicateData { source, target } => {
                log::info!("模拟数据复制: {} -> {}", source, target);
                
                // 模拟复制延迟
                tokio::time::sleep(Duration::from_secs(3)).await;
                
                Ok(())
            },
            HealingAction::RedirectTraffic { from, to } => {
                log::info!("模拟流量重定向: {} -> {}", from, to);
                
                // 模拟配置更新延迟
                tokio::time::sleep(Duration::from_millis(500)).await;
                
                Ok(())
            },
            HealingAction::AddReplica { node_id } => {
                log::info!("模拟添加副本到节点: {}", node_id);
                
                // 模拟部署延迟
                tokio::time::sleep(Duration::from_secs(4)).await;
                
                // 85%的概率成功
                let random = rand::random::<f64>();
                if random < 0.85 {
                    Ok(())
                } else {
                    Err(ActionError::InsufficientResources(format!("节点 {} 资源不足", node_id)))
                }
            },
            HealingAction::RemoveNode { node_id } => {
                log::info!("模拟移除节点: {}", node_id);
                
                // 模拟清理延迟
                tokio::time::sleep(Duration::from_secs(1)).await;
                
                Ok(())
            },
        }
    }
}

// 使用示例
async fn self_healing_example() {
    // 创建故障检测器
    let detector = Arc::new(FailureDetector::new(
        Duration::from_secs(5),    // 心跳超时
        Duration::from_secs(10)    // 怀疑超时
    ));
    
    // 创建动作执行器
    let executor = Arc::new(SimpleActionExecutor);
    
    // 创建自愈系统
    let healing_system = SelfHealingSystem::new(
        detector.clone(),
        HealingStrategy {
            min_replicas: 2,
            max_recovery_attempts: 3,
            recovery_backoff: Duration::from_secs(60),
        },
        executor
    );
    
    // 初始化集群状态
    {
        let mut state = healing_system.cluster_state.write().await;
        
        // 添加节点
        for i in 1..=5 {
            let node_id = format!("node{}", i);
            state.nodes.insert(node_id.clone(), NodeInfo {
                id: node_id,
                status: NodeStatus::Alive,
                resources: Resources {
                    cpu: 0.3,
                    memory: 0.4,
                    disk: 0.2,
                },
                last_status_change: Instant::now(),
            });
        }
        
        // 添加服务
        state.services.insert("service1".to_string(), ServiceInfo {
            id: "service1".to_string(),
            required_replicas: 3,
            active_replicas: ["node1", "node2", "node3"].iter().map(|s| s.to_string()).collect(),
            dependencies: HashSet::new(),
        });
        
        state.services.insert("service2".to_string(), ServiceInfo {
            id: "service2".to_string(),
            required_replicas: 2,
            active_replicas: ["node4", "node5"].iter().map(|s| s.to_string()).collect(),
            dependencies: HashSet::new(),
        });
        
        // 设置副本映射
        let mut service1_replicas = HashSet::new();
        service1_replicas.insert("node1".to_string());
        service1_replicas.insert("node2".to_string());
        service1_replicas.insert("node3".to_string());
        state.replicas.insert("service1".to_string(), service1_replicas);
        
        let mut service2_replicas = HashSet::new();
        service2_replicas.insert("node4".to_string());
        service2_replicas.insert("node5".to_string());
        state.replicas.insert("service2".to_string(), service2_replicas);
    }
    
    // 启动检测器和自愈系统
    detector.start().await;
    healing_system.start().await;
    
    // 添加节点
    detector.add_node("node1".to_string()).await;
    detector.add_node("node2".to_string()).await;
    detector.add_node("node3".to_string()).await;
    detector.add_node("node4".to_string()).await;
    detector.add_node("node5".to_string()).await;
    
    // 模拟心跳
    let detector_clone = detector.clone();
    tokio::spawn(async move {
        let mut interval = tokio::time::interval(Duration::from_secs(1));
        
        loop {
            interval.tick().await;
            
            // 所有节点发送心跳，除了node3
            detector_clone.record_heartbeat("node1").await;
            detector_clone.record_heartbeat("node2").await;
            // 不为node3发送心跳，让它被检测为故障
            detector_clone.record_heartbeat("node4").await;
            detector_clone.record_heartbeat("node5").await;
        }
    });
    
    // 等待系统工作一段时间
    tokio::time::sleep(Duration::from_secs(30)).await;
    
    // 检查最终状态
    {
        let state = healing_system.cluster_state.read().await;
        
        println!("\n最终集群状态:");
        println!("节点状态:");
        for (id, node) in &state.nodes {
            println!("  {} - {:?}", id, node.status);
        }
        
        println!("服务状态:");
        for (id, service) in &state.services {
            println!("  {} - 副本数: {}/{}", id, service.active_replicas.len(), service.required_replicas);
            println!("    活跃副本: {:?}", service.active_replicas);
        }
    }
}
```

故障检测与自愈系统的实现展示了一个分布式系统如何自动处理节点故障和负载不平衡问题。该设计包括：

1. **故障检测**：使用心跳机制定期检查节点活性，多阶段检测减少误报。
2. **自愈策略**：根据预定义策略执行恢复操作，包括启动新副本、重定向流量等。
3. **负载均衡**：检测并解决节点负载不平衡问题。
4. **重试机制**：避免同一节点频繁重试，具有退避策略。
5. **集群状态管理**：统一管理节点和服务状态。

### 3.5 分布式事务模式

分布式系统中，事务跨越多个节点或服务，需要特殊协议确保原子性和一致性。

**分布式事务的核心概念**：

```rust
DistributedTransaction = {
    协调器: "管理事务生命周期的中央组件",
    参与者: "执行事务操作的分布式节点",
    提交协议: "确保事务原子性的协议",
    补偿操作: "回滚已执行操作的逆操作",
    数据一致性: "确保数据在所有节点上最终一致"
}
```

**Rust中的分布式事务实现**：

1. **两阶段提交协议(2PC)**：

```rust
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{mpsc, oneshot, RwLock};
use tokio::time::timeout;
use serde::{Serialize, Deserialize};
use uuid::Uuid;

// 事务状态
#[derive(Debug, Clone, PartialEq, Eq)]
enum TransactionStatus {
    Preparing,
    Prepared,
    Committing,
    Committed,
    Aborting,
    Aborted,
    TimedOut,
}

// 事务参与者响应
#[derive(Debug, Clone, Serialize, Deserialize)]
enum ParticipantResponse {
    Prepared,
    Committed,
    Aborted,
    Error(String),
}

// 事务协调器消息
#[derive(Debug, Clone, Serialize, Deserialize)]
enum CoordinatorMessage {
    Prepare {
        tx_id: String,
        operation: Operation,
    },
    Commit {
        tx_id: String,
    },
    Abort {
        tx_id: String,
    },
}

// 参与者消息
#[derive(Debug, Clone, Serialize, Deserialize)]
enum ParticipantMessage {
    PrepareResponse {
        tx_id: String,
        response: ParticipantResponse,
    },
    CommitResponse {
        tx_id: String,
        response: ParticipantResponse,
    },
    AbortResponse {
        tx_id: String,
        response: ParticipantResponse,
    },
}

// 事务操作
#[derive(Debug, Clone, Serialize, Deserialize)]
struct Operation {
    target: String,
    action: OperationAction,
}

// 操作类型
#[derive(Debug, Clone, Serialize, Deserialize)]
enum OperationAction {
    Update {
        key: String,
        value: Vec<u8>,
    },
    Delete {
        key: String,
    },
    // 其他操作类型...
}

// 事务管理器
struct TransactionManager {
    // 活跃事务
    active_transactions: Arc<RwLock<HashMap<String, TransactionState>>>,
    // 参与者客户端
    participants: Arc<RwLock<HashMap<String, ParticipantClient>>>,
    // 事务超时设置
    transaction_timeout: Duration,
    // 事务日志
    transaction_log: Arc<dyn TransactionLog>,
}

// 事务状态
struct TransactionState {
    id: String,
    status: TransactionStatus,
    participants: HashSet<String>,
    prepared_participants: HashSet<String>,
    operations: Vec<Operation>,
    start_time: Instant,
    completion_sender: Option<oneshot::Sender<Result<(), TransactionError>>>,
}

// 参与者客户端
struct ParticipantClient {
    id: String,
    sender: mpsc::Sender<(CoordinatorMessage, oneshot::Sender<ParticipantMessage>)>,
}

// 事务日志接口
trait TransactionLog: Send + Sync {
    fn log_prepare(&self, tx_id: &str, participants: &HashSet<String>) -> Result<(), LogError>;
    fn log_decision(&self, tx_id: &str, commit: bool) -> Result<(), LogError>;
    fn log_completion(&self, tx_id: &str) -> Result<(), LogError>;
    fn get_pending_transactions(&self) -> Result<Vec<(String, TransactionStatus, HashSet<String>)>, LogError>;
}

// 日志错误
#[derive(Debug, thiserror::Error)]
enum LogError {
    #[error("IO错误: {0}")]
    IoError(String),
    
    #[error("序列化错误: {0}")]
    SerializationError(String),
    
    #[error("数据库错误: {0}")]
    DatabaseError(String),
}

// 事务错误
#[derive(Debug, thiserror::Error)]
enum TransactionError {
    #[error("事务准备失败: {0}")]
    PreparationFailed(String),
    
    #[error("事务提交失败: {0}")]
    CommitFailed(String),
    
    #[error("事务中止: {0}")]
    Aborted(String),
    
    #[error("事务超时")]
    Timeout,
    
    #[error("内部错误: {0}")]
    InternalError(String),
}

impl TransactionManager {
    // 创建新的事务管理器
    fn new(
        transaction_timeout: Duration,
        transaction_log: Arc<dyn TransactionLog>,
    ) -> Self {
        Self {
            active_transactions: Arc::new(RwLock::new(HashMap::new())),
            participants: Arc::new(RwLock::new(HashMap::new())),
            transaction_timeout,
            transaction_log,
        }
    }
    
    // 注册参与者
    async fn register_participant(&self, id: String, client: ParticipantClient) {
        let mut participants = self.participants.write().await;
        participants.insert(id, client);
    }
    
    // 恢复未完成的事务（系统重启后）
    async fn recover_pending_transactions(&self) -> Result<(), TransactionError> {
        let pending_transactions = self.transaction_log.get_pending_transactions()
            .map_err(|e| TransactionError::InternalError(format!("无法获取待处理事务: {}", e)))?;
            
        log::info!("发现 {} 个待处理事务需要恢复", pending_transactions.len());
        
        for (tx_id, status, participants) in pending_transactions {
            match status {
                TransactionStatus::Prepared => {
                    // 在准备好状态但未提交的事务应该被中止
                    log::warn!("恢复中: 中止准备好但未提交的事务 {}", tx_id);
                    self.abort_transaction(&tx_id, participants).await?;
                },
                TransactionStatus::Committing => {
                    // 处于提交中的事务应该完成提交
                    log::info!("恢复中: 完成部分提交的事务 {}", tx_id);
                    self.commit_transaction(&tx_id, participants).await?;
                },
                TransactionStatus::Aborting => {
                    // 处于中止中的事务应该完成中止
                    log::info!("恢复中: 完成部分中止的事务 {}", tx_id);
                    self.abort_transaction(&tx_id, participants).await?;
                },
                _ => {
                    // 其他状态，记录但不处理
                    log::info!("恢复中: 跳过状态为 {:?} 的事务 {}", status, tx_id);
                }
            }
        }
        
        Ok(())
    }
    
    // 开始新事务
    async fn begin_transaction(&self) -> String {
        let tx_id = Uuid::new_v4().to_string();
        
        let transaction = TransactionState {
            id: tx_id.clone(),
            status: TransactionStatus::Preparing,
            participants: HashSet::new(),
            prepared_participants: HashSet::new(),
            operations: Vec::new(),
            start_time: Instant::now(),
            completion_sender: None,
        };
        
        let mut active_txs = self.active_transactions.write().await;
        active_txs.insert(tx_id.clone(), transaction);
        
        log::info!("开始新事务: {}", tx_id);
        
        tx_id
    }
    
    // 添加操作到事务
    async fn add_operation(&self, tx_id: &str, operation: Operation) -> Result<(), TransactionError> {
        let mut active_txs = self.active_transactions.write().await;
        
        let transaction = active_txs.get_mut(tx_id)
            .ok_or_else(|| TransactionError::InternalError(format!("事务不存在: {}", tx_id)))?;
            
        if transaction.status != TransactionStatus::Preparing {
            return Err(TransactionError::InternalError(
                format!("事务 {} 状态不是 Preparing，当前状态: {:?}", tx_id, transaction.status)
            ));
        }
        
        // 添加参与者
        transaction.participants.insert(operation.target.clone());
        
        // 添加操作
        transaction.operations.push(operation);
        
        Ok(())
    }
    
    // 提交事务
    async fn commit(&self, tx_id: &str) -> Result<(), TransactionError> {
        // 创建完成通道
        let (tx, rx) = oneshot::channel();
        
        // 设置完成发送者
        {
            let mut active_txs = self.active_transactions.write().await;
            
            let transaction = active_txs.get_mut(tx_id)
                .ok_or_else(|| TransactionError::InternalError(format!("事务不存在: {}", tx_id)))?;
                
            if transaction.status != TransactionStatus::Preparing {
                return Err(TransactionError::InternalError(
                    format!("事务 {} 状态不是 Preparing，当前状态: {:?}", tx_id, transaction.status)
                ));
            }
            
            transaction.completion_sender = Some(tx);
        }
        
        // 启动两阶段提交
        let self_clone = self.clone();
        let tx_id = tx_id.to_string();
        
        tokio::spawn(async move {
            if let Err(e) = self_clone.execute_two_phase_commit(&tx_id).await {
                log::error!("事务 {} 执行失败: {}", tx_id, e);
                
                // 清理事务状态
                let mut active_txs = self_clone.active_transactions.write().await;
                if let Some(transaction) = active_txs.remove(&tx_id) {
                    if let Some(sender) = transaction.completion_sender {
                        let _ = sender.send(Err(e));
                    }
                }
            }
        });
        
        // 等待事务完成或超时
        match timeout(self.transaction_timeout, rx).await {
            Ok(result) => result.unwrap_or_else(|_| Err(TransactionError::InternalError("完成通道关闭".into()))),
            Err(_) => Err(TransactionError::Timeout),
        }
    }
    
    // 执行两阶段提交
    async fn execute_two_phase_commit(&self, tx_id: &str) -> Result<(), TransactionError> {
        log::info!("执行两阶段提交: {}", tx_id);
        
        // ---- 阶段1: 准备阶段 ----
        
        // 获取事务信息
        let (participants, operations) = {
            let active_txs = self.active_transactions.read().await;
            
            let transaction = active_txs.get(tx_id)
                .ok_or_else(|| TransactionError::InternalError(format!("事务不存在: {}", tx_id)))?;
                
            (transaction.participants.clone(), transaction.operations.clone())
        };
        
        // 记录准备阶段开始
        self.transaction_log.log_prepare(tx_id, &participants)
            .map_err(|e| TransactionError::InternalError(format!("无法记录准备阶段: {}", e)))?;
        
        // 更新事务状态
        {
            let mut active_txs = self.active_transactions.write().await;
            
            if let Some(transaction) = active_txs.get_mut(tx_id) {
                transaction.status = TransactionStatus::Preparing;
            } else {
                return Err(TransactionError::InternalError(format!("事务不存在: {}", tx_id)));
            }
        }
        
        // 向所有参与者发送准备消息
        let mut prepare_results = HashMap::new();
        
        for participant_id in &participants {
            // 获取参与者的操作
            let participant_ops: Vec<_> = operations.iter()
                .filter(|op| &op.target == participant_id)
                .cloned()
                .collect();
                
            if participant_ops.is_empty() {
                continue;
            }
            
            // 准备消息
            let prepare_msg = CoordinatorMessage::Prepare {
                tx_id: tx_id.to_string(),
                operation: participant_ops[0].clone(), // 简化：每个参与者只发送一个操作
            };
            
            // 发送准备消息
            match self.send_to_participant(participant_id, prepare_msg).await {
                Ok(ParticipantMessage::PrepareResponse { response, .. }) => {
                    prepare_results.insert(participant_id.clone(), response);
                },
                Ok(_) => {
                    return Err(TransactionError::PreparationFailed(
                        format!("从参与者 {} 收到意外响应", participant_id)
                    ));
                },
                Err(e) => {
                    return Err(TransactionError::PreparationFailed(
                        format!("无法向参与者 {} 发送准备消息: {}", participant_id, e)
                    ));
                }
            }
        }
        
        // 检查所有参与者是否准备好
        let all_prepared = prepare_results.values()
            .all(|resp| *resp == ParticipantResponse::Prepared);
            
        // 更新准备好的参与者
        {
            let mut active_txs = self.active_transactions.write().await;
            
            if let Some(transaction) = active_txs.get_mut(tx_id) {
                for (participant_id, response) in &prepare_results {
                    if *response == ParticipantResponse::Prepared {
                        transaction.prepared_participants.insert(participant_id.clone());
                    }
                }
                
                // 更新事务状态
                if all_prepared {
                    transaction.status = TransactionStatus::Prepared;
                } else {
                    transaction.status = TransactionStatus::Aborting;
                }
            }
        }
        
        // ---- 阶段2: 提交或中止阶段 ----
        
        if all_prepared {
            // 所有参与者都准备好了，进行提交
            log::info!("所有参与者都准备好了，提交事务 {}", tx_id);
            
            // 记录提交决定
            self.transaction_log.log_decision(tx_id, true)
                .map_err(|e| TransactionError::InternalError(format!("无法记录提交决定: {}", e)))?;
                
            // 更新事务状态
            {
                let mut active_txs = self.active_transactions.write().await;
                
                if let Some(transaction) = active_txs.get_mut(tx_id) {
                    transaction.status = TransactionStatus::Committing;
                }
            }
            
            // 发送提交消息给所有准备好的参与者
            let prepared_participants = {
                let active_txs = self.active_transactions.read().await;
                
                active_txs.get(tx_id)
                    .map(|tx| tx.prepared_participants.clone())
                    .unwrap_or_default()
            };
            
            self.commit_transaction(tx_id, prepared_participants).await?;
            
            // 事务成功完成
            self.complete_transaction(tx_id, true).await
        } else {
            // 有参与者没有准备好，中止事务
            log::warn!("有参与者没有准备好，中止事务 {}", tx_id);
            
            // 记录中止决定
            self.transaction_log.log_decision(tx_id, false)
                .map_err(|e| TransactionError::InternalError(format!("无法记录中止决定: {}", e)))?;
                
            // 发送中止消息给所有准备好的参与者
            let prepared_participants = {
                let active_txs = self.active_transactions.read().await;
                
                active_txs.get(tx_id)
                    .map(|tx| tx.prepared_participants.clone())
                    .unwrap_or_default()
            };
            
            self.abort_transaction(tx_id, prepared_participants).await?;
            
            // 事务中止完成
            self.complete_transaction(tx_id, false).await
        }
    }
    
    // 提交事务（向所有准备好的参与者发送提交消息）
    async fn commit_transaction(
        &self,
        tx_id: &str,
        prepared_participants: HashSet<String>
    ) -> Result<(), TransactionError> {
        log::info!("发送提交消息给 {} 个参与者: {}", prepared_participants.len(), tx_id);
        
        for participant_id in &prepared_participants {
            let commit_msg = CoordinatorMessage::Commit {
                tx_id: tx_id.to_string(),
            };
            
            match self.send_to_participant(participant_id, commit_msg).await {
                Ok(ParticipantMessage::CommitResponse { response, .. }) => {
                    if response != ParticipantResponse::Committed {
                        log::error!(
                            "参与者 {} 提交事务 {} 失败: {:?}",
                            participant_id, tx_id, response
                        );
                    }
                },
                Ok(_) => {
                    log::warn!(
                        "从参与者 {} 收到意外响应类型，事务 {}",
                        participant_id, tx_id
                    );
                },
                Err(e) => {
                    log::error!(
                        "向参与者 {} 发送提交消息失败，事务 {}: {}",
                        participant_id, tx_id, e
                    );
                    // 继续提交其他参与者
                }
            }
        }
        
        Ok(())
    }
    
    // 中止事务（向所有准备好的参与者发送中止消息）
    async fn abort_transaction(
        &self,
        tx_id: &str,
        prepared_participants: HashSet<String>
    ) -> Result<(), TransactionError> {
        log::info!("发送中止消息给 {} 个参与者: {}", prepared_participants.len(), tx_id);
        
        for participant_id in &prepared_participants {
            let abort_msg = CoordinatorMessage::Abort {
                tx_id: tx_id.to_string(),
            };
            
            match self.send_to_participant(participant_id, abort_msg).await {
                Ok(ParticipantMessage::AbortResponse { response, .. }) => {
                    if response != ParticipantResponse::Aborted {
                        log::error!(
                            "参与者 {} 中止事务 {} 失败: {:?}",
                            participant_id, tx_id, response
                        );
                    }
                },
                Ok(_) => {
                    log::warn!(
                        "从参与者 {} 收到意外响应类型，事务 {}",
                        participant_id, tx_id
                    );
                },
                Err(e) => {
                    log::error!(
                        "向参与者 {} 发送中止消息失败，事务 {}: {}",
                        participant_id, tx_id, e
                    );
                    // 继续中止其他参与者
                }
            }
        }
        
        Ok(())
    }
    
    // 完成事务（更新状态和通知结果）
    async fn complete_transaction(&self, tx_id: &str, success: bool) -> Result<(), TransactionError> {
        // 记录事务完成
        self.transaction_log.log_completion(tx_id)
            .map_err(|e| TransactionError::InternalError(format!("无法记录事务完成: {}", e)))?;
            
        // 获取并移除事务
        let transaction = {
            let mut active_txs = self.active_transactions.write().await;
            active_txs.remove(tx_id)
        };
        
        // 如果事务存在，通知完成
        if let Some(transaction) = transaction {
            if let Some(sender) = transaction.completion_sender {
                if success {
                    let _ = sender.send(Ok(()));
                } else {
                    let _ = sender.send(Err(TransactionError::Aborted(
                        format!("事务 {} 被中止", tx_id)
                    )));
                }
            }
        }
        
        Ok(())
    }
    
    // 向参与者发送消息
    async fn send_to_participant(
        &self,
        participant_id: &str,
        message: CoordinatorMessage
    ) -> Result<ParticipantMessage, String> {
        let participants = self.participants.read().await;
        
        let client = participants.get(participant_id)
            .ok_or_else(|| format!("参与者不存在: {}", participant_id))?;
            
        let (tx, rx) = oneshot::channel();
        
        client.sender.send((message, tx)).await
            .map_err(|_| format!("无法发送消息给参与者: {}", participant_id))?;
            
        rx.await.map_err(|_| format!("无法接收参与者响应: {}", participant_id))
    }
}

// 参与者实现
struct TransactionParticipant {
    id: String,
    storage: Box<dyn ParticipantStorage>,
    receiver: mpsc::Receiver<(CoordinatorMessage, oneshot::Sender<ParticipantMessage>)>,
    prepared_transactions: HashMap<String, Operation>,
}

// 参与者存储接口
trait ParticipantStorage: Send + Sync {
    // 尝试准备操作（但不应用）
    fn prepare(&mut self, tx_id: &str, operation: &Operation) -> Result<(), StorageError>;
    
    // 提交准备好的操作
    fn commit(&mut self, tx_id: &str) -> Result<(), StorageError>;
    
    // 中止准备好的操作
    fn abort(&mut self, tx_id: &str) -> Result<(), StorageError>;
}

// 存储错误
#[derive(Debug, thiserror::Error)]
enum StorageError {
    #[error("准备失败: {0}")]
    PreparationFailed(String),
    
    #[error("提交失败: {0}")]
    CommitFailed(String),
    
    #[error("中止失败: {0}")]
    AbortFailed(String),
    
    #[error("事务未找到: {0}")]
    TransactionNotFound(String),
}

impl TransactionParticipant {
    // 创建新的事务参与者
    fn new(
        id: String,
        storage: Box<dyn ParticipantStorage>,
        receiver: mpsc::Receiver<(CoordinatorMessage, oneshot::Sender<ParticipantMessage>)>,
    ) -> Self {
        Self {
            id,
            storage,
            receiver,
            prepared_transactions: HashMap::new(),
        }
    }
    
    // 启动参与者处理循环
    async fn run(&mut self) {
        while let Some((message, response_sender)) = self.receiver.recv().await {
            let response = match message {
                CoordinatorMessage::Prepare { tx_id, operation } => {
                    self.handle_prepare(&tx_id, operation).await
                },
                CoordinatorMessage::Commit { tx_id } => {
                    self.handle_commit(&tx_id).await
                },
                CoordinatorMessage::Abort { tx_id } => {
                    self.handle_abort(&tx_id).await
                },
            };
            
            // 发送响应
            if let Err(e) = response_sender.send(response) {
                log::error!("无法发送响应: {:?}", e);
            }
        }
    }
    
    // 处理准备消息
    async fn handle_prepare(&mut self, tx_id: &str, operation: Operation) -> ParticipantMessage {
        log::info!("参与者 {} 收到准备请求: {}", self.id, tx_id);
        
        // 尝试准备操作
        match self.storage.prepare(tx_id, &operation) {
            Ok(()) => {
                // 记录已准备的操作
                self.prepared_transactions.insert(tx_id.to_string(), operation);
                
                ParticipantMessage::PrepareResponse {
                    tx_id: tx_id.to_string(),
                    response: ParticipantResponse::Prepared,
                }
            },
            Err(e) => {
                log::error!("参与者 {} 准备失败: {}", self.id, e);
                
                ParticipantMessage::PrepareResponse {
                    tx_id: tx_id.to_string(),
                    response: ParticipantResponse::Error(e.to_string()),
                }
            }
        }
    }
    
    // 处理提交消息
    async fn handle_commit(&mut self, tx_id: &str) -> ParticipantMessage {
        log::info!("参与者 {} 收到提交请求: {}", self.id, tx_id);
        
        // 检查事务是否已准备
        if !self.prepared_transactions.contains_key(tx_id) {
            return ParticipantMessage::CommitResponse {
                tx_id: tx_id.to_string(),
                response: ParticipantResponse::Error(format!("事务未准备: {}", tx_id)),
            };
        }
        
        // 尝试提交操作
        match self.storage.commit(tx_id) {
            Ok(()) => {
                // 移除已提交的操作
                self.prepared_transactions.remove(tx_id);
                
                ParticipantMessage::CommitResponse {
                    tx_id: tx_id.to_string(),
                    response: ParticipantResponse::Committed,
                }
            },
            Err(e) => {
                log::error!("参与者 {} 提交失败: {}", self.id, e);
                
                ParticipantMessage::CommitResponse {
                    tx_id: tx_id.to_string(),
                    response: ParticipantResponse::Error(e.to_string()),
                }
            }
        }
    }
    
    // 处理中止消息
    async fn handle_abort(&mut self, tx_id: &str) -> ParticipantMessage {
        log::info!("参与者 {} 收到中止请求: {}", self.id, tx_id);
        
        // 检查事务是否已准备
        if !self.prepared_transactions.contains_key(tx_id) {
            return ParticipantMessage::AbortResponse {
                tx_id: tx_id.to_string(),
                response: ParticipantResponse::Error(format!("事务未准备: {}", tx_id)),
            };
        }
        
        // 尝试中止操作
        match self.storage.abort(tx_id) {
            Ok(()) => {
                // 移除已中止的操作
                self.prepared_transactions.remove(tx_id);
                
                ParticipantMessage::AbortResponse {
                    tx_id: tx_id.to_string(),
                    response: ParticipantResponse::Aborted,
                }
            },
            Err(e) => {
                log::error!("参与者 {} 中止失败: {}", self.id, e);
                
                ParticipantMessage::AbortResponse {
                    tx_id: tx_id.to_string(),
                    response: ParticipantResponse::Error(e.to_string()),
                }
            }
        }
    }
}

// 实现Clone
impl Clone for TransactionManager {
    fn clone(&self) -> Self {
        Self {
            active_transactions: self.active_transactions.clone(),
            participants: self.participants.clone(),
            transaction_timeout: self.transaction_timeout,
            transaction_log: self.transaction_log.clone(),
        }
    }
}

// 使用示例
async fn two_phase_commit_example() {
    // 创建事务日志
    struct SimpleTransactionLog;
    
    impl TransactionLog for SimpleTransactionLog {
        fn log_prepare(&self, tx_id: &str, participants: &HashSet<String>) -> Result<(), LogError> {
            println!("日志: 准备事务 {} 与参与者 {:?}", tx_id, participants);
            Ok(())
        }
        
        fn log_decision(&self, tx_id: &str, commit: bool) -> Result<(), LogError> {
            println!("日志: 事务 {} 决定 {}", tx_id, if commit { "提交" } else { "中止" });
            Ok(())
        }
        
        fn log_completion(&self, tx_id: &str) -> Result<(), LogError> {
            println!("日志: 事务 {} 完成", tx_id);
            Ok(())
        }
        
        fn get_pending_transactions(&self) -> Result<Vec<(String, TransactionStatus, HashSet<String>)>, LogError> {
            // 简化实现，返回空列表
            Ok(Vec::new())
        }
    }
    
    // 创建事务管理器
    let transaction_manager = TransactionManager::new(
        Duration::from_secs(30),
        Arc::new(SimpleTransactionLog)
    );
    
    // 创建参与者存储
    struct MemoryStorage {
        data: HashMap<String, Vec<u8>>,
        prepared_operations: HashMap<String, Operation>,
    }
    
    impl MemoryStorage {
        fn new() -> Self {
            Self {
                data: HashMap::new(),
                prepared_operations: HashMap::new(),
            }
        }
    }
    
    impl ParticipantStorage for MemoryStorage {
        fn prepare(&mut self, tx_id: &str, operation: &Operation) -> Result<(), StorageError> {
            // 检查操作是否可行
            match &operation.action {
                OperationAction::Update { key, value: _ } => {
                    // 对于更新，我们只需要检查键存在（如果存在）
                    println!("存储 {}: 准备更新键 {}", operation.target, key);
                },
                OperationAction::Delete { key } => {
                    // 对于删除，键必须存在
                    if !self.data.contains_key(key) {
                        return Err(StorageError::PreparationFailed(
                            format!("键不存在: {}", key)
                        ));
                    }
                    println!("存储 {}: 准备删除键 {}", operation.target, key);
                },
            }
            
            // 记录准备好的操作
            self.prepared_operations.insert(tx_id.to_string(), operation.clone());
            
            Ok(())
        }
        
        fn commit(&mut self, tx_id: &str) -> Result<(), StorageError> {
            // 获取准备好的操作
            let operation = self.prepared_operations.get(tx_id)
                .ok_or_else(|| StorageError::TransactionNotFound(tx_id.to_string()))?
                .clone();
                
            // 应用操作
            match &operation.action {
                OperationAction::Update { key, value } => {
                    println!("存储 {}: 提交更新键 {}", operation.target, key);
                    self.data.insert(key.clone(), value.clone());
                },
                OperationAction::Delete { key } => {
                    println!("存储 {}: 提交删除键 {}", operation.target, key);
                    self.data.remove(key);
                },
            }
            
            // 移除准备好的操作
            self.prepared_operations.remove(tx_id);
            
            Ok(())
        }
        
        fn abort(&mut self, tx_id: &str) -> Result<(), StorageError> {
            // 检查事务是否存在
            if !self.prepared_operations.contains_key(tx_id) {
                return Err(StorageError::TransactionNotFound(tx_id.to_string()));
            }
            
            let operation = self.prepared_operations.get(tx_id).unwrap();
            println!("存储 {}: 中止事务 {}", operation.target, tx_id);
            
            // 移除准备好的操作
            self.prepared_operations.remove(tx_id);
            
            Ok(())
        }
    }
    
    // 创建参与者
    for id in &["participant1", "participant2", "participant3"] {
        let (tx, rx) = mpsc::channel(100);
        
        // 创建参与者客户端
        let client = ParticipantClient {
            id: id.to_string(),
            sender: tx,
        };
        
        // 注册参与者
        transaction_manager.register_participant(id.to_string(), client).await;
        
        // 创建并启动参与者
        let id_clone = id.to_string();
        let storage = Box::new(MemoryStorage::new());
        let mut participant = TransactionParticipant::new(id_clone, storage, rx);
        
        tokio::spawn(async move {
            participant.run().await;
        });
    }
    
    // 使用两阶段提交执行事务
    let tx_id = transaction_manager.begin_transaction().await;
    
    // 添加操作
    let operations = [
        Operation {
            target: "participant1".to_string(),
            action: OperationAction::Update {
                key: "user:1001".to_string(),
                value: vec![1, 2, 3, 4],
            },
        },
        Operation {
            target: "participant2".to_string(),
            action: OperationAction::Update {
                key: "order:5001".to_string(),
                value: vec![5, 6, 7, 8],
            },
        },
    ];
    
    for op in &operations {
        transaction_manager.add_operation(&tx_id, op.clone()).await.unwrap();
    }
    
    // 提交事务
    match transaction_manager.commit(&tx_id).await {
        Ok(()) => {
            println!("事务 {} 成功提交", tx_id);
        },
        Err(e) => {
            println!("事务 {} 提交失败: {}", tx_id, e);
        }
    }
    
    // 等待一会儿让所有日志打印出来
    tokio::time::sleep(Duration::from_secs(1)).await;
}
```

1. **Saga模式**：

Saga模式是一种长事务解决方案，将分布式事务分解为本地事务序列，并为每个本地事务定义补偿操作。

```rust
// Saga事务管理器
struct SagaManager {
    // 活跃Sagas
    active_sagas: Arc<RwLock<HashMap<String, SagaState>>>,
    // 参与者客户端
    participants: Arc<RwLock<HashMap<String, SagaParticipantClient>>>,
    // 事务超时设置
    transaction_timeout: Duration,
    // Saga日志
    saga_log: Arc<dyn SagaLog>,
}

// Saga状态
struct SagaState {
    id: String,
    status: SagaStatus,
    steps: Vec<SagaStep>,
    current_step: usize,
    start_time: Instant,
    completion_sender: Option<oneshot::Sender<Result<(), SagaError>>>,
}

// Saga步骤
struct SagaStep {
    participant: String,
    action: SagaAction,
    compensation: SagaAction,
    status: StepStatus,
}

// Saga动作
#[derive(Clone, Debug, Serialize, Deserialize)]
struct SagaAction {
    name: String,
    params: HashMap<String, Value>,
}

// 步骤状态
#[derive(Clone, Debug, PartialEq, Eq)]
enum StepStatus {
    Pending,
    Completed,
    Failed(String),
    Compensated,
    CompensationFailed(String),
}

// Saga状态
#[derive(Clone, Debug, PartialEq, Eq)]
enum SagaStatus {
    Running,
    Compensating,
    Completed,
    Failed(String),
    Aborted,
}

// Saga日志接口
trait SagaLog: Send + Sync {
    fn log_start(&self, saga_id: &str, steps: &[SagaStep]) -> Result<(), LogError>;
    fn log_step_completed(&self, saga_id: &str, step_index: usize) -> Result<(), LogError>;
    fn log_step_failed(&self, saga_id: &str, step_index: usize, reason: &str) -> Result<(), LogError>;
    fn log_saga_completed(&self, saga_id: &str) -> Result<(), LogError>;
    fn log_saga_failed(&self, saga_id: &str, reason: &str) -> Result<(), LogError>;
    fn log_compensation_started(&self, saga_id: &str) -> Result<(), LogError>;
    fn log_step_compensated(&self, saga_id: &str, step_index: usize) -> Result<(), LogError>;
    fn log_compensation_failed(&self, saga_id: &str, step_index: usize, reason: &str) -> Result<(), LogError>;
    fn get_pending_sagas(&self) -> Result<Vec<(String, Vec<SagaStep>, usize)>, LogError>;
}

// Saga错误
#[derive(Debug, thiserror::Error)]
enum SagaError {
    #[error("Saga执行失败: {0}")]
    ExecutionFailed(String),
    
    #[error("补偿失败: {0}")]
    CompensationFailed(String),
    
    #[error("Saga超时")]
    Timeout,
    
    #[error("内部错误: {0}")]
    InternalError(String),
}

// Saga参与者客户端
struct SagaParticipantClient {
    id: String,
    sender: mpsc::Sender<(SagaRequest, oneshot::Sender<SagaResponse>)>,
}

// Saga请求
#[derive(Debug, Clone, Serialize, Deserialize)]
enum SagaRequest {
    ExecuteAction {
        saga_id: String,
        action: SagaAction,
    },
    CompensateAction {
        saga_id: String,
        action: SagaAction,
    },
}

// Saga响应
#[derive(Debug, Clone, Serialize, Deserialize)]
enum SagaResponse {
    ActionCompleted,
    ActionFailed(String),
    CompensationCompleted,
    CompensationFailed(String),
}

impl SagaManager {
    // 创建新的Saga管理器
    fn new(
        transaction_timeout: Duration,
        saga_log: Arc<dyn SagaLog>,
    ) -> Self {
        Self {
            active_sagas: Arc::new(RwLock::new(HashMap::new())),
            participants: Arc::new(RwLock::new(HashMap::new())),
            transaction_timeout,
            saga_log,
        }
    }
    
    // 注册参与者
    async fn register_participant(&self, id: String, client: SagaParticipantClient) {
        let mut participants = self.participants.write().await;
        participants.insert(id, client);
    }
    
    // 开始新Saga
    async fn begin_saga(&self, steps: Vec<SagaStep>) -> String {
        let saga_id = Uuid::new_v4().to_string();
        
        // 创建Saga状态
        let saga = SagaState {
            id: saga_id.clone(),
            status: SagaStatus::Running,
            steps,
            current_step: 0,
            start_time: Instant::now(),
            completion_sender: None,
        };
        
        // 记录Saga开始
        self.saga_log.log_start(&saga_id, &saga.steps)
            .expect("无法记录Saga开始");
            
        // 保存Saga状态
        let mut active_sagas = self.active_sagas.write().await;
        active_sagas.insert(saga_id.clone(), saga);
        
        log::info!("开始新Saga: {}", saga_id);
        
        saga_id
    }
    
    // 执行Saga
    async fn execute(&self, saga_id: &str) -> Result<(), SagaError> {
        // 创建完成通道
        let (tx, rx) = oneshot::channel();
        
        // 设置完成发送者
        {
            let mut active_sagas = self.active_sagas.write().await;
            
            let saga = active_sagas.get_mut(saga_id)
                .ok_or_else(|| SagaError::InternalError(format!("Saga不存在: {}", saga_id)))?;
                
            saga.completion_sender = Some(tx);
        }
        
        // 启动Saga执行
        let self_clone = self.clone();
        let saga_id = saga_id.to_string();
        
        tokio::spawn(async move {
            self_clone.execute_saga(&saga_id).await;
        });
        
        // 等待Saga完成或超时
        match timeout(self.transaction_timeout, rx).await {
            Ok(result) => result.unwrap_or_else(|_| Err(SagaError::InternalError("完成通道关闭".into()))),
            Err(_) => Err(SagaError::Timeout),
        }
    }
    
    // 执行Saga步骤
    async fn execute_saga(&self, saga_id: &str) {
        log::info!("执行Saga: {}", saga_id);
        
        loop {
            // 获取当前步骤
            let (current_step, participant_id, action, completed) = {
                let active_sagas = self.active_sagas.read().await;
                
                let saga = match active_sagas.get(saga_id) {
                    Some(s) => s,
                    None => {
                        log::error!("Saga不存在: {}", saga_id);
                        return;
                    }
                };
                
                // 检查Saga是否已完成
                if saga.status == SagaStatus::Completed || 
                   matches!(saga.status, SagaStatus::Failed(_)) ||
                   saga.status == SagaStatus::Aborted {
                    return;
                }
                
                // 如果所有步骤都已完成，标记Saga为已完成
                if saga.current_step >= saga.steps.len() {
                    break;
                }
                
                // 获取当前步骤
                let step = &saga.steps[saga.current_step];
                
                (
                    saga.current_step,
                    step.participant.clone(),
                    step.action.clone(),
                    step.status == StepStatus::Completed
                )
            };
            
            // 如果当前步骤已完成，移动到下一步
            if completed {
                let mut active_sagas = self.active_sagas.write().await;
                
                let saga = match active_sagas.get_mut(saga_id) {
                    Some(s) => s,
                    None => {
                        log::error!("Saga不存在: {}", saga_id);
                        return;
                    }
                };
                
                saga.current_step += 1;
                continue;
            }
            
            // 获取参与者客户端
            let participant_client = {
                let participants = self.participants.read().await;
                
                match participants.get(&participant_id) {
                    Some(client) => client.clone(),
                    None => {
                        log::error!("参与者不存在: {}", participant_id);
                        
                        // 将步骤标记为失败
                        self.handle_step_failure(
                            saga_id,
                            current_step,
                            format!("参与者不存在: {}", participant_id)
                        ).await;
                        
                        return;
                    }
                }
            };
            
            // 执行步骤动作
            let request = SagaRequest::ExecuteAction {
                saga_id: saga_id.to_string(),
                action,
            };
            
            let response = match self.send_to_participant(&participant_client, request).await {
                Ok(resp) => resp,
                Err(e) => {
                    log::error!("无法发送请求给参与者 {}: {}", participant_id, e);
                    
                    // 将步骤标记为失败
                    self.handle_step_failure(
                        saga_id,
                        current_step,
                        format!("无法发送请求给参与者: {}", e)
                    ).await;
                    
                    return;
                }
            };
            
            // 处理响应
            match response {
                SagaResponse::ActionCompleted => {
                    log::info!("Saga {} 步骤 {} 完成", saga_id, current_step);
                    
                    // 更新步骤状态
                    let mut active_sagas = self.active_sagas.write().await;
                    
                    let saga = match active_sagas.get_mut(saga_id) {
                        Some(s) => s,
                        None => return,
                    };
                    
                    if current_step < saga.steps.len() {
                        saga.steps[current_step].status = StepStatus::Completed;
                    }
                    
                    // 记录步骤完成
                    if let Err(e) = self.saga_log.log_step_completed(saga_id, current_step) {
                        log::error!("无法记录步骤完成: {}", e);
                    }
                    
                    // 移动到下一步
                    saga.current_step += 1;
                },
                SagaResponse::ActionFailed(reason) => {
                    log::error!("Saga {} 步骤 {} 失败: {}", saga_id, current_step, reason);
                    
                    // 处理步骤失败
                    self.handle_step_failure(
                        saga_id,
                        current_step,
                        reason
                    ).await;
                    
                    return;
                },
                _ => {
                    log::error!("从参与者收到意外响应类型");
                    
                    // 处理步骤失败
                    self.handle_step_failure(
                        saga_id,
                        current_step,
                        "意外响应类型".to_string()
                    ).await;
                    
                    return;
                }
            }
        }
        
        // 所有步骤都已完成，标记Saga为已完成
        self.complete_saga(saga_id).await;
    }
    
    // 处理步骤失败
    async fn handle_step_failure(&self, saga_id: &str, step_index: usize, reason: String) {
        log::error!("Saga {} 步骤 {} 失败: {}", saga_id, step_index, reason);
        
        // 更新步骤状态
        {
            let mut active_sagas = self.active_sagas.write().await;
            
            let saga = match active_sagas.get_mut(saga_id) {
                Some(s) => s,
                None => return,
            };
            
            if step_index < saga.steps.len() {
                saga.steps[step_index].status = StepStatus::Failed(reason.clone());
            }
            
            // 更新Saga状态为补偿中
            saga.status = SagaStatus::Compensating;
        }
        
        // 记录步骤失败
        if let Err(e) = self.saga_log.log_step_failed(saga_id, step_index, &reason) {
            log::error!("无法记录步骤失败: {}", e);
        }
        
        // 记录开始补偿
        if let Err(e) = self.saga_log.log_compensation_started(saga_id) {
            log::error!("无法记录开始补偿: {}", e);
        }
        
        // 开始补偿
        self.compensate_saga(saga_id, step_index).await;
    }
    
    // 补偿Saga
    async fn compensate_saga(&self, saga_id: &str, failed_step: usize) {
        log::info!("开始补偿Saga {}, 从步骤 {} 开始", saga_id, failed_step);
        
        // 获取需要补偿的步骤
        let steps_to_compensate = {
            let active_sagas = self.active_sagas.read().await;
            
            let saga = match active_sagas.get(saga_id) {
                Some(s) => s,
                None => return,
            };
            
            // 收集已完成的步骤（按相反顺序）
            let mut steps = Vec::new();
            for i in (0..failed_step).rev() {
                if saga.steps[i].status == StepStatus::Completed {
                    steps.push((i, saga.steps[i].clone()));
                }
            }
            
            steps
        };
        
        // 逐个补偿步骤（按相反顺序）
        let mut all_compensated = true;
        
        for (step_index, step) in steps_to_compensate {
            log::info!("补偿Saga {} 步骤 {}", saga_id, step_index);
            
            // 获取参与者客户端
            let participant_client = {
                let participants = self.participants.read().await;
                
                match participants.get(&step.participant) {
                    Some(client) => client.clone(),
                    None => {
                        log::error!("补偿时参与者不存在: {}", step.participant);
                        
                        // 标记补偿失败
                        let mut active_sagas = self.active_sagas.write().await;
                        
                        if let Some(saga) = active_sagas.get_mut(saga_id) {
                            saga.steps[step_index].status = StepStatus::CompensationFailed(
                                format!("参与者不存在: {}", step.participant)
                            );
                        }
                        
                        all_compensated = false;
                        continue;
                    }
                }
            };
            
            // 执行补偿动作
            let request = SagaRequest::CompensateAction {
                saga_id: saga_id.to_string(),
                action: step.compensation,
            };
            
            let response = match self.send_to_participant(&participant_client, request).await {
                Ok(resp) => resp,
                Err(e) => {
                    log::error!(
                        "无法发送补偿请求给参与者 {}: {}",
                        step.participant, e
                    );
                    
                    // 标记补偿失败
                    let mut active_sagas = self.active_sagas.write().await;
                    
                    if let Some(saga) = active_sagas.get_mut(saga_id) {
                        saga.steps[step_index].status = StepStatus::CompensationFailed(
                            format!("无法发送补偿请求: {}", e)
                        );
                    }
                    
                    all_compensated = false;
                    continue;
                }
            };
            
            // 处理响应
            match response {
                SagaResponse::CompensationCompleted => {
                    log::info!("Saga {} 步骤 {} 补偿完成", saga_id, step_index);
                    
                    // 更新步骤状态
                    let mut active_sagas = self.active_sagas.write().await;
                    
                    if let Some(saga) = active_sagas.get_mut(saga_id) {
                        saga.steps[step_index].status = StepStatus::Compensated;
                    }
                    
                    // 记录步骤补偿完成
                    if let Err(e) = self.saga_log.log_step_compensated(saga_id, step_index) {
                        log::error!("无法记录步骤补偿完成: {}", e);
                    }
                },
                SagaResponse::CompensationFailed(reason) => {
                    log::error!(
                        "Saga {} 步骤 {} 补偿失败: {}",
                        saga_id, step_index, reason
                    );
                    
                    // 更新步骤状态
                    let mut active_sagas = self.active_sagas.write().await;
                    
                    if let Some(saga) = active_sagas.get_mut(saga_id) {
                        saga.steps[step_index].status = StepStatus::CompensationFailed(reason.clone());
                    }
                    
                    // 记录步骤补偿失败
                    if let Err(e) = self.saga_log.log_compensation_failed(saga_id, step_index, &reason) {
                        log::error!("无法记录步骤补偿失败: {}", e);
                    }
                    
                    all_compensated = false;
                },
                _ => {
                    log::error!("从参与者收到意外补偿响应类型");
                    
                    // 更新步骤状态
                    let mut active_sagas = self.active_sagas.write().await;
                    
                    if let Some(saga) = active_sagas.get_mut(saga_id) {
                        saga.steps[step_index].status = StepStatus::CompensationFailed(
                            "意外响应类型".to_string()
                        );
                    }
                    
                    all_compensated = false;
                }
            }
        }
        
        // 补偿完成后，根据结果更新Saga状态
        {
            let mut active_sagas = self.active_sagas.write().await;
            
            let saga = match active_sagas.get_mut(saga_id) {
                Some(s) => s,
                None => return,
            };
            
            if all_compensated {
                saga.status = SagaStatus::Aborted;
                log::info!("Saga {} 成功中止（所有步骤都已补偿）", saga_id);
            } else {
                let reason = format!("Saga部分补偿失败");
                saga.status = SagaStatus::Failed(reason.clone());
                log::error!("Saga {} 失败: {}", saga_id, reason);
                
                // 记录Saga失败
                if let Err(e) = self.saga_log.log_saga_failed(saga_id, &reason) {
                    log::error!("无法记录Saga失败: {}", e);
                }
            }
            
            // 通知完成
            if let Some(sender) = saga.completion_sender.take() {
                if all_compensated {
                    let _ = sender.send(Err(SagaError::ExecutionFailed(
                        format!("Saga已中止（已补偿）")
                    )));
                } else {
                    let _ = sender.send(Err(SagaError::CompensationFailed(
                        format!("Saga补偿部分失败")
                    )));
                }
            }
        }
    }
    
    // 完成Saga
    async fn complete_saga(&self, saga_id: &str) {
        log::info!("Saga {} 所有步骤都已完成", saga_id);
        
        // 更新Saga状态
        let completion_sender = {
            let mut active_sagas = self.active_sagas.write().await;
            
            let saga = match active_sagas.get_mut(saga_id) {
                Some(s) => s,
                None => return,
            };
            
            saga.status = SagaStatus::Completed;
            saga.completion_sender.take()
        };
        
        // 记录Saga完成
        if let Err(e) = self.saga_log.log_saga_completed(saga_id) {
            log::error!("无法记录Saga完成: {}", e);
        }
        
        // 通知完成
        if let Some(sender) = completion_sender {
            let _ = sender.send(Ok(()));
        }
    }
    
    // 向参与者发送消息
    async fn send_to_participant(
        &self,
        client: &SagaParticipantClient,
        request: SagaRequest
    ) -> Result<SagaResponse, String> {
        let (tx, rx) = oneshot::channel();
        
        client.sender.send((request, tx)).await
            .map_err(|_| format!("无法发送消息给参与者: {}", client.id))?;
            
        rx.await.map_err(|_| format!("无法接收参与者响应: {}", client.id))
    }
}

// 参与者实现
struct SagaParticipant {
    id: String,
    storage: Box<dyn SagaParticipantStorage>,
    receiver: mpsc::Receiver<(SagaRequest, oneshot::Sender<SagaResponse>)>,
}

// 参与者存储接口
trait SagaParticipantStorage: Send + Sync {
    // 执行动作
    fn execute_action(&mut self, saga_id: &str, action: &SagaAction) -> Result<(), StorageError>;
    
    // 补偿动作
    fn compensate_action(&mut self, saga_id: &str, action: &SagaAction) -> Result<(), StorageError>;
}

impl SagaParticipant {
    // 创建新的Saga参与者
    fn new(
        id: String,
        storage: Box<dyn SagaParticipantStorage>,
        receiver: mpsc::Receiver<(SagaRequest, oneshot::Sender<SagaResponse>)>,
    ) -> Self {
        Self {
            id,
            storage,
            receiver,
        }
    }
    
    // 启动参与者处理循环
    async fn run(&mut self) {
        while let Some((request, response_sender)) = self.receiver.recv().await {
            let response = match request {
                SagaRequest::ExecuteAction { saga_id, action } => {
                    self.handle_execute(&saga_id, &action).await
                },
                SagaRequest::CompensateAction { saga_id, action } => {
                    self.handle_compensate(&saga_id, &action).await
                },
            };
            
            // 发送响应
            if let Err(e) = response_sender.send(response) {
                log::error!("无法发送响应: {:?}", e);
            }
        }
    }
    
    // 处理执行请求
    async fn handle_execute(&mut self, saga_id: &str, action: &SagaAction) -> SagaResponse {
        log::info!("参与者 {} 执行动作 {} for saga {}", self.id, action.name, saga_id);
        
        match self.storage.execute_action(saga_id, action) {
            Ok(()) => {
                SagaResponse::ActionCompleted
            },
            Err(e) => {
                log::error!("参与者 {} 执行失败: {}", self.id, e);
                SagaResponse::ActionFailed(e.to_string())
            }
        }
    }
    
    // 处理补偿请求
    async fn handle_compensate(&mut self, saga_id: &str, action: &SagaAction) -> SagaResponse {
        log::info!("参与者 {} 补偿动作 {} for saga {}", self.id, action.name, saga_id);
        
        match self.storage.compensate_action(saga_id, action) {
            Ok(()) => {
                SagaResponse::CompensationCompleted
            },
            Err(e) => {
                log::error!("参与者 {} 补偿失败: {}", self.id, e);
                SagaResponse::CompensationFailed(e.to_string())
            }
        }
    }
}

// 实现Clone
impl Clone for SagaManager {
    fn clone(&self) -> Self {
        Self {
            active_sagas: self.active_sagas.clone(),
            participants: self.participants.clone(),
            transaction_timeout: self.transaction_timeout,
            saga_log: self.saga_log.clone(),
        }
    }
}

impl Clone for SagaParticipantClient {
    fn clone(&self) -> Self {
        Self {
            id: self.id.clone(),
            sender: self.sender.clone(),
        }
    }
}

// 使用示例
async fn saga_pattern_example() {
    // 创建Saga日志
    struct SimpleSagaLog;
    
    impl SagaLog for SimpleSagaLog {
        fn log_start(&self, saga_id: &str, steps: &[SagaStep]) -> Result<(), LogError> {
            println!("日志: 开始Saga {} 有 {} 个步骤", saga_id, steps.len());
            Ok(())
        }
        
        fn log_step_completed(&self, saga_id: &str, step_index: usize) -> Result<(), LogError> {
            println!("日志: Saga {} 步骤 {} 完成", saga_id, step_index);
            Ok(())
        }
        
        fn log_step_failed(&self, saga_id: &str, step_index: usize, reason: &str) -> Result<(), LogError> {
            println!("日志: Saga {} 步骤 {} 失败: {}", saga_id, step_index, reason);
            Ok(())
        }
        
        fn log_saga_completed(&self, saga_id: &str) -> Result<(), LogError> {
            println!("日志: Saga {} 完成", saga_id);
            Ok(())
        }
        
        fn log_saga_failed(&self, saga_id: &str, reason: &str) -> Result<(), LogError> {
            println!("日志: Saga {} 失败: {}", saga_id, reason);
            Ok(())
        }
        
        fn log_compensation_started(&self, saga_id: &str) -> Result<(), LogError> {
            println!("日志: Saga {} 开始补偿", saga_id);
            Ok(())
        }
        
        fn log_step_compensated(&self, saga_id: &str, step_index: usize) -> Result<(), LogError> {
            println!("日志: Saga {} 步骤 {} 补偿完成", saga_id, step_index);
            Ok(())
        }
        
        fn log_compensation_failed(&self, saga_id: &str, step_index: usize, reason: &str) -> Result<(), LogError> {
            println!("日志: Saga {} 步骤 {} 补偿失败: {}", saga_id, step_index, reason);
            Ok(())
        }
        
        fn get_pending_sagas(&self) -> Result<Vec<(String, Vec<SagaStep>, usize)>, LogError> {
            // 简化实现，返回空列表
            Ok(Vec::new())
        }
    }
    
    // 创建Saga管理器
    let saga_manager = SagaManager::new(
        Duration::from_secs(30),
        Arc::new(SimpleSagaLog)
    );
    
    // 创建参与者存储
    struct MemorySagaStorage {
        id: String,
        data: HashMap<String, HashMap<String, Vec<u8>>>,
    }
    
    impl MemorySagaStorage {
        fn new(id: &str) -> Self {
            Self {
                id: id.to_string(),
                data: HashMap::new(),
            }
        }
    }
    
    impl SagaParticipantStorage for MemorySagaStorage {
        fn execute_action(&mut self, saga_id: &str, action: &SagaAction) -> Result<(), StorageError> {
            println!("存储 {}: 执行动作 {} for saga {}", self.id, action.name, saga_id);
            
            // 为Saga创建数据容器
            let saga_data = self.data.entry(saga_id.to_string()).or_insert_with(HashMap::new);
            
            // 根据动作类型执行
            match action.name.as_str() {
                "create" => {
                    if let (Some(key), Some(value)) = (
                        action.params.get("key").and_then(|v| v.as_str()).map(|s| s.to_string()),
                        action.params.get("value").and_then(|v| v.as_bytes().map(|b| b.to_vec()))
                    ) {
                        saga_data.insert(key, value);
                        Ok(())
                    } else {
                        Err(StorageError::PreparationFailed("缺少必要参数".into()))
                    }
                },
                "update" => {
                    if let (Some(key), Some(value)) = (
                        action.params.get("key").and_then(|v| v.as_str()).map(|s| s.to_string()),
                        action.params.get("value").and_then(|v| v.as_bytes().map(|b| b.to_vec()))
                    ) {
                        if !saga_data.contains_key(&key) {
                            return Err(StorageError::PreparationFailed(format!("键不存在: {}", key)));
                        }
                        saga_data.insert(key, value);
                        Ok(())
                    } else {
                        Err(StorageError::PreparationFailed("缺少必要参数".into()))
                    }
                },
                "delete" => {
                    if let Some(key) = action.params.get("key").and_then(|v| v.as_str()) {
                        if saga_data.remove(key).is_none() {
                            return Err(StorageError::PreparationFailed(format!("键不存在: {}", key)));
                        }
                        Ok(())
                    } else {
                        Err(StorageError::PreparationFailed("缺少必要参数".into()))
                    }
                },
                _ => Err(StorageError::PreparationFailed(format!("未知动作: {}", action.name))),
            }
        }
        
        fn compensate_action(&mut self, saga_id: &str, action: &SagaAction) -> Result<(), StorageError> {
            println!("存储 {}: 补偿动作 {} for saga {}", self.id, action.name, saga_id);
            
            // 获取Saga数据容器
            let saga_data = match self.data.get_mut(saga_id) {
                Some(data) => data,
                None => return Ok(()),  // 如果没有数据，不需要补偿
            };
            
            // 根据动作类型执行补偿
            match action.name.as_str() {
                "undo_create" => {
                    if let Some(key) = action.params.get("key").and_then(|v| v.as_str()) {
                        saga_data.remove(key);
                        Ok(())
                    } else {
                        Err(StorageError::AbortFailed("缺少必要参数".into()))
                    }
                },
                "undo_update" => {
                    if let (Some(key), Some(original_value)) = (
                        action.params.get("key").and_then(|v| v.as_str()).map(|s| s.to_string()),
                        action.params.get("original_value").and_then(|v| v.as_bytes().map(|b| b.to_vec()))
                    ) {
                        saga_data.insert(key, original_value);
                        Ok(())
                    } else {
                        Err(StorageError::AbortFailed("缺少必要参数".into()))
                    }
                },
                "undo_delete" => {
                    if let (Some(key), Some(value)) = (
                        action.params.get("key").and_then(|v| v.as_str()).map(|s| s.to_string()),
                        action.params.get("value").and_then(|v| v.as_bytes().map(|b| b.to_vec()))
                    ) {
                        saga_data.insert(key, value);
                        Ok(())
                    } else {
                        Err(StorageError::AbortFailed("缺少必要参数".into()))
                    }
                },
                _ => Err(StorageError::AbortFailed(format!("未知补偿动作: {}", action.name))),
            }
        }
    }
    
    // 创建参与者
    for id in &["order_service", "payment_service", "inventory_service"] {
        let (tx, rx) = mpsc::channel(100);
        
        // 创建参与者客户端
        let client = SagaParticipantClient {
            id: id.to_string(),
            sender: tx,
        };
        
        // 注册参与者
        saga_manager.register_participant(id.to_string(), client).await;
        
        // 创建并启动参与者
        let id_clone = id.to_string();
        let storage = Box::new(MemorySagaStorage::new(id));
        let mut participant = SagaParticipant::new(id_clone, storage, rx);
        
        tokio::spawn(async move {
            participant.run().await;
        });
    }
    
    // 创建Saga步骤
    let mut create_order_params = HashMap::new();
    create_order_params.insert("key".to_string(), serde_json::Value::String("order:1001".to_string()));
    create_order_params.insert("value".to_string(), serde_json::Value::String(r#"{"id":"1001","status":"pending"}"#.to_string()));
    
    let mut undo_create_order_params = HashMap::new();
    undo_create_order_params.insert("key".to_string(), serde_json::Value::String("order:1001".to_string()));
    
    let mut payment_params = HashMap::new();
    payment_params.insert("key".to_string(), serde_json::Value::String("payment:1001".to_string()));
    payment_params.insert("value".to_string(), serde_json::Value::String(r#"{"orderId":"1001","amount":100}"#.to_string()));
    
    let mut undo_payment_params = HashMap::new();
    undo_payment_params.insert("key".to_string(), serde_json::Value::String("payment:1001".to_string()));
    
    let mut update_inventory_params = HashMap::new();
    update_inventory_params.insert("key".to_string(), serde_json::Value::String("product:101".to_string()));
    update_inventory_params.insert("value".to_string(), serde_json::Value::String(r#"{"stock":50}"#.to_string()));
    
    // 使这个步骤失败
    update_inventory_params.insert("should_fail".to_string(), serde_json::Value::Bool(true));
    
    let mut undo_inventory_params = HashMap::new();
    undo_inventory_params.insert("key".to_string(), serde_json::Value::String("product:101".to_string()));
    undo_inventory_params.insert("original_value".to_string(), serde_json::Value::String(r#"{"stock":51}"#.to_string()));
    
    let steps = vec![
        SagaStep {
            participant: "order_service".to_string(),
            action: SagaAction {
                name: "create".to_string(),
                params: create_order_params,
            },
            compensation: SagaAction {
                name: "undo_create".to_string(),
                params: undo_create_order_params,
            },
            status: StepStatus::Pending,
        },
        SagaStep {
            participant: "payment_service".to_string(),
            action: SagaAction {
                name: "create".to_string(),
                params: payment_params,
            },
            compensation: SagaAction {
                name: "undo_create".to_string(),
                params: undo_payment_params,
            },
            status: StepStatus::Pending,
        },
        SagaStep {
            participant: "inventory_service".to_string(),
            action: SagaAction {
                name: "update".to_string(),
                params: update_inventory_params,
            },
            compensation: SagaAction {
                name: "undo_update".to_string(),
                params: undo_inventory_params,
            },
            status: StepStatus::Pending,
        },
    ];
    
    // 启动Saga
    let saga_id = saga_manager.begin_saga(steps).await;
    
    // 执行Saga
    match saga_manager.execute(&saga_id).await {
        Ok(()) => {
            println!("Saga {} 成功完成", saga_id);
        },
        Err(e) => {
            println!("Saga {} 执行失败: {}", saga_id, e);
        }
    }
    
    // 等待一会儿让所有日志打印出来
    tokio::time::sleep(Duration::from_secs(1)).await;
}
```

分布式事务是分布式系统中的复杂挑战。上述实现展示了两种常用的分布式事务模式：

1. **两阶段提交(2PC)**：通过准备和提交两个阶段确保事务的原子性，适用于需要强一致性的场景。

2. **Saga模式**：将长事务分解为一系列本地事务，每个本地事务都有相应的补偿操作，适用于长时间运行的事务和需要高可用性的场景。

这些模式各有优缺点：

- 2PC提供了强一致性保证，但可能导致资源锁定和协调器成为单点故障。
- Saga提供了更高的可用性和并行性，但实现复杂且仅保证最终一致性。

在实际应用中，系统设计人员需要根据业务需求和系统特性选择合适的事务模式。

## 4. Rust分布式系统组件

### 4.1 网络库与协议实现

分布式系统的基础是可靠的网络通信。Rust生态系统提供了多种高性能网络库，支持不同的通信协议和模式。

**网络通信的核心挑战**：

```rust
NetworkChallenges = {
    可靠性: "处理网络失败和消息丢失",
    性能: "最大化吞吐量和最小化延迟",
    安全性: "加密和认证通信",
    可扩展性: "处理大量连接",
    协议兼容性: "与现有系统集成"
}
```

**Rust中的主要网络库**：

1. **Tokio**：异步运行时和网络库

```rust
use tokio::net::{TcpListener, TcpStream};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use std::error::Error;

// 异步TCP服务器
async fn run_tcp_server() -> Result<(), Box<dyn Error>> {
    // 绑定监听器
    let listener = TcpListener::bind("127.0.0.1:8080").await?;
    println!("服务器监听于 127.0.0.1:8080");
    
    loop {
        // 接受连接
        let (socket, addr) = listener.accept().await?;
        println!("接受连接来自: {}", addr);
        
        // 为每个连接创建任务
        tokio::spawn(async move {
            if let Err(e) = handle_connection(socket).await {
                eprintln!("处理连接错误: {}", e);
            }
        });
    }
}

// 处理连接
async fn handle_connection(mut socket: TcpStream) -> Result<(), Box<dyn Error>> {
    let mut buffer = [0; 1024];
    
    // 读取数据
    let n = socket.read(&mut buffer).await?;
    
    if n == 0 {
        // 连接关闭
        return Ok(());
    }
    
    // 处理请求
    let request = String::from_utf8_lossy(&buffer[..n]);
    println!("收到请求: {}", request);
    
    // 构造响应
    let response = format!("已处理请求: {}", request);
    
    // 发送响应
    socket.write_all(response.as_bytes()).await?;
    
    Ok(())
}

// TCP客户端
async fn run_tcp_client() -> Result<(), Box<dyn Error>> {
    // 连接服务器
    let mut socket = TcpStream::connect("127.0.0.1:8080").await?;
    println!("已连接到服务器");
    
    // 发送请求
    let request = "Hello, server!";
    socket.write_all(request.as_bytes()).await?;
    println!("已发送请求: {}", request);
    
    // 读取响应
    let mut buffer = [0; 1024];
    let n = socket.read(&mut buffer).await?;
    
    if n == 0 {
        return Err("服务器关闭连接".into());
    }
    
    let response = String::from_utf8_lossy(&buffer[..n]);
    println!("收到响应: {}", response);
    
    Ok(())
}
```

1. **Async-std**：标准库风格的异步库

```rust
use async_std::net::{TcpListener, TcpStream};
use async_std::prelude::*;
use async_std::task;
use std::error::Error;

// 异步TCP服务器
async fn run_async_std_server() -> Result<(), Box<dyn Error>> {
    // 绑定监听器
    let listener = TcpListener::bind("127.0.0.1:8081").await?;
    println!("服务器监听于 127.0.0.1:8081");
    
    // 接受连接
    let mut incoming = listener.incoming();
    
    while let Some(stream) = incoming.next().await {
        let stream = stream?;
        
        // 为每个连接创建任务
        task::spawn(async move {
            if let Err(e) = handle_async_std_connection(stream).await {
                eprintln!("处理连接错误: {}", e);
            }
        });
    }
    
    Ok(())
}

// 处理连接
async fn handle_async_std_connection(mut stream: TcpStream) -> Result<(), Box<dyn Error>> {
    let mut buffer = vec![0u8; 1024];
    
    // 读取数据
    let n = stream.read(&mut buffer).await?;
    
    if n == 0 {
        // 连接关闭
        return Ok(());
    }
    
    // 处理请求
    let request = String::from_utf8_lossy(&buffer[..n]);
    println!("收到请求: {}", request);
    
    // 构造响应
    let response = format!("已处理请求: {}", request);
    
    // 发送响应
    stream.write_all(response.as_bytes()).await?;
    
    Ok(())
}
```

1. **Tonic**：gRPC实现

```rust
// 定义服务（在proto文件中）
// service Greeter {
//   rpc SayHello (HelloRequest) returns (HelloResponse);
// }
// 
// message HelloRequest {
//   string name = 1;
// }
// 
// message HelloResponse {
//   string message = 1;
// }

use tonic::{transport::Server, Request, Response, Status};

// 导入生成的代码
pub mod hello {
    tonic::include_proto!("hello"); // 假设proto文件名为hello.proto
}

use hello::greeter_server::{Greeter, GreeterServer};
use hello::{HelloRequest, HelloResponse};

// 实现Greeter服务
#[derive(Debug, Default)]
pub struct MyGreeter {}

#[tonic::async_trait]
impl Greeter for MyGreeter {
    async fn say_hello(
        &self,
        request: Request<HelloRequest>,
    ) -> Result<Response<HelloResponse>, Status> {
        println!("收到请求: {:?}", request);
        
        let reply = HelloResponse {
            message: format!("你好，{}!", request.into_inner().name),
        };
        
        Ok(Response::new(reply))
    }
}

// gRPC服务器
async fn run_grpc_server() -> Result<(), Box<dyn std::error::Error>> {
    let addr = "[::1]:50051".parse()?;
    let greeter = MyGreeter::default();
    
    println!("gRPC服务器监听于 {}", addr);
    
    Server::builder()
        .add_service(GreeterServer::new(greeter))
        .serve(addr)
        .await?;
        
    Ok(())
}

// gRPC客户端
async fn run_grpc_client() -> Result<(), Box<dyn std::error::Error>> {
    let mut client = hello::greeter_client::GreeterClient::connect("http://[::1]:50051").await?;
    
    let request = tonic::Request::new(HelloRequest {
        name: "张三".into(),
    });
    
    let response = client.say_hello(request).await?;
    
    println!("收到响应: {:?}", response);
    
    Ok(())
}
```

1. **Quinn**：QUIC协议实现

```rust
use quinn::{Endpoint, ServerConfig, TransportConfig, VarInt, ClientConfig};
use rustls::{Certificate, PrivateKey};
use std::error::Error;
use std::net::SocketAddr;
use std::sync::Arc;

// 配置QUIC服务器
fn configure_server() -> Result<ServerConfig, Box<dyn Error>> {
    // 生成自签名证书（生产环境应使用正式证书）
    let cert = rcgen::generate_simple_self_signed(vec!["localhost".into()])?;
    let cert_der = cert.serialize_der()?;
    let priv_key = cert.serialize_private_key_der();
    let priv_key = PrivateKey(priv_key);
    let cert_chain = vec![Certificate(cert_der)];
    
    // 创建服务器配置
    let mut server_config = ServerConfig::with_single_cert(cert_chain, priv_key)?;
    let mut transport_config = TransportConfig::default();
    
    // 配置传输参数
    transport_config.max_concurrent_uni_streams(VarInt::from_u32(0));
    server_config.transport = Arc::new(transport_config);
    
    Ok(server_config)
}

// 配置QUIC客户端
fn configure_client() -> Result<ClientConfig, Box<dyn Error>> {
    // 创建客户端配置
    let mut client_config = ClientConfig::new(Arc::new(rustls::ClientConfig::builder()
        .with_safe_defaults()
        .with_custom_certificate_verifier(Arc::new(SkipServerVerification))
        .with_no_client_auth()));
    
    let mut transport_config = TransportConfig::default();
    transport_config.max_idle_timeout(Some(VarInt::from_u32(10_000).into()));
    client_config.transport_config(Arc::new(transport_config));
    
    Ok(client_config)
}

// 证书验证器（生产环境应该正确验证证书）
struct SkipServerVerification;

impl rustls::client::ServerCertVerifier for SkipServerVerification {
    fn verify_server_cert(
        &self,
        _end_entity: &rustls::Certificate,
        _intermediates: &[rustls::Certificate],
        _server_name: &rustls::ServerName,
        _scts: &mut dyn Iterator<Item = &[u8]>,
        _ocsp_response: &[u8],
        _now: std::time::SystemTime,
    ) -> Result<rustls::client::ServerCertVerified, rustls::Error> {
        Ok(rustls::client::ServerCertVerified::assertion())
    }
}

// QUIC服务器
async fn run_quic_server() -> Result<(), Box<dyn Error>> {
    let server_config = configure_server()?;
    let addr = "127.0.0.1:5000".parse::<SocketAddr>()?;
    
    // 创建服务器端点
    let (endpoint, mut incoming) = Endpoint::server(server_config, addr)?;
    println!("QUIC服务器监听于 {}", addr);
    
    // 处理连接
    while let Some(conn) = incoming.next().await {
        tokio::spawn(async move {
            let connection = match conn.await {
                Ok(c) => c,
                Err(e) => {
                    eprintln!("连接错误: {}", e);
                    return;
                }
            };
            
            println!("新连接: {}", connection.remote_address());
            
            // 等待流
            while let Ok(stream) = connection.accept_bi().await {
                let (mut send, mut recv) = stream;
                
                // 读取请求
                let mut buffer = vec![0; 1024];
                let n = match recv.read(&mut buffer).await {
                    Ok(n) => n,
                    Err(e) => {
                        eprintln!("读取错误: {}", e);
                        continue;
                    }
                };
                
                if n == 0 {
                    continue;
                }
                
                // 处理请求
                let request = String::from_utf8_lossy(&buffer[..n]);
                println!("收到请求: {}", request);
                
                // 发送响应
                let response = format!("已处理QUIC请求: {}", request);
                if let Err(e) = send.write_all(response.as_bytes()).await {
                    eprintln!("写入错误: {}", e);
                }
            }
        });
    }
    
    Ok(())
}

// QUIC客户端
async fn run_quic_client() -> Result<(), Box<dyn Error>> {
    let client_config = configure_client()?;
    let addr = "127.0.0.1:0".parse::<SocketAddr>()?;
    
    // 创建客户端端点
    let mut endpoint = Endpoint::client(addr)?;
    endpoint.set_default_client_config(client_config);
    
    // 连接服务器
    let server_addr = "127.0.0.1:5000".parse::<SocketAddr>()?;
    let connection = endpoint.connect(server_addr, "localhost")?.await?;
    println!("已连接到QUIC服务器");
    
    // 创建双向流
    let (mut send, mut recv) = connection.open_bi().await?;
    
    // 发送请求
    let request = "Hello, QUIC server!";
    send.write_all(request.as_bytes()).await?;
    send.finish().await?;
    println!("已发送QUIC请求: {}", request);
    
    // 读取响应
    let mut buffer = vec![0; 1024];
    let n = recv.read(&mut buffer).await?;
    
    if n == 0 {
        return Err("服务器关闭连接".into());
    }
    
    let response = String::from_utf8_lossy(&buffer[..n]);
    println!("收到QUIC响应: {}", response);
    
    Ok(())
}
```

1. **自定义可靠UDP协议**：

```rust
use tokio::net::UdpSocket;
use tokio::time::{timeout, Duration};
use serde::{Serialize, Deserialize};
use bincode;
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use std::error::Error;
use rand::Rng;

// 消息类型
#[derive(Serialize, Deserialize, Debug, Clone)]
enum Message {
    Data {
        id: u64,
        seq: u32,
        total: u32,
        payload: Vec<u8>,
    },
    Ack {
        id: u64,
        seq: u32,
    },
}

// 可靠UDP协议实现
struct ReliableUdp {
    socket: Arc<UdpSocket>,
    // 消息ID到分片的映射
    pending_sends: Arc<RwLock<HashMap<u64, PendingSend>>>,
    // 接收中的消息
    pending_receives: Arc<RwLock<HashMap<u64, PendingReceive>>>,
    // 下一个消息ID
    next_id: Arc<RwLock<u64>>,
    // 重试次数
    max_retries: u32,
    // 超时时间
    timeout: Duration,
}

// 待发送的消息
struct PendingSend {
    fragments: HashMap<u32, Vec<u8>>,
    acks: HashMap<u32, bool>,
    addr: std::net::SocketAddr,
    retries: HashMap<u32, u32>,
}

// 接收中的消息
struct PendingReceive {
    fragments: HashMap<u32, Vec<u8>>,
    total: u32,
    last_activity: std::time::Instant,
}

impl ReliableUdp {
    // 创建新实例
    async fn new(addr: &str) -> Result<Self, Box<dyn Error>> {
        let socket = UdpSocket::bind(addr).await?;
        let socket = Arc::new(socket);
        
        let reliable_udp = Self {
            socket,
            pending_sends: Arc::new(RwLock::new(HashMap::new())),
            pending_receives: Arc::new(RwLock::new(HashMap::new())),
            next_id: Arc::new(RwLock::new(0)),
            max_retries: 5,
            timeout: Duration::from_secs(1),
        };
        
        Ok(reliable_udp)
    }
    
    // 开始接收处理循环
    async fn start_receive_loop(&self) {
        let socket = self.socket.clone();
        let pending_sends = self.pending_sends.clone();
        let pending_receives = self.pending_receives.clone();
        let max_retries = self.max_retries;
        
        tokio::spawn(async move {
            let mut buf = vec![0; 65536];
            
            loop {
                match socket.recv_from(&mut buf).await {
                    Ok((n, addr)) => {
                        let data = &buf[..n];
                        if let Ok(message) = bincode::deserialize::<Message>(data) {
                            match message {
                                Message::Data { id, seq, total, payload } => {
                                    // 处理数据消息
                                    println!("收到数据: id={}, seq={}/{}", id, seq, total);
                                    
                                    // 发送确认
                                    let ack = Message::Ack { id, seq };
                                    let ack_data = bincode::serialize(&ack).unwrap();
                                    let _ = socket.send_to(&ack_data, &addr).await;
                                    
                                    // 存储数据分片
                                    let mut receives = pending_receives.write().await;
                                    let receive = receives.entry(id).or_insert_with(|| PendingReceive {
                                        fragments: HashMap::new(),
                                        total,
                                        last_activity: std::time::Instant::now(),
                                    });
                                    
                                    receive.fragments.insert(seq, payload);
                                    receive.last_activity = std::time::Instant::now();
                                    
                                    // 检查是否收到所有分片
                                    if receive.fragments.len() as u32 == total {
                                        println!("收到完整消息: id={}", id);
                                        // 重组消息会在 receive_message 中完成
                                    }
                                },
                                Message::Ack { id, seq } => {
                                    // 处理确认消息
                                    println!("收到确认: id={}, seq={}", id, seq);
                                    
                                    let mut sends = pending_sends.write().await;
                                    if let Some(send) = sends.get_mut(&id) {
                                        send.acks.insert(seq, true);
                                        
                                        // 检查是否所有分片都已确认
                                        let all_acked = send.acks.values().all(|&acked| acked);
                                        if all_acked {
                                            println!("所有分片已确认: id={}", id);
                                            sends.remove(&id);
                                        }
                                    }
                                },
                            }
                        }
                    },
                    Err(e) => {
                        eprintln!("接收错误: {}", e);
                    }
                }
            }
        });
        
        // 启动重传定时器
        let socket = self.socket.clone();
        let pending_sends = self.pending_sends.clone();
        let timeout = self.timeout;
        
        tokio::spawn(async move {
            loop {
                tokio::time::sleep(Duration::from_millis(100)).await;
                
                let mut sends = pending_sends.write().await;
                let now = std::time::Instant::now();
                
                // 检查需要重传的分片
                for (id, send) in sends.iter_mut() {
                    for (seq, data) in &send.fragments {
                        if !send.acks.get(seq).copied().unwrap_or(false) {
                            let retries = send.retries.entry(*seq).or_insert(0);
                            
                            // 如果超过重试次数，放弃
                            if *retries >= max_retries {
                                println!("分片重传次数过多，放弃: id={}, seq={}", id, seq);
                                continue;
                            }
                            
                            // 重传
                            let message = Message::Data {
                                id: *id,
                                seq: *seq,
                                total: send.fragments.len() as u32,
                                payload: data.clone(),
                            };
                            
                            let data = bincode::serialize(&message).unwrap();
                            if let Err(e) = socket.send_to(&data, &send.addr).await {
                                eprintln!("重传错误: {}", e);
                            } else {
                                println!("重传分片: id={}, seq={}, 尝试次数={}", id, seq, *retries);
                                *retries += 1;
                            }
                        }
                    }
                }
                
                // 清理已完成或超时的发送
                sends.retain(|_, send| {
                    !send.acks.values().all(|&acked| acked)
                });
            }
        });
        
        // 清理超时的接收
        let pending_receives = self.pending_receives.clone();
        
        tokio::spawn(async move {
            loop {
                tokio::time::sleep(Duration::from_secs(10)).await;
                
                let mut receives = pending_receives.write().await;
                let now = std::time::Instant::now();
                
                // 移除超过30秒不活跃的接收
                receives.retain(|_, receive| {
                    now.duration_since(receive.last_activity) < Duration::from_secs(30)
                });
            }
        });
    }
    
    // 发送消息
    async fn send_message(&self, addr: &std::net::SocketAddr, data: &[u8], fragment_size: usize) -> Result<u64, Box<dyn Error>> {
        // 生成消息ID
        let id = {
            let mut next_id = self.next_id.write().await;
            let id = *next_id;
            *next_id += 1;
            id
        };
        
        // 分片数据
        let mut fragments = HashMap::new();
        let total_fragments = (data.len() + fragment_size - 1) / fragment_size;
        
        for seq in 0..total_fragments {
            let start = seq * fragment_size;
            let end = std::cmp::min(start + fragment_size, data.len());
            fragments.insert(seq as u32, data[start..end].to_vec());
        }
        
        // 创建挂起的发送
        let mut acks = HashMap::new();
        for seq in 0..total_fragments {
            acks.insert(seq as u32, false);
        }
        
        let pending_send = PendingSend {
            fragments: fragments.clone(),
            acks,
            addr: *addr,
            retries: HashMap::new(),
        };
        
        // 存储发送状态
        {
            let mut sends = self.pending_sends.write().await;
            sends.insert(id, pending_send);
        }
        
        // 发送所有分片
        for (seq, data) in &fragments {
            let message = Message::Data {
                id,
                seq: *seq,
                total: total_fragments as u32,
                payload: data.clone(),
            };
            
            let serialized = bincode::serialize(&message)?;
            self.socket.send_to(&serialized, addr).await?;
            
            println!("发送分片: id={}, seq={}/{}", id, seq, total_fragments);
        }
        
        Ok(id)
    }
    
    // 等待消息发送完成
    async fn wait_for_send_completion(&self, id: u64) -> Result<(), Box<dyn Error>> {
        loop {
            tokio::time::sleep(Duration::from_millis(100)).await;
            
            let sends = self.pending_sends.read().await;
            if !sends.contains_key(&id) {
                return Ok(());
            }
        }
    }
    
    // 接收消息
    async fn receive_message(&self, id: u64) -> Result<Vec<u8>, Box<dyn Error>> {
        loop {
            // 检查是否收到完整消息
            let mut receives = self.pending_receives.write().await;
            
            if let Some(receive) = receives.get(&id) {
                if receive.fragments.len() as u32 == receive.total {
                    // 重组消息
                    let mut result = Vec::new();
                    
                    for seq in 0..receive.total {
                        if let Some(fragment) = receive.fragments.get(&seq) {
                            result.extend_from_slice(fragment);
                        } else {
                            return Err("消息不完整".into());
                        }
                    }
                    
                    // 移除接收状态
                    receives.remove(&id);
                    
                    return Ok(result);
                }
            }
            
            // 等待更多分片
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    }
    
    // 关闭套接字
    async fn close(&self) {
        // 清理状态
        {
            let mut sends = self.pending_sends.write().await;
            sends.clear();
        }
        
        {
            let mut receives = self.pending_receives.write().await;
            receives.clear();
        }
    }
}

// 使用示例
async fn reliable_udp_example() -> Result<(), Box<dyn Error>> {
    // 创建服务端
    let server = ReliableUdp::new("127.0.0.1:7000").await?;
    server.start_receive_loop().await;
    
    // 创建客户端
    let client = ReliableUdp::new("127.0.0.1:7001").await?;
    client.start_receive_loop().await;
    
    // 连接对方
    let server_addr = "127.0.0.1:7000".parse::<std::net::SocketAddr>()?;
    let client_addr = "127.0.0.1:7001".parse::<std::net::SocketAddr>()?;
    
    // 客户端发送大消息
    let large_message = vec![0u8; 100000]; // 100KB消息
    let message_id = client.send_message(&server_addr, &large_message, 1024).await?;
    
    println!("客户端发送大消息，ID: {}", message_id);
    
    // 等待发送完成
    client.wait_for_send_completion(message_id).await?;
    
    println!("客户端消息发送完成");
    
    // 服务端接收消息
    let received = server.receive_message(message_id).await?;
    
    println!("服务端接收到完整消息，大小: {}", received.len());
    
    // 清理
    client.close().await;
    server.close().await;
    
    Ok(())
}
```

**分布式系统中的协议设计考虑**：

1. **连接管理**：
   - 建立和维护连接
   - 心跳机制
   - 优雅关闭

2. **消息序列化**：
   - 使用Serde、bincode、Protocol Buffers等
   - 版本控制和兼容性

3. **流量控制**：
   - 背压机制
   - 速率限制

4. **安全性**：
   - TLS加密
   - 双向认证
   - 安全密钥交换

5. **监控和调试**：
   - 协议级别的日志
   - 性能监控点

Rust的类型系统和零成本抽象使其成为实现高性能、类型安全的网络协议的理想选择。异步编程支持使得可以高效处理大量并发连接，而所有权系统确保了资源的正确管理。

### 4.2 序列化与数据编码

在分布式系统中，数据需要在网络上传输或持久化到存储介质。高效的序列化和数据编码对性能和兼容性至关重要。

**序列化的核心需求**：

```rust
SerializationRequirements = {
    效率: "最小化序列化/反序列化开销和数据大小",
    类型安全: "确保类型信息在传输过程中保持一致",
    兼容性: "处理不同版本的结构和向前/向后兼容性",
    安全性: "防止反序列化漏洞",
    可读性: "调试和诊断的便利性（用于人类可读格式）"
}
```

**Rust中的主要序列化库**：

1. **Serde生态系统**：

```rust
use serde::{Serialize, Deserialize};

// 定义可序列化结构
#[derive(Serialize, Deserialize, Debug, Clone)]
struct User {
    id: u64,
    name: String,
    email: String,
    #[serde(default)]  // 处理向前兼容性
    role: Option<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]  // 优化输出
    permissions: Vec<String>,
}

// JSON格式
fn serde_json_example() -> Result<(), Box<dyn std::error::Error>> {
    // 创建对象
    let user = User {
        id: 1001,
        name: "张三".to_string(),
        email: "zhangsan@example.com".to_string(),
        role: Some("管理员".to_string()),
        permissions: vec!["读取".to_string(), "写入".to_string()],
    };
    
    // 序列化为JSON
    let json = serde_json::to_string(&user)?;
    println!("JSON序列化结果: {}", json);
    
    // 反序列化
    let deserialized: User = serde_json::from_str(&json)?;
    println!("JSON反序列化结果: {:?}", deserialized);
    
    // 美化输出（用于日志或调试）
    let pretty_json = serde_json::to_string_pretty(&user)?;
    println!("美化JSON:\n{}", pretty_json);
    
    Ok(())
}

// 二进制格式（bincode）
fn bincode_example() -> Result<(), Box<dyn std::error::Error>> {
    // 创建对象
    let user = User {
        id: 1001,
        name: "张三".to_string(),
        email: "zhangsan@example.com".to_string(),
        role: Some("管理员".to_string()),
        permissions: vec!["读取".to_string(), "写入".to_string()],
    };
    
    // 序列化为二进制
    let encoded: Vec<u8> = bincode::serialize(&user)?;
    println!("Bincode序列化结果大小: {} 字节", encoded.len());
    
    // 反序列化
    let decoded: User = bincode::deserialize(&encoded[..])?;
    println!("Bincode反序列化结果: {:?}", decoded);
    
    Ok(())
}

// CBOR格式
fn cbor_example() -> Result<(), Box<dyn std::error::Error>> {
    // 创建对象
    let user = User {
        id: 1001,
        name: "张三".to_string(),
        email: "zhangsan@example.com".to_string(),
        role: Some("管理员".to_string()),
        permissions: vec!["读取".to_string(), "写入".to_string()],
    };
    
    // 序列化为CBOR
    let encoded = serde_cbor::to_vec(&user)?;
    println!("CBOR序列化结果大小: {} 字节", encoded.len());
    
    // 反序列化
    let decoded: User = serde_cbor::from_slice(&encoded[..])?;
    println!("CBOR反序列化结果: {:?}", decoded);
    
    Ok(())
}

// MessagePack格式
fn messagepack_example() -> Result<(), Box<dyn std::error::Error>> {
    // 创建对象
    let user = User {
        id: 1001,
        name: "张三".to_string(),
        email: "zhangsan@example.com".to_string(),
        role: Some("管理员".to_string()),
        permissions: vec!["读取".to_string(), "写入".to_string()],
    };
    
    // 序列化为MessagePack
    let encoded = rmp_serde::to_vec(&user)?;
    println!("MessagePack序列化结果大小: {} 字节", encoded.len());
    
    // 反序列化
    let decoded: User = rmp_serde::from_slice(&encoded[..])?;
    println!("MessagePack反序列化结果: {:?}", decoded);
    
    Ok(())
}
```

1. **Protocol Buffers（protobuf）**：

```rust
// 通过.proto文件定义结构
// syntax = "proto3";
// 
// message UserProto {
//   uint64 id = 1;
//   string name = 2;
//   string email = 3;
//   optional string role = 4;
//   repeated string permissions = 5;
// }

use prost::Message;

// 生成的代码
#[derive(Clone, PartialEq, Message)]
pub struct UserProto {
    #[prost(uint64, tag = "1")]
    pub id: u64,
    #[prost(string, tag = "2")]
    pub name: String,
    #[prost(string, tag = "3")]
    pub email: String,
    #[prost(string, optional, tag = "4")]
    pub role: Option<String>,
    #[prost(string, repeated, tag = "5")]
    pub permissions: Vec<String>,
}

// Protocol Buffers示例
fn protobuf_example() -> Result<(), Box<dyn std::error::Error>> {
    // 创建对象
    let mut user = UserProto {
        id: 1001,
        name: "张三".to_string(),
        email: "zhangsan@example.com".to_string(),
        role: Some("管理员".to_string()),
        permissions: vec!["读取".to_string(), "写入".to_string()],
    };
    
    // 序列化
    let mut buf = Vec::new();
    buf.reserve(user.encoded_len());
    user.encode(&mut buf)?;
    
    println!("Protocol Buffers序列化结果大小: {} 字节", buf.len());
    
    // 反序列化
    let decoded = UserProto::decode(&buf[..])?;
    println!("Protocol Buffers反序列化结果: {:?}", decoded);
    
    Ok(())
}
```

1. **Cap'n Proto**：

```rust
// 通过.capnp文件定义结构
// @0xd4e54c2d023eb14c;  // 文件ID
// 
// struct UserCapnp {
//   id @0 :UInt64;
//   name @1 :Text;
//   email @2 :Text;
//   role @3 :Text;
//   permissions @4 :List(Text);
// }

// 使用capnpc-rust生成代码
pub mod user_capnp {
    include!(concat!(env!("OUT_DIR"), "/user_capnp.rs"));
}

use capnp::message::{Builder, HeapAllocator, ReaderOptions};
use capnp::serialize::{write_message, read_message};
use user_capnp::user_capnp;

// Cap'n Proto示例
fn capnproto_example() -> Result<(), Box<dyn std::error::Error>> {
    // 创建对象
    let mut message = Builder::new_default();
    let mut user = message.init_root::<user_capnp::Builder>();
    
    user.set_id(1001);
    user.set_name("张三");
    user.set_email("zhangsan@example.com");
    user.set_role("管理员");
    
    {
        let mut permissions = user.reborrow().init_permissions(2);
        permissions.set(0, "读取");
        permissions.set(1, "写入");
    }
    
    // 序列化
    let mut buf = Vec::new();
    write_message(&mut buf, &message)?;
    
    println!("Cap'n Proto序列化结果大小: {} 字节", buf.len());
    
    // 反序列化
    let reader = read_message(&mut buf.as_slice(), ReaderOptions::new())?;
    let user_reader = reader.get_root::<user_capnp::Reader>()?;
    
    println!("Cap'n Proto反序列化结果:");
    println!("  ID: {}", user_reader.get_id());
    println!("  名称: {}", user_reader.get_name()?);
    println!("  邮箱: {}", user_reader.get_email()?);
    println!("  角色: {}", user_reader.get_role()?);
    
    let permissions = user_reader.get_permissions()?;
    print!("  权限: [");
    for i in 0..permissions.len() {
        if i > 0 { print!(", "); }
        print!("{}", permissions.get(i)?);
    }
    println!("]");
    
    Ok(())
}
```

1. **Flatbuffers**：

```rust
// 通过.fbs文件定义结构
// namespace MyGame;
// 
// table UserFlatbuf {
//   id:ulong;
//   name:string;
//   email:string;
//   role:string;
//   permissions:[string];
// }
// 
// root_type UserFlatbuf;

// 使用flatc生成代码
#[allow(unused_imports)]
use flatbuffers::{FlatBufferBuilder, WIPOffset, Follow, Push, EndianScalar};

// 生成的代码
include!(concat!(env!("OUT_DIR"), "/user_flatbuf_generated.rs"));

use my_game::user_flatbuf::*;

// Flatbuffers示例
fn flatbuffers_example() -> Result<(), Box<dyn std::error::Error>> {
    // 创建对象
    let mut builder = FlatBufferBuilder::new();
    
    let name = builder.create_string("张三");
    let email = builder.create_string("zhangsan@example.com");
    let role = builder.create_string("管理员");
    
    let permissions = {
        let perm1 = builder.create_string("读取");
        let perm2 = builder.create_string("写入");
        let perms = [perm1, perm2];
        builder.create_vector(&perms)
    };
    
    let user = UserFlatbuf::create(&mut builder, &UserFlatbufArgs {
        id: 1001,
        name: Some(name),
        email: Some(email),
        role: Some(role),
        permissions: Some(permissions),
    });
    
    builder.finish(user, None);
    
    let buf = builder.finished_data();
    println!("Flatbuffers序列化结果大小: {} 字节", buf.len());
    
    // 反序列化（零拷贝）
    let user = get_root_as_user_flatbuf(buf);
    
    println!("Flatbuffers反序列化结果:");
    println!("  ID: {}", user.id());
    println!("  名称: {}", user.name().unwrap());
    println!("  邮箱: {}", user.email().unwrap());
    println!("  角色: {}", user.role().unwrap());
    
    print!("  权限: [");
    for i in 0..user.permissions().unwrap().len() {
        if i > 0 { print!(", "); }
        print!("{}", user.permissions().unwrap().get(i));
    }
    println!("]");
    
    Ok(())
}
```

**序列化格式性能比较**：

| 格式 | 优势 | 劣势 | 适用场景 |
|-----|-----|-----|---------|
| JSON | 人类可读、广泛支持 | 相对较大、性能较低 | API接口、配置文件 |
| Bincode | 小巧高效、原生Rust | 不跨语言、不可读 | Rust系统间通信、持久化 |
| CBOR | 小巧、自描述、可扩展 | 较新、支持相对较少 | IoT设备、资源受限环境 |
| MessagePack | 小巧、跨语言、快速 | 较难调试 | 高性能系统间通信 |
| Protocol Buffers | 小巧、跨语言、模式进化 | 需要编译、不可读 | 微服务通信、持久存储 |
| Cap'n Proto | 零拷贝、超高性能、跨语言 | 复杂、入门难度高 | 高性能系统、大数据传输 |
| Flatbuffers | 零拷贝、跨语言、无解析开销 | 序列化较慢 | 游戏、移动应用、低延迟场景 |

**序列化最佳实践**：

1. **选择合适的格式**：
   - 人类可读性和调试需求高 → JSON
   - 纯Rust环境追求性能 → Bincode
   - 跨语言、需要模式演进 → Protocol Buffers/CBOR
   - 极端性能场景 → Cap'n Proto/Flatbuffers

2. **版本管理与兼容性**：

```rust
// 使用版本化结构
#[derive(Serialize, Deserialize, Debug)]
#[serde(tag = "version")]
enum VersionedMessage {
    #[serde(rename = "1.0")]
    V1 {
        id: u64,
        content: String,
    },
    #[serde(rename = "1.1")]
    V2 {
        id: u64,
        content: String,
        #[serde(default)]
        metadata: HashMap<String, String>,
    },
    #[serde(rename = "2.0")]
    V3 {
        id: u64,
        content: String,
        #[serde(default)]
        metadata: HashMap<String, String>,
        #[serde(default)]
        attachments: Vec<Attachment>,
    },
}

#[derive(Serialize, Deserialize, Debug)]
struct Attachment {
    name: String,
    content_type: String,
    data: Vec<u8>,
}

// 处理不同版本
fn handle_versioned_message(json: &str) -> Result<(), Box<dyn std::error::Error>> {
    let message: VersionedMessage = serde_json::from_str(json)?;
    
    match message {
        VersionedMessage::V1 { id, content } => {
            println!("处理V1消息: id={}, content={}", id, content);
        },
        VersionedMessage::V2 { id, content, metadata } => {
            println!("处理V2消息: id={}, content={}, metadata={:?}", id, content, metadata);
        },
        VersionedMessage::V3 { id, content, metadata, attachments } => {
            println!("处理V3消息: id={}, content={}, metadata={:?}, attachments={}", 
                    id, content, metadata, attachments.len());
        },
    }
    
    Ok(())
}
```

1. **安全反序列化**：

```rust
// 限制输入大小
fn safely_deserialize_json<T: serde::de::DeserializeOwned>(json: &str, max_size: usize) -> Result<T, String> {
    if json.len() > max_size {
        return Err(format!("输入太大：{} > {}", json.len(), max_size));
    }
    
    match serde_json::from_str(json) {
        Ok(result) => Ok(result),
        Err(e) => Err(format!("反序列化错误: {}", e)),
    }
}

// 验证反序列化后的数据
#[derive(Serialize, Deserialize, Debug)]
struct UserInput {
    username: String,
    email: String,
    age: u8,
}

impl UserInput {
    fn validate(&self) -> Result<(), String> {
        // 验证用户名长度
        if self.username.len() < 3 || self.username.len() > 50 {
            return Err("用户名长度必须在3-50字符之间".to_string());
        }
        
        // 验证邮箱格式（简化示例）
        if !self.email.contains('@') {
            return Err("无效的邮箱格式".to_string());
        }
        
        // 验证年龄范围
        if self.age < 18 || self.age > 120 {
            return Err("年龄必须在18-120之间".to_string());
        }
        
        Ok(())
    }
}

// 安全处理用户输入
fn process_user_input(json: &str) -> Result<(), String> {
    // 限制输入大小为10KB
    let user: UserInput = safely_deserialize_json(json, 10240)?;
    
    // 验证输入
    user.validate()?;
    
    // 处理验证过的数据
    println!("处理有效用户: {:?}", user);
    
    Ok(())
}
```

1. **性能优化**：

```rust
// 重用缓冲区和分配器
fn reuse_buffers_example() -> Result<(), Box<dyn std::error::Error>> {
    // 创建示例数据
    let users = vec![
        User { id: 1, name: "张三".to_string(), email: "zhang@example.com".to_string(), 
              role: None, permissions: vec![] },
        User { id: 2, name: "李四".to_string(), email: "li@example.com".to_string(), 
              role: None, permissions: vec![] },
        // ... 更多用户
    ];
    
    // 重用写入缓冲区
    let mut write_buffer = Vec::with_capacity(1024);
    
    // 重用读取缓冲区
    let mut read_buffer = Vec::with_capacity(1024);
    
    for user in &users {
        // 清空写入缓冲区而不释放内存
        write_buffer.clear();
        
        // 序列化到重用的缓冲区
        bincode::serialize_into(&mut write_buffer, user)?;
        
        // 准备读取缓冲区
        read_buffer.clear();
        read_buffer.extend_from_slice(&write_buffer);
        
        // 反序列化
        let _: User = bincode::deserialize_from(read_buffer.as_slice())?;
    }
    
    Ok(())
}

// 使用零拷贝技术
fn zero_copy_example() -> Result<(), Box<dyn std::error::Error>> {
    // 创建Flatbuffers构建器
    let mut builder = flatbuffers::FlatBufferBuilder::new();
    
    // 创建一些用户
    let mut user_offsets = Vec::new();
    
    for i in 1..100 {
        let name = builder.create_string(&format!("用户{}", i));
        let email = builder.create_string(&format!("user{}@example.com", i));
        
        let user = UserFlatbuf::create(&mut builder, &UserFlatbufArgs {
            id: i as u64,
            name: Some(name),
            email: Some(email),
            role: None,
            permissions: None,
        });
        
        user_offsets.push(user);
    }
    
    // 创建用户表
    let users_vector = builder.create_vector(&user_offsets);
    builder.finish(users_vector, None);
    
    let buffer = builder.finished_data();
    
    // 测量访问性能
    let start = std::time::Instant::now();
    
    // 直接从缓冲区访问（零拷贝）
    let users = flatbuffers::root_as_vector::<flatbuffers::ForwardsUOffset<UserFlatbuf>>(buffer);
    
    for i in 0..users.len() {
        let user = users.get(i);
        let _ = user.id();
        let _ = user.name();
        let _ = user.email();
    }
    
    let duration = start.elapsed();
    println!("零拷贝访问100个用户耗时: {:?}", duration);
    
    Ok(())
}
```

1. **压缩与加密**：

```rust
use flate2::Compression;
use flate2::write::{GzEncoder, GzDecoder};
use std::io::{Read, Write};
use ring::aead::{self, Aad, BoundKey, Nonce, UnboundKey, AES_256_GCM};
use ring::rand::{SecureRandom, SystemRandom};

// 压缩序列化数据
fn compress_data<T: serde::Serialize>(data: &T) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    // 首先序列化
    let serialized = bincode::serialize(data)?;
    
    // 然后压缩
    let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
    encoder.write_all(&serialized)?;
    let compressed = encoder.finish()?;
    
    Ok(compressed)
}

// 解压缩并反序列化
fn decompress_data<T: serde::de::DeserializeOwned>(compressed: &[u8]) -> Result<T, Box<dyn std::error::Error>> {
    // 解压缩
    let mut decoder = GzDecoder::new(Vec::new());
    decoder.write_all(compressed)?;
    let decompressed = decoder.finish()?;
    
    // 反序列化
    let result = bincode::deserialize(&decompressed)?;
    
    Ok(result)
}

// 加密序列化数据
struct MySealing(aead::SealingKey<aead::Unbound>);

fn encrypt_data<T: serde::Serialize>(
    data: &T, 
    key: &[u8; 32]
) -> Result<(Vec<u8>, [u8; 12]), Box<dyn std::error::Error>> {
    // 首先序列化
    let serialized = bincode::serialize(data)?;
    
    // 生成随机nonce
    let rng = SystemRandom::new();
    let mut nonce_bytes = [0u8; 12];
    rng.fill(&mut nonce_bytes)?;
    let nonce = Nonce::assume_unique_for_key(nonce_bytes);
    
    // 创建密钥
    let unbound_key = UnboundKey::new(&AES_256_GCM, key)?;
    let mut sealing_key = MySealing(aead::SealingKey::new(unbound_key, aead::Nonce::from(nonce)));
    
    // 加密数据
    let mut in_out = serialized;
    let tag = sealing_key.0.seal_in_place_separate_tag(
        Aad::empty(), 
        &mut in_out
    )?;
    
    // 组合密文和认证标签
    let mut result = in_out;
    result.extend_from_slice(tag.as_ref());
    
    Ok((result, nonce_bytes))
}

// 解密并反序列化
struct MyOpening(aead::OpeningKey<aead::Unbound>);

fn decrypt_data<T: serde::de::DeserializeOwned>(
    encrypted: &[u8], 
    key: &[u8; 32],
    nonce_bytes: &[u8; 12]
) -> Result<T, Box<dyn std::error::Error>> {
    // 分离密文和认证标签
    let tag_len = aead::AES_256_GCM.tag_len();
    if encrypted.len() < tag_len {
        return Err("加密数据太短".into());
    }
    
    let ciphertext_len = encrypted.len() - tag_len;
    let mut ciphertext = encrypted[..ciphertext_len].to_vec();
    let tag = encrypted[ciphertext_len..].to_vec();
    
    // 创建密钥
    let nonce = Nonce::assume_unique_for_key(*nonce_bytes);
    let unbound_key = UnboundKey::new(&AES_256_GCM, key)?;
    let mut opening_key = MyOpening(aead::OpeningKey::new(unbound_key, aead::Nonce::from(nonce)));
    
    // 解密数据
    let plaintext = opening_key.0.open_in_place(
        Aad::empty(), 
        &mut ciphertext
    )?;
    
    // 反序列化
    let result = bincode::deserialize(plaintext)?;
    
    Ok(result)
}
```

### 4.3 分布式日志和监控

在分布式系统中，日志和监控至关重要，它们帮助开发者了解系统状态、排查问题并验证系统行为。

**1. 结构化日志实现**：

```rust
use serde::{Serialize, Deserialize};
use chrono::{DateTime, Utc};
use std::sync::{Arc, Mutex};
use std::collections::HashMap;

// 日志级别
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum LogLevel {
    Trace,
    Debug,
    Info,
    Warn,
    Error,
    Fatal,
}

// 结构化日志条目
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogEntry {
    timestamp: DateTime<Utc>,
    level: LogLevel,
    message: String,
    service: String,
    trace_id: Option<String>,
    span_id: Option<String>,
    #[serde(flatten)]
    fields: HashMap<String, serde_json::Value>,
}

// 日志接收器特性
pub trait LogSink: Send + Sync {
    fn write(&self, entry: &LogEntry) -> Result<(), Box<dyn std::error::Error>>;
    fn flush(&self) -> Result<(), Box<dyn std::error::Error>>;
}

// 控制台日志接收器
pub struct ConsoleSink;

impl LogSink for ConsoleSink {
    fn write(&self, entry: &LogEntry) -> Result<(), Box<dyn std::error::Error>> {
        let json = serde_json::to_string_pretty(entry)?;
        println!("{}", json);
        Ok(())
    }
    
    fn flush(&self) -> Result<(), Box<dyn std::error::Error>> {
        Ok(())
    }
}

// 文件日志接收器
pub struct FileSink {
    file: Mutex<std::fs::File>,
}

impl FileSink {
    pub fn new(path: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let file = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)?;
        
        Ok(Self {
            file: Mutex::new(file),
        })
    }
}

impl LogSink for FileSink {
    fn write(&self, entry: &LogEntry) -> Result<(), Box<dyn std::error::Error>> {
        let json = serde_json::to_string(entry)?;
        let mut file = self.file.lock().unwrap();
        writeln!(file, "{}", json)?;
        Ok(())
    }
    
    fn flush(&self) -> Result<(), Box<dyn std::error::Error>> {
        let mut file = self.file.lock().unwrap();
        file.flush()?;
        Ok(())
    }
}

// 网络日志接收器
pub struct NetworkSink {
    endpoint: String,
    client: reqwest::Client,
    buffer: Mutex<Vec<LogEntry>>,
    max_buffer_size: usize,
}

impl NetworkSink {
    pub fn new(endpoint: &str, max_buffer_size: usize) -> Self {
        Self {
            endpoint: endpoint.to_string(),
            client: reqwest::Client::new(),
            buffer: Mutex::new(Vec::with_capacity(max_buffer_size)),
            max_buffer_size,
        }
    }
    
    fn send_logs(&self, logs: Vec<LogEntry>) -> Result<(), Box<dyn std::error::Error>> {
        let rt = tokio::runtime::Runtime::new()?;
        rt.block_on(async {
            self.client.post(&self.endpoint)
                .json(&logs)
                .send()
                .await?
                .error_for_status()?;
            Ok::<_, Box<dyn std::error::Error>>(())
        })?;
        Ok(())
    }
}

impl LogSink for NetworkSink {
    fn write(&self, entry: &LogEntry) -> Result<(), Box<dyn std::error::Error>> {
        let mut buffer = self.buffer.lock().unwrap();
        buffer.push(entry.clone());
        
        if buffer.len() >= self.max_buffer_size {
            let logs = std::mem::replace(&mut *buffer, Vec::with_capacity(self.max_buffer_size));
            drop(buffer); // 释放锁
            self.send_logs(logs)?;
        }
        
        Ok(())
    }
    
    fn flush(&self) -> Result<(), Box<dyn std::error::Error>> {
        let mut buffer = self.buffer.lock().unwrap();
        if !buffer.is_empty() {
            let logs = std::mem::replace(&mut *buffer, Vec::new());
            drop(buffer); // 释放锁
            self.send_logs(logs)?;
        }
        Ok(())
    }
}

// 日志记录器
pub struct Logger {
    service: String,
    sinks: Vec<Arc<dyn LogSink>>,
    context: Mutex<HashMap<String, serde_json::Value>>,
}

impl Logger {
    pub fn new(service: &str) -> Self {
        Self {
            service: service.to_string(),
            sinks: Vec::new(),
            context: Mutex::new(HashMap::new()),
        }
    }
    
    pub fn add_sink(&mut self, sink: Arc<dyn LogSink>) {
        self.sinks.push(sink);
    }
    
    pub fn with_context(&self, key: &str, value: serde_json::Value) {
        let mut context = self.context.lock().unwrap();
        context.insert(key.to_string(), value);
    }
    
    pub fn log(&self, level: LogLevel, message: &str) {
        self.log_with_fields(level, message, HashMap::new());
    }
    
    pub fn log_with_fields(&self, level: LogLevel, message: &str, fields: HashMap<String, serde_json::Value>) {
        let mut all_fields = {
            let context = self.context.lock().unwrap();
            context.clone()
        };
        
        // 合并字段
        for (k, v) in fields {
            all_fields.insert(k, v);
        }
        
        let entry = LogEntry {
            timestamp: Utc::now(),
            level,
            message: message.to_string(),
            service: self.service.clone(),
            trace_id: all_fields.get("trace_id").and_then(|v| v.as_str().map(|s| s.to_string())),
            span_id: all_fields.get("span_id").and_then(|v| v.as_str().map(|s| s.to_string())),
            fields: all_fields,
        };
        
        for sink in &self.sinks {
            if let Err(e) = sink.write(&entry) {
                eprintln!("日志写入失败: {}", e);
            }
        }
    }
    
    pub fn trace(&self, message: &str) {
        self.log(LogLevel::Trace, message);
    }
    
    pub fn debug(&self, message: &str) {
        self.log(LogLevel::Debug, message);
    }
    
    pub fn info(&self, message: &str) {
        self.log(LogLevel::Info, message);
    }
    
    pub fn warn(&self, message: &str) {
        self.log(LogLevel::Warn, message);
    }
    
    pub fn error(&self, message: &str) {
        self.log(LogLevel::Error, message);
    }
    
    pub fn fatal(&self, message: &str) {
        self.log(LogLevel::Fatal, message);
    }
    
    pub fn flush(&self) {
        for sink in &self.sinks {
            if let Err(e) = sink.flush() {
                eprintln!("日志刷新失败: {}", e);
            }
        }
    }
}

// 日志宏，简化日志使用
#[macro_export]
macro_rules! log_info {
    ($logger:expr, $message:expr) => {
        $logger.info($message)
    };
    ($logger:expr, $message:expr, $($key:expr => $value:expr),*) => {{
        let mut fields = std::collections::HashMap::new();
        $(
            fields.insert($key.to_string(), serde_json::json!($value));
        )*
        $logger.log_with_fields(LogLevel::Info, $message, fields);
    }};
}

// 使用示例
fn logging_example() {
    // 创建日志记录器
    let mut logger = Logger::new("user-service");
    
    // 添加接收器
    logger.add_sink(Arc::new(ConsoleSink));
    
    if let Ok(file_sink) = FileSink::new("logs/service.log") {
        logger.add_sink(Arc::new(file_sink));
    }
    
    logger.add_sink(Arc::new(NetworkSink::new(
        "https://logging.example.com/ingest",
        100
    )));
    
    // 设置上下文
    logger.with_context("env", serde_json::json!("production"));
    logger.with_context("version", serde_json::json!("1.2.3"));
    
    // 记录基本日志
    logger.info("服务启动");
    
    // 带字段的日志
    let mut fields = HashMap::new();
    fields.insert("user_id".to_string(), serde_json::json!(1001));
    fields.insert("action".to_string(), serde_json::json!("login"));
    logger.log_with_fields(LogLevel::Info, "用户登录", fields);
    
    // 使用宏记录日志
    log_info!(logger, "处理请求", "method" => "GET", "path" => "/api/users", "duration_ms" => 42);
    
    // 错误日志
    logger.error("数据库连接失败");
    
    // 确保日志刷新
    logger.flush();
}
```

**2. 分布式跟踪实现**：

```rust
use opentelemetry::{
    trace::{Tracer, TraceError},
    global, sdk,
};
use opentelemetry::sdk::trace::Sampler;
use opentelemetry_jaeger::new_pipeline;
use std::error::Error;

// 初始化分布式跟踪
fn init_tracer() -> Result<impl Tracer, TraceError> {
    // 配置Jaeger导出器
    let tracer = new_pipeline()
        .with_service_name("my-distributed-service")
        .with_max_packet_size(65000)
        .with_collector_endpoint("http://jaeger:14268/api/traces")
        .install_batch(opentelemetry::runtime::Tokio)?;
    
    Ok(tracer)
}

// 手动创建跟踪
async fn manual_tracing_example() -> Result<(), Box<dyn Error>> {
    // 获取全局跟踪器
    let tracer = global::tracer("my-tracer");
    
    // 创建根跨度
    let mut root_span = tracer.start("process_request");
    root_span.set_attribute(opentelemetry::KeyValue::new("http.method", "GET"));
    root_span.set_attribute(opentelemetry::KeyValue::new("http.url", "/api/data"));
    
    // 子操作
    {
        let mut db_span = tracer.start_with_context("database_query", &root_span);
        db_span.set_attribute(opentelemetry::KeyValue::new("db.system", "postgresql"));
        db_span.set_attribute(opentelemetry::KeyValue::new("db.statement", "SELECT * FROM users"));
        
        // 模拟数据库查询
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        
        if rand::random::<f32>() < 0.1 {
            // 10%概率发生错误
            db_span.record_error("数据库连接错误");
            db_span.set_status(opentelemetry::trace::Status::error("连接超时"));
        }
        
        // 子跨度自动结束
    }
    
    // 另一个子操作
    {
        let mut cache_span = tracer.start_with_context("cache_lookup", &root_span);
        cache_span.set_attribute(opentelemetry::KeyValue::new("cache.system", "redis"));
        
        // 模拟缓存查询
        tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
        
        // 子跨度自动结束
    }
    
    // 标记根跨度完成
    root_span.end();
    
    // 确保所有跨度都已导出
    global::shutdown_tracer_provider();
    
    Ok(())
}

// 使用跟踪中间件
use actix_web::{web, App, HttpServer, HttpResponse, Error as ActixError};
use opentelemetry::trace::TraceContextExt;
use opentelemetry_actix::RequestTracing;

// 带跟踪的HTTP处理函数
async fn handle_request() -> Result<HttpResponse, ActixError> {
    // 获取当前跨度
    let span = global::get_text_map_propagator(|prop| {
        prop.extract(&actix_web::HttpRequest::current())
    });
    
    // 在当前跨度上添加属性
    if let Some(span_ctx) = span.span().span_context() {
        span.span().set_attribute(opentelemetry::KeyValue::new("user.id", "1001"));
    }
    
    // 业务逻辑...
    
    Ok(HttpResponse::Ok().body("处理成功"))
}

// 启动带有跟踪的Web服务器
async fn start_traced_server() -> std::io::Result<()> {
    // 初始化跟踪器
    let _ = init_tracer().expect("初始化跟踪器失败");
    
    // 启动服务器
    HttpServer::new(|| {
        App::new()
            .wrap(RequestTracing::new()) // 添加跟踪中间件
            .route("/api/data", web::get().to(handle_request))
    })
    .bind("127.0.0.1:8080")?
    .run()
    .await
}
```

**3. 指标和监控实现**：

```rust
use prometheus::{
    register_counter, register_gauge, register_histogram,
    Counter, Gauge, Histogram,
    Encoder, TextEncoder,
};
use lazy_static::lazy_static;

// 定义应用程序指标
lazy_static! {
    // 请求计数器
    static ref HTTP_REQUESTS_TOTAL: Counter = register_counter!(
        opts!(
            "http_requests_total",
            "请求总数",
            labels! {"handler" => "all"}
        )
    ).unwrap();
    
    // 活跃连接数量
    static ref ACTIVE_CONNECTIONS: Gauge = register_gauge!(
        opts!(
            "active_connections",
            "当前活跃连接数"
        )
    ).unwrap();
    
    // 请求持续时间
    static ref REQUEST_DURATION_SECONDS: Histogram = register_histogram!(
        histogram_opts!(
            "request_duration_seconds",
            "请求持续时间（秒）",
            vec![0.01, 0.05, 0.1, 0.5, 1.0, 5.0]
        )
    ).unwrap();
    
    // 每个路径的请求计数器
    static ref PATH_COUNTER: CounterVec = register_counter_vec!(
        opts!(
            "http_requests_by_path",
            "每个路径的请求数"
        ),
        &["method", "path"]
    ).unwrap();
    
    // 响应状态计数器
    static ref RESPONSE_STATUS_COUNTER: CounterVec = register_counter_vec!(
        opts!(
            "http_responses_by_status",
            "每个状态码的响应数"
        ),
        &["status"]
    ).unwrap();
}

// Prometheus指标导出处理程序
async fn metrics_handler() -> HttpResponse {
    let encoder = TextEncoder::new();
    let metric_families = prometheus::gather();
    let mut buffer = Vec::new();
    encoder.encode(&metric_families, &mut buffer).unwrap();
    
    HttpResponse::Ok()
        .content_type("text/plain")
        .body(String::from_utf8(buffer).unwrap())
}

// 带有指标的HTTP中间件
use actix_web::{
    dev::{Service, Transform, ServiceRequest, ServiceResponse},
    Error,
};
use std::future::{ready, Ready, Future};
use std::pin::Pin;
use std::task::{Context, Poll};
use std::time::Instant;

pub struct MetricsMiddleware;

impl<S, B> Transform<S, ServiceRequest> for MetricsMiddleware
where
    S: Service<ServiceRequest, Response = ServiceResponse<B>, Error = Error>,
    S::Future: 'static,
    B: 'static,
{
    type Response = ServiceResponse<B>;
    type Error = Error;
    type InitError = ();
    type Transform = MetricsMiddlewareService<S>;
    type Future = Ready<Result<Self::Transform, Self::InitError>>;

    fn new_transform(&self, service: S) -> Self::Future {
        ready(Ok(MetricsMiddlewareService { service }))
    }
}

pub struct MetricsMiddlewareService<S> {
    service: S,
}

impl<S, B> Service<ServiceRequest> for MetricsMiddlewareService<S>
where
    S: Service<ServiceRequest, Response = ServiceResponse<B>, Error = Error>,
    S::Future: 'static,
    B: 'static,
{
    type Response = ServiceResponse<B>;
    type Error = Error;
    type Future = Pin<Box<dyn Future<Output = Result<Self::Response, Self::Error>>>>;

    fn poll_ready(&self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        self.service.poll_ready(cx)
    }

    fn call(&self, req: ServiceRequest) -> Self::Future {
        // 增加请求计数
        HTTP_REQUESTS_TOTAL.inc();
        
        // 增加活跃连接数
        ACTIVE_CONNECTIONS.inc();
        
        // 记录路径计数
        let method = req.method().as_str().to_string();
        let path = req.path().to_string();
        PATH_COUNTER.with_label_values(&[&method, &path]).inc();
        
        // 记录请求开始时间
        let start = Instant::now();
        
        let fut = self.service.call(req);
        
        Box::pin(async move {
            // 调用实际服务
            let res = fut.await?;
            
            // 减少活跃连接计数
            ACTIVE_CONNECTIONS.dec();
            
            // 记录持续时间
            let duration = start.elapsed().as_secs_f64();
            REQUEST_DURATION_SECONDS.observe(duration);
            
            // 记录响应状态
            let status = res.status().as_u16().to_string();
            RESPONSE_STATUS_COUNTER.with_label_values(&[&status]).inc();
            
            Ok(res)
        })
    }
}

// 启动带有指标监控的Web服务器
async fn start_monitored_server() -> std::io::Result<()> {
    HttpServer::new(|| {
        App::new()
            .wrap(MetricsMiddleware)  // 添加指标中间件
            .route("/metrics", web::get().to(metrics_handler))  // 指标导出端点
            .route("/api/data", web::get().to(handle_request))
    })
    .bind("127.0.0.1:8080")?
    .run()
    .await
}
```

**4. 健康检查实现**：

```rust
use actix_web::{web, App, HttpServer, HttpResponse, Error as ActixError};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::collections::HashMap;
use serde::Serialize;

// 健康状态
#[derive(Clone, Debug)]
struct HealthState {
    // 系统是否可以接受流量
    ready: Arc<AtomicBool>,
    // 系统是否处于活跃状态
    alive: Arc<AtomicBool>,
    // 各组件健康状态
    components: Arc<parking_lot::RwLock<HashMap<String, ComponentHealth>>>,
}

// 组件健康状态
#[derive(Clone, Debug, Serialize)]
struct ComponentHealth {
    name: String,
    status: HealthStatus,
    details: Option<String>,
    last_check: chrono::DateTime<chrono::Utc>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
enum HealthStatus {
    #[serde(rename = "healthy")]
    Healthy,
    #[serde(rename = "degraded")]
    Degraded,
    #[serde(rename = "unhealthy")]
    Unhealthy,
}

impl HealthState {
    fn new() -> Self {
        Self {
            ready: Arc::new(AtomicBool::new(false)),
            alive: Arc::new(AtomicBool::new(true)),
            components: Arc::new(parking_lot::RwLock::new(HashMap::new())),
        }
    }
    
    // 检查系统是否可以接受流量
    fn is_ready(&self) -> bool {
        self.ready.load(Ordering::Relaxed)
    }
    
    // 检查系统是否处于活跃状态
    fn is_alive(&self) -> bool {
        self.alive.load(Ordering::Relaxed)
    }
    
    // 设置系统就绪状态
    fn set_ready(&self, ready: bool) {
        self.ready.store(ready, Ordering::Relaxed);
    }
    
    // 设置系统活跃状态
    fn set_alive(&self, alive: bool) {
        self.alive.store(alive, Ordering::Relaxed);
    }
    
    // 更新组件健康状态
    fn update_component(&self, name: &str, status: HealthStatus, details: Option<String>) {
        let mut components = self.components.write();
        components.insert(name.to_string(), ComponentHealth {
            name: name.to_string(),
            status,
            details,
            last_check: chrono::Utc::now(),
        });
    }
    
    // 检查所有组件是否健康
    fn all_components_healthy(&self) -> bool {
        let components = self.components.read();
        components.values().all(|c| c.status == HealthStatus::Healthy)
    }
    
    // 获取健康状态报告
    fn get_health_report(&self) -> HashMap<String, serde_json::Value> {
        let mut report = HashMap::new();
        
        report.insert("status".to_string(), 
            serde_json::json!(if self.all_components_healthy() {"healthy"} else {"degraded"}));
        
        report.insert("ready".to_string(), serde_json::json!(self.is_ready()));
        report.insert("alive".to_string(), serde_json::json!(self.is_alive()));
        
        let components = self.components.read();
        let components_json = serde_json::json!(components.values().collect::<Vec<_>>());
        report.insert("components".to_string(), components_json);
        
        report
    }
}

// 健康检查处理程序
async fn health_handler(health_state: web::Data<HealthState>) -> HttpResponse {
    let report = health_state.get_health_report();
    
    let status = if health_state.all_components_healthy() {
        http::StatusCode::OK
    } else {
        http::StatusCode::SERVICE_UNAVAILABLE
    };
    
    HttpResponse::build(status)
        .json(report)
}

// 就绪检查处理程序
async fn readiness_handler(health_state: web::Data<HealthState>) -> HttpResponse {
    if health_state.is_ready() {
        HttpResponse::Ok().finish()
    } else {
        HttpResponse::ServiceUnavailable().finish()
    }
}

// 活跃检查处理程序
async fn liveness_handler(health_state: web::Data<HealthState>) -> HttpResponse {
    if health_state.is_alive() {
        HttpResponse::Ok().finish()
    } else {
        HttpResponse::ServiceUnavailable().finish()
    }
}

// 定期健康检查任务
struct HealthChecker {
    health_state: Arc<HealthState>,
    db_pool: Arc<DbPool>, // 数据库连接池
    cache_client: Arc<CacheClient>, // 缓存客户端
    external_service_client: Arc<ExternalServiceClient>, // 外部服务客户端
}

impl HealthChecker {
    fn new(
        health_state: Arc<HealthState>,
        db_pool: Arc<DbPool>,
        cache_client: Arc<CacheClient>,
        external_service_client: Arc<ExternalServiceClient>,
    ) -> Self {
        Self {
            health_state,
            db_pool,
            cache_client,
            external_service_client,
        }
    }
    
    // 启动定期健康检查
    async fn start_periodic_checks(&self) {
        let health_state = self.health_state.clone();
        let db_pool = self.db_pool.clone();
        let cache_client = self.cache_client.clone();
        let external_service_client = self.external_service_client.clone();
        
        tokio::spawn(async move {
            loop {
                // 检查数据库
                match db_pool.check_health().await {
                    Ok(_) => {
                        health_state.update_component("database", HealthStatus::Healthy, None);
                    },
                    Err(e) => {
                        health_state.update_component("database", HealthStatus::Unhealthy, Some(e.to_string()));
                    }
                }
                
                // 检查缓存
                match cache_client.check_health().await {
                    Ok(_) => {
                        health_state.update_component("cache", HealthStatus::Healthy, None);
                    },
                    Err(e) => {
                        health_state.update_component("cache", HealthStatus::Unhealthy, Some(e.to_string()));
                    }
                }
                
                // 检查外部服务
                match external_service_client.check_health().await {
                    Ok(_) => {
                        health_state.update_component("external_service", HealthStatus::Healthy, None);
                    },
                    Err(e) => {
                        health_state.update_component("external_service", HealthStatus::Unhealthy, Some(e.to_string()));
                    }
                }
                
                // 根据组件状态更新整体就绪状态
                health_state.set_ready(health_state.all_components_healthy());
                
                // 等待下一个检查周期
                tokio::time::sleep(std::time::Duration::from_secs(30)).await;
            }
        });
    }
    
    // 优雅关闭
    async fn start_shutdown(&self) {
        // 首先标记为不就绪，拒绝新请求
        self.health_state.set_ready(false);
        
        // 等待一段时间，让现有请求完成
        tokio::time::sleep(std::time::Duration::from_secs(10)).await;
        
        // 然后标记为不活跃，准备最终关闭
        self.health_state.set_alive(false);
    }
}
```

### 4.4 分布式配置管理

在分布式系统中，配置管理必须能够支持动态更新、环境隔离、敏感信息保护等需求。

**1. 分层配置系统**：

```rust
use serde::{Serialize, Deserialize};
use std::sync::{Arc, RwLock};
use std::collections::HashMap;
use std::path::Path;
use std::fs;
use notify::{Watcher, RecursiveMode, watcher};
use std::time::Duration;
use std::sync::mpsc::channel;

// 配置源特征
trait ConfigSource: Send + Sync {
    fn load(&self) -> Result<HashMap<String, serde_json::Value>, Box<dyn std::error::Error>>;
    fn name(&self) -> &str;
}

// 文件配置源
struct FileConfigSource {
    name: String,
    path: String,
}

impl FileConfigSource {
    fn new(name: &str, path: &str) -> Self {
        Self {
            name: name.to_string(),
            path: path.to_string(),
        }
    }
}

impl ConfigSource for FileConfigSource {
    fn load(&self) -> Result<HashMap<String, serde_json::Value>, Box<dyn std::error::Error>> {
        let content = fs::read_to_string(&self.path)?;
        let config: HashMap<String, serde_json::Value> = serde_json::from_str(&content)?;
        Ok(config)
    }
    
    fn name(&self) -> &str {
        &self.name
    }
}

// 环境变量配置源
struct EnvConfigSource {
    name: String,
    prefix: String,
}

impl EnvConfigSource {
    fn new(name: &str, prefix: &str) -> Self {
        Self {
            name: name.to_string(),
            prefix: prefix.to_string(),
        }
    }
}

impl ConfigSource for EnvConfigSource {
    fn load(&self) -> Result<HashMap<String, serde_json::Value>, Box<dyn std::error::Error>> {
        let mut config = HashMap::new();
        
        for (key, value) in std::env::vars() {
            if key.starts_with(&self.prefix) {
                let config_key = key[self.prefix.len()..].to_lowercase();
                config.insert(config_key, serde_json::Value::String(value));
            }
        }
        
        Ok(config)
    }
    
    fn name(&self) -> &str {
        &self.name
    }
}

// 远程配置源
struct RemoteConfigSource {
    name: String,
    endpoint: String,
    client: reqwest::Client,
}

impl RemoteConfigSource {
    fn new(name: &str, endpoint: &str) -> Self {
        Self {
            name: name.to_string(),
            endpoint: endpoint.to_string(),
            client: reqwest::Client::new(),
        }
    }
}

impl ConfigSource for RemoteConfigSource {
    fn load(&self) -> Result<HashMap<String, serde_json::Value>, Box<dyn std::error::Error>> {
        let runtime = tokio::runtime::Runtime::new()?;
        
        runtime.block_on(async {
            let response = self.client.get(&self.endpoint)
                .send()
                .await?
                .error_for_status()?
                .json::<HashMap<String, serde_json::Value>>()
                .await?;
            
            Ok::<_, Box<dyn std::error::Error>>(response)
        })
    }
    
    fn name(&self) -> &str {
        &self.name
    }
}

// 配置管理器
struct ConfigManager {
    sources: Vec<Box<dyn ConfigSource>>,
    config: RwLock<HashMap<String, serde_json::Value>>,
    subscribers: RwLock<Vec<Box<dyn Fn(&str, &serde_json::Value) + Send + Sync>>>,
}

impl ConfigManager {
    fn new() -> Self {
        Self {
            sources: Vec::new(),
            config: RwLock::new(HashMap::new()),
            subscribers: RwLock::new(Vec::new()),
        }
    }
    
    fn add_source(&mut self, source: Box<dyn ConfigSource>) {
        self.sources.push(source);
    }
    
    fn load_all(&self) -> Result<(), Box<dyn std::error::Error>> {
        let mut config = HashMap::new();
        
        // 按优先级顺序加载配置源（后面的覆盖前面的）
        for source in &self.sources {
            match source.load() {
                Ok(source_config) => {
                    println!("从源 {} 加载配置", source.name());
                    
                    // 合并配置
                    for (key, value) in source_config {
                        config.insert(key, value);
                    }
                },
                Err(e) => {
                    println!("从源 {} 加载配置失败: {}", source.name(), e);
                }
            }
        }
        
        // 更新配置并通知订阅者
        {
            let mut current_config = self.config.write().unwrap();
            
            // 找出变化的配置项
            let mut changed_keys = Vec::new();
            for (key, value) in &config {
                if !current_config.contains_key(key) || current_config[key] != *value {
                    changed_keys.push((key.clone(), value.clone()));
                }
            }
            
            // 更新配置
            *current_config = config;
            
            // 释放锁再通知订阅者，避免死锁
            drop(current_config);
            
            // 通知订阅者
            let subscribers = self.subscribers.read().unwrap();
            for (key, value) in changed_keys {
                for subscriber in subscribers.iter() {
                    subscriber(&key, &value);
                }
            }
        }
        
        Ok(())
    }
    
    fn get<T: serde::de::DeserializeOwned>(&self, key: &str) -> Option<T> {
        let config = self.config.read().unwrap();
        
        config.get(key)
            .and_then(|value| serde_json::from_value(value.clone()).ok())
    }
    
    fn subscribe<F>(&self, callback: F)
    where
        F: Fn(&str, &serde_json::Value) + Send + Sync + 'static
    {
        let mut subscribers = self.subscribers.write().unwrap();
        subscribers.push(Box::new(callback));
    }
    
    // 监视配置文件变化
    fn watch_file_changes(&self, path: &str) -> Result<(), Box<dyn std::error::Error>> {
        let path = path.to_string();
        let self_arc = Arc::new(self.clone());
        
        std::thread::spawn(move || {
            let (tx, rx) = channel();
            let mut watcher = watcher(tx, Duration::from_secs(10)).unwrap();
            watcher.watch(&path, RecursiveMode::NonRecursive).unwrap();
            
            println!("开始监视配置文件: {}", path);
            
            loop {
                match rx.recv() {
                    Ok(event) => {
                        println!("检测到文件变化: {:?}", event);
                        if let Err(e) = self_arc.load_all() {
                            println!("重新加载配置失败: {}", e);
                        } else {
                            println!("成功重新加载配置");
                        }
                    },
                    Err(e) => println!("监视错误: {}", e),
                }
            }
        });
        
        Ok(())
    }
}

impl Clone for ConfigManager {
    fn clone(&self) -> Self {
        Self {
            sources: self.sources.iter()
                .map(|s| Box::new(*s.clone()) as Box<dyn ConfigSource>)
                .collect(),
            config: RwLock::new(self.config.read().unwrap().clone()),
            subscribers: RwLock::new(Vec::new()),
        }
    }
}

// 使用示例
fn config_example() -> Result<(), Box<dyn std::error::Error>> {
    let mut config_manager = ConfigManager::new();
    
    // 添加配置源（按优先级顺序）
    config_manager.add_source(Box::new(FileConfigSource::new(
        "defaults",
        "config/defaults.json"
    )));
    
    config_manager.add_source(Box::new(FileConfigSource::new(
        "environment",
        "config/production.json"
    )));
    
    config_manager.add_source(Box::new(EnvConfigSource::new(
        "environment-vars",
        "APP_"
    )));
    
    config_manager.add_source(Box::new(RemoteConfigSource::new(
        "remote-config",
        "https://config.example.com/api/config"
    )));
    
    // 加载所有配置
    config_manager.load_all()?;
    
    // 订阅配置变化
    config_manager.subscribe(|key, value| {
        println!("配置变化: {} = {}", key, value);
    });
    
    // 获取配置
    if let Some(db_url) = config_manager.get::<String>("database.url") {
        println!("数据库URL: {}", db_url);
    }
    
    // 监视文件变化
    config_manager.watch_file_changes("config/production.json")?;
    
    // 应用继续运行...
    
    Ok(())
}

// 带有类型的配置结构
#[derive(Debug, Serialize, Deserialize)]
struct AppConfig {
    server: ServerConfig,
    database: DatabaseConfig,
    logging: LoggingConfig,
}

#[derive(Debug, Serialize, Deserialize)]
struct ServerConfig {
    host: String,
    port: u16,
    threads: u32,
}

#[derive(Debug, Serialize, Deserialize)]
struct DatabaseConfig {
    url: String,
    pool_size: u32,
    timeout_seconds: u32,
}

#[derive(Debug, Serialize, Deserialize)]
struct LoggingConfig {
    level: String,
    file: Option<String>,
}

// 使用类型化配置
fn typed_config_example() -> Result<(), Box<dyn std::error::Error>> {
    let mut config_manager = ConfigManager::new();
    
    // 添加配置源
    config_manager.add_source(Box::new(FileConfigSource::new(
        "defaults",
        "config/defaults.json"
    )));
    
    // 加载配置
    config_manager.load_all()?;
    
    // 获取类型化配置（使用路径获取整个结构）
    if let Some(config) = config_manager.get::<AppConfig>("") {
        println!("服务器配置: {:?}", config.server);
        println!("数据库配置: {:?}", config.database);
        println!("日志配置: {:?}", config.logging);
    } else {
        println!("无法加载类型化配置");
    }
    
    // 也可以单独获取某个部分
    if let Some(db_config) = config_manager.get::<DatabaseConfig>("database") {
        println!("单独获取数据库配置: {:?}", db_config);
    }
    
    Ok(())
}
```

**2. 安全配置管理**：

```rust
use aes_gcm::{Aes256Gcm, Key, Nonce};
use aes_gcm::aead::{Aead, NewAead};
use rand::RngCore;
use base64::{Engine as _, engine::general_purpose::STANDARD as BASE64};

// 加密配置源
struct EncryptedConfigSource {
    name: String,
    path: String,
    key: [u8; 32],
}

impl EncryptedConfigSource {
    fn new(name: &str, path: &str, key: &[u8; 32]) -> Self {
        Self {
            name: name.to_string(),
            path: path.to_string(),
            key: *key,
        }
    }
    
    fn decrypt(&self, ciphertext: &str) -> Result<String, Box<dyn std::error::Error>> {
        // 解码Base64
        let decoded = BASE64.decode(ciphertext)?;
        
        // 提取nonce和密文
        if decoded.len() < 12 {
            return Err("密文太短".into());
        }
        
        let nonce_bytes = &decoded[..12];
        let ciphertext_bytes = &decoded[12..];
        
        // 创建Nonce
        let nonce = Nonce::from_slice(nonce_bytes);
        
        // 创建密钥
        let key = Key::from_slice(&self.key);
        let cipher = Aes256Gcm::new(key);
        
        // 解密
        let plaintext = cipher.decrypt(nonce, ciphertext_bytes)
            .map_err(|e| format!("解密失败: {:?}", e))?;
        
        // 转换为字符串
        let plaintext_str = String::from_utf8(plaintext)?;
        
        Ok(plaintext_str)
    }
}

impl ConfigSource for EncryptedConfigSource {
    fn load(&self) -> Result<HashMap<String, serde_json::Value>, Box<dyn std::error::Error>> {
        // 读取加密配置文件
        let encrypted_content = fs::read_to_string(&self.path)?;
        
        // 解密
        let decrypted_content = self.decrypt(&encrypted_content)?;
        
        // 解析JSON
        let config: HashMap<String, serde_json::Value> = serde_json::from_str(&decrypted_content)?;
        
        Ok(config)
    }
    
    fn name(&self) -> &str {
        &self.name
    }
}

// 配置加密工具
struct ConfigEncryptor {
    key: [u8; 32],
}

impl ConfigEncryptor {
    fn new(key: &[u8; 32]) -> Self {
        Self {
            key: *key,
        }
    }
    
    fn encrypt(&self, plaintext: &str) -> Result<String, Box<dyn std::error::Error>> {
        // 创建随机nonce
        let mut nonce_bytes = [0u8; 12];
        rand::thread_rng().fill_bytes(&mut nonce_bytes);
        let nonce = Nonce::from_slice(&nonce_bytes);
        
        // 创建密钥
        let key = Key::from_slice(&self.key);
        let cipher = Aes256Gcm::new(key);
        
        // 加密
        let ciphertext = cipher.encrypt(nonce, plaintext.as_bytes())
            .map_err(|e| format!("加密失败: {:?}", e))?;
        
        // 组合nonce和密文
        let mut result = Vec::with_capacity(nonce_bytes.len() + ciphertext.len());
        result.extend_from_slice(&nonce_bytes);
        result.extend_from_slice(&ciphertext);
        
        // 编码为Base64
        let encoded = BASE64.encode(result);
        
        Ok(encoded)
    }
    
    fn encrypt_file(&self, input_path: &str, output_path: &str) -> Result<(), Box<dyn std::error::Error>> {
        // 读取明文配置
        let plaintext = fs::read_to_string(input_path)?;
        
        // 加密
        let encrypted = self.encrypt(&plaintext)?;
        
        // 写入加密文件
        fs::write(output_path, encrypted)?;
        
        Ok(())
    }
}

// 使用示例
fn secure_config_example() -> Result<(), Box<dyn std::error::Error>> {
    // 通常会从环境变量或密钥管理系统获取
    let key = [0u8; 32]; // 实际应用中使用随机生成的密钥
    
    // 创建配置加密工具
    let encryptor = ConfigEncryptor::new(&key);
    
    // 加密配置文件
    encryptor.encrypt_file("config/secrets.json", "config/secrets.enc.json")?;
    
    // 创建配置管理器
    let mut config_manager = ConfigManager::new();
    
    // 添加加密配置源
    config_manager.add_source(Box::new(EncryptedConfigSource::new(
        "encrypted-secrets",
        "config/secrets.enc.json",
        &key
    )));
    
    // 加载配置
    config_manager.load_all()?;
    
    // 获取敏感配置
    if let Some(api_key) = config_manager.get::<String>("api.key") {
        println!("API密钥: {}", api_key);
    }
    
    Ok(())
}
```

**3. 可观察配置模式**：

```rust
use std::sync::Arc;
use tokio::sync::RwLock;

// 响应式配置
#[derive(Debug, Clone)]
struct ReactiveConfig<T> {
    value: Arc<RwLock<T>>,
    version: Arc<RwLock<u64>>,
}

impl<T: Clone> ReactiveConfig<T> {
    fn new(initial: T) -> Self {
        Self {
            value: Arc::new(RwLock::new(initial)),
            version: Arc::new(RwLock::new(0)),
        }
    }
    
    async fn get(&self) -> T {
        let value = self.value.read().await;
        value.clone()
    }
    
    async fn set(&self, new_value: T) {
        let mut value = self.value.write().await;
        *value = new_value;
        
        let mut version = self.version.write().await;
        *version += 1;
    }
    
    async fn get_version(&self) -> u64 {
        let version = self.version.read().await;
        *version
    }
    
    // 创建一个观察者，当配置变化时调用回调函数
    async fn observe<F>(&self, mut callback: F)
    where
        F: FnMut(T) + Send + 'static,
        T: Send + Sync + 'static
    {
        let self_clone = self.clone();
        let initial_version = self.get_version().await;
        
        tokio::spawn(async move {
            let mut last_version = initial_version;
            
            loop {
                // 获取当前版本
                let current_version = self_clone.get_version().await;
                
                // 如果版本变了，调用回调
                if current_version > last_version {
                    let value = self_clone.get().await;
                    callback(value);
                    last_version = current_version;
                }
                
                // 避免过于频繁检查
                tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
            }
        });
    }
}

// 使用示例
async fn reactive_config_example() {
    // 创建响应式配置
    let config = ReactiveConfig::new(ServerConfig {
        host: "localhost".to_string(),
        port: 8080,
        threads: 4,
    });
    
    // 观察配置变化
    let config_clone = config.clone();
    config.observe(move |new_config| {
        println!("配置变化: {:?}", new_config);
        // 这里可以进行服务重新配置
    }).await;
    
    // 获取配置
    let server_config = config.get().await;
    println!("当前配置: {:?}", server_config);
    
    // 修改配置
    config.set(ServerConfig {
        host: "0.0.0.0".to_string(),
        port: 9000,
        threads: 8,
    }).await;
    
    // 等待观察者处理
    tokio::time::sleep(tokio::time::Duration::from_millis(200)).await;
}
```

### 4.5 分布式中间件集成

在分布式系统中，常需要集成各种中间件，如消息队列、缓存系统等。

**1. 消息队列集成**：

```rust
use async_trait::async_trait;
use serde::{Serialize, Deserialize};
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::mpsc;
use futures::{Stream, StreamExt};
use std::pin::Pin;
use std::task::{Context, Poll};

// 消息接口
#[async_trait]
trait MessageQueue<T: Serialize + for<'de> Deserialize<'de> + Send + Sync + 'static> {
    // 发送消息
    async fn send(&self, destination: &str, message: T) -> Result<(), Box<dyn std::error::Error>>;
    
    // 接收消息（返回流）
    async fn receive(&self, source: &str) -> Result<MessageStream<T>, Box<dyn std::error::Error>>;
    
    // 创建消费者组
    async fn create_consumer_group(&self, group: &str, topic: &str) -> Result<(), Box<dyn std::error::Error>>;
    
    // 确认消息处理完成
    async fn ack(&self, source: &str, message_id: &str) -> Result<(), Box<dyn std::error::Error>>;
}

// 消息流
struct MessageStream<T> {
    receiver: mpsc::Receiver<Message<T>>,
}

impl<T> Stream for MessageStream<T> {
    type Item = Message<T>;
    
    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        Pin::new(&mut self.receiver).poll_recv(cx)
    }
}

// 消息结构
#[derive(Clone, Debug)]
struct Message<T> {
    id: String,
    payload: T,
    timestamp: chrono::DateTime<chrono::Utc>,
    headers: std::collections::HashMap<String, String>,
    redelivered: bool,
}

// Kafka集成实现
#[derive(Clone)]
struct KafkaMessageQueue {
    producer: Arc<rdkafka::producer::FutureProducer>,
    consumer_config: rdkafka::ClientConfig,
}

impl KafkaMessageQueue {
    fn new(brokers: &str) -> Result<Self, Box<dyn std::error::Error>> {
        // 创建生产者配置
        let mut producer_config = rdkafka::ClientConfig::new();
        producer_config.set("bootstrap.servers", brokers);
        producer_config.set("message.timeout.ms", "5000");
        
        // 创建生产者
        let producer: rdkafka::producer::FutureProducer = producer_config.create()?;
        
        // 创建消费者配置
        let mut consumer_config = rdkafka::ClientConfig::new();
        consumer_config.set("bootstrap.servers", brokers);
        consumer_config.set("enable.auto.commit", "false");
        consumer_config.set("auto.offset.reset", "earliest");
        
        Ok(Self {
            producer: Arc::new(producer),
            consumer_config,
        })
    }
}

#[async_trait]
impl<T: Serialize + for<'de> Deserialize<'de> + Send + Sync + 'static> MessageQueue<T> for KafkaMessageQueue {
    async fn send(&self, topic: &str, message: T) -> Result<(), Box<dyn std::error::Error>> {
        // 序列化消息
        let payload = serde_json::to_string(&message)?;
        
        // 创建记录
        let record = rdkafka::producer::FutureRecord::to(topic)
            .payload(&payload)
            .key(&uuid::Uuid::new_v4().to_string());
        
        // 发送消息
        let result = self.producer.send(record, Duration::from_secs(5)).await;
        
        match result {
            Ok(_) => Ok(()),
            Err((e, _)) => Err(Box::new(e)),
        }
    }
    
    async fn receive(&self, topic: &str) -> Result<MessageStream<T>, Box<dyn std::error::Error>> {
        // 克隆消费者配置
        let mut config = self.consumer_config.clone();
        config.set("group.id", &uuid::Uuid::new_v4().to_string());
        
        // 创建消费者
        let consumer: rdkafka::consumer::StreamConsumer = config.create()?;
        
        // 订阅主题
        consumer.subscribe(&[topic])?;
        
        // 创建通道
        let (tx, rx) = mpsc::channel(100);
        
        // 启动消费线程
        let consumer = Arc::new(consumer);
        let consumer_clone = consumer.clone();
        
        tokio::spawn(async move {
            let mut message_stream = consumer_clone.stream();
            
            while let Some(message_result) = message_stream.next().await {
                match message_result {
                    Ok(borrowed_message) => {
                        if let Some(payload) = borrowed_message.payload() {
                            // 尝试反序列化消息
                            if let Ok(typed_message) = serde_json::from_slice::<T>(payload) {
                                // 创建消息结构
                                let message = Message {
                                    id: borrowed_message.offset().to_string(),
                                    payload: typed_message,
                                    timestamp: chrono::Utc::now(),
                                    headers: HashMap::new(),
                                    redelivered: false,
                                };
                                
                                // 发送到通道
                                if tx.send(message).await.is_err() {
                                    break;
                                }
                            }
                        }
                    },
                    Err(e) => {
                        eprintln!("Kafka消费错误: {}", e);
                    }
                }
            }
        });
        
        Ok(MessageStream { receiver: rx })
    }
    
    async fn create_consumer_group(&self, group: &str, topic: &str) -> Result<(), Box<dyn std::error::Error>> {
        // 创建消费者组配置
        let mut config = self.consumer_config.clone();
        config.set("group.id", group);
        
        // 创建消费者
        let consumer: rdkafka::consumer::StreamConsumer = config.create()?;
        
        // 订阅主题（这会创建消费者组）
        consumer.subscribe(&[topic])?;
        
        // 等待一小段时间，确保消费者组被创建
        tokio::time::sleep(Duration::from_millis(100)).await;
        
        Ok(())
    }
    
    async fn ack(&self, topic: &str, message_id: &str) -> Result<(), Box<dyn std::error::Error>> {
        // Kafka通过提交偏移量来确认消息
        // 这里简化处理，实际应用中需要更复杂的逻辑
        println!("确认Kafka消息: {} in {}", message_id, topic);
        
        Ok(())
    }
}

// RabbitMQ集成实现
struct RabbitMQMessageQueue {
    connection: Arc<lapin::Connection>,
}

impl RabbitMQMessageQueue {
    async fn new(uri: &str) -> Result<Self, Box<dyn std::error::Error>> {
        // 创建连接
        let connection = lapin::Connection::connect(
            uri,
            lapin::ConnectionProperties::default(),
        ).await?;
        
        Ok(Self {
            connection: Arc::new(connection),
        })
    }
}

#[async_trait]
impl<T: Serialize + for<'de> Deserialize<'de> + Send + Sync + 'static> MessageQueue<T> for RabbitMQMessageQueue {
    async fn send(&self, queue: &str, message: T) -> Result<(), Box<dyn std::error::Error>> {
        // 创建通道
        let channel = self.connection.create_channel().await?;
        
        // 声明队列
        channel.queue_declare(
            queue,
            lapin::options::QueueDeclareOptions::default(),
            lapin::types::FieldTable::default(),
        ).await?;
        
        // 序列化消息
        let payload = serde_json::to_string(&message)?;
        
        // 发送消息
        channel.basic_publish(
            "",
            queue,
            lapin::options::BasicPublishOptions::default(),
            payload.as_bytes(),
            lapin::BasicProperties::default(),
        ).await?;
        
        Ok(())
    }
    
    async fn receive(&self, queue: &str) -> Result<MessageStream<T>, Box<dyn std::error::Error>> {
        // 创建通道
        let channel = self.connection.create_channel().await?;
        
        // 声明队列
        channel.queue_declare(
            queue,
            lapin::options::QueueDeclareOptions::default(),
            lapin::types::FieldTable::default(),
        ).await?;
        
        // 创建消费者
        let consumer = channel.basic_consume(
            queue,
            &uuid::Uuid::new_v4().to_string(),
            lapin::options::BasicConsumeOptions::default(),
            lapin::types::FieldTable::default(),
        ).await?;
        
        // 创建通道
        let (tx, rx) = mpsc::channel(100);
        
        let channel_clone = channel.clone();
        
        // 启动消费线程
        tokio::spawn(async move {
            let mut delivery_stream = consumer.into_stream();
            
            while let Some(delivery_result) = delivery_stream.next().await {
                match delivery_result {
                    Ok(delivery) => {
                        // 尝试反序列化消息
                        if let Ok(typed_message) = serde_json::from_slice::<T>(&delivery.data) {
                            // 创建消息结构
                            let message = Message {
                                id: delivery.delivery_tag.to_string(),
                                payload: typed_message,
                                timestamp: chrono::Utc::now(),
                                headers: HashMap::new(),
                                redelivered: delivery.redelivered,
                            };
                            
                            // 发送到通道
                            if tx.send(message).await.is_err() {
                                break;
                            }
                        }
                        
                        // 注意：这里没有自动确认消息，需要显式调用ack
                    },
                    Err(e) => {
                        eprintln!("RabbitMQ消费错误: {}", e);
                    }
                }
            }
        });
        
        Ok(MessageStream { receiver: rx })
    }
    
    async fn create_consumer_group(&self, _group: &str, queue: &str) -> Result<(), Box<dyn std::error::Error>> {
        // RabbitMQ没有直接的消费者组概念，但可以通过队列绑定实现类似功能
        // 这里简化为创建队列
        let channel = self.connection.create_channel().await?;
        
        channel.queue_declare(
            queue,
            lapin::options::QueueDeclareOptions::default(),
            lapin::types::FieldTable::default(),
        ).await?;
        
        Ok(())
    }
    
    async fn ack(&self, _queue: &str, message_id: &str) -> Result<(), Box<dyn std::error::Error>> {
        // 创建通道
        let channel = self.connection.create_channel().await?;
        
        // 解析消息ID为投递标签
        let delivery_tag = message_id.parse::<u64>()?;
        
        // 确认消息
        channel.basic_ack(
            delivery_tag,
            lapin::options::BasicAckOptions::default(),
        ).await?;
        
        Ok(())
    }
}

// Redis Streams集成实现
struct RedisStreamsMessageQueue {
    client: Arc<redis::Client>,
    pool: Arc<r2d2::Pool<redis::Client>>,
}

impl RedisStreamsMessageQueue {
    fn new(uri: &str) -> Result<Self, Box<dyn std::error::Error>> {
        // 创建客户端
        let client = redis::Client::open(uri)?;
        
        // 创建连接池
        let pool = r2d2::Pool::builder()
            .max_size(15)
            .build(client.clone())?;
        
        Ok(Self {
            client: Arc::new(client),
            pool: Arc::new(pool),
        })
    }
}

#[async_trait]
impl<T: Serialize + for<'de> Deserialize<'de> + Send + Sync + 'static> MessageQueue<T> for RedisStreamsMessageQueue {

async fn send(&self, stream: &str, message: T) -> Result<(), Box<dyn std::error::Error>> {
    // 获取连接
    let mut conn = self.pool.get()?;
    
    // 序列化消息
    let payload = serde_json::to_string(&message)?;
    
    // 添加到流
    let _: String = redis::cmd("XADD")
        .arg(stream)
        .arg("*")  // 自动生成ID
        .arg("payload")
        .arg(payload)
        .query(&mut *conn)?;
    
    Ok(())
}

async fn receive(&self, stream: &str) -> Result<MessageStream<T>, Box<dyn std::error::Error>> {
    // 获取连接
    let client = self.client.clone();
    
    // 创建通道
    let (tx, rx) = mpsc::channel(100);
    
    // 生成消费者ID
    let consumer_id = uuid::Uuid::new_v4().to_string();
    
    // 启动消费线程
    tokio::spawn(async move {
        // 创建异步连接
        let mut conn = match client.get_async_connection().await {
            Ok(conn) => conn,
            Err(e) => {
                eprintln!("Redis连接错误: {}", e);
                return;
            }
        };
        
        // 从最新消息开始消费
        let mut last_id = "$".to_string();
        
        loop {
            // 读取新消息
            let result: Result<Vec<redis::Value>, redis::RedisError> = redis::cmd("XREAD")
                .arg("COUNT")
                .arg(10)  // 每次最多读取10条
                .arg("BLOCK")
                .arg(5000)  // 阻塞5秒
                .arg("STREAMS")
                .arg(stream)
                .arg(&last_id)
                .query_async(&mut conn)
                .await;
            
            match result {
                Ok(values) => {
                    if let Some(redis::Value::Bulk(stream_data)) = values.get(0) {
                        if let Some(redis::Value::Bulk(messages)) = stream_data.get(1) {
                            for message_value in messages {
                                if let redis::Value::Bulk(message_parts) = message_value {
                                    if message_parts.len() >= 2 {
                                        // 获取消息ID
                                        if let redis::Value::Data(id_bytes) = &message_parts[0] {
                                            let id = String::from_utf8_lossy(id_bytes).to_string();
                                            last_id = id.clone();
                                            
                                            // 获取消息内容
                                            if let redis::Value::Bulk(fields) = &message_parts[1] {
                                                for i in (0..fields.len()).step_by(2) {
                                                    if i + 1 < fields.len() {
                                                        if let (redis::Value::Data(field_name), redis::Value::Data(field_value)) = (&fields[i], &fields[i+1]) {
                                                            let field = String::from_utf8_lossy(field_name).to_string();
                                                            
                                                            if field == "payload" {
                                                                let payload_str = String::from_utf8_lossy(field_value).to_string();
                                                                
                                                                // 反序列化消息
                                                                if let Ok(typed_message) = serde_json::from_str::<T>(&payload_str) {
                                                                    // 创建消息结构
                                                                    let message = Message {
                                                                        id: id.clone(),
                                                                        payload: typed_message,
                                                                        timestamp: chrono::Utc::now(),
                                                                        headers: HashMap::new(),
                                                                        redelivered: false,
                                                                    };
                                                                    
                                                                    // 发送到通道
                                                                    if tx.send(message).await.is_err() {
                                                                        return;
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                },
                Err(e) => {
                    eprintln!("Redis流读取错误: {}", e);
                    tokio::time::sleep(Duration::from_secs(1)).await;
                }
            }
        }
    });
    
    Ok(MessageStream { receiver: rx })
}

async fn create_consumer_group(&self, group: &str, stream: &str) -> Result<(), Box<dyn std::error::Error>> {
    // 获取连接
    let mut conn = self.pool.get()?;
    
    // 检查流是否存在，不存在则创建
    let exists: bool = redis::cmd("EXISTS")
        .arg(stream)
        .query(&mut *conn)?;
    
    if !exists {
        // 创建空流
        let _: String = redis::cmd("XADD")
            .arg(stream)
            .arg("*")
            .arg("_init")
            .arg("true")
            .query(&mut *conn)?;
    }
    
    // 创建消费者组
    // 忽略组已存在的错误
    let result: Result<String, redis::RedisError> = redis::cmd("XGROUP")
        .arg("CREATE")
        .arg(stream)
        .arg(group)
        .arg("0")  // 从头开始消费
        .arg("MKSTREAM")  // 如果流不存在则创建
        .query(&mut *conn);
    
    match result {
        Ok(_) => Ok(()),
        Err(e) => {
            if e.to_string().contains("BUSYGROUP") {
                // 组已存在，不是错误
                Ok(())
            } else {
                Err(Box::new(e))
            }
        }
    }
}

async fn ack(&self, stream: &str, message_id: &str) -> Result<(), Box<dyn std::error::Error>> {
    // 获取连接
    let mut conn = self.pool.get()?;
    
    // 在Redis Streams中，通常需要指定消费者组进行确认
    // 这里简化处理，直接删除消息（实际应用中不要这样做！）
    let _: () = redis::cmd("XDEL")
        .arg(stream)
        .arg(message_id)
        .query(&mut *conn)?;
    
    Ok(())
}
```

**2. 分布式缓存集成**：

```rust
use async_trait::async_trait;
use std::time::Duration;
use std::sync::Arc;
use serde::{Serialize, Deserialize};

// 缓存接口
#[async_trait]
trait DistributedCache {
    // 获取值
    async fn get<T: for<'de> Deserialize<'de> + Send + 'static>(&self, key: &str) -> Result<Option<T>, Box<dyn std::error::Error>>;
    
    // 设置值
    async fn set<T: Serialize + Send + 'static>(&self, key: &str, value: T, ttl: Option<Duration>) -> Result<(), Box<dyn std::error::Error>>;
    
    // 删除值
    async fn delete(&self, key: &str) -> Result<bool, Box<dyn std::error::Error>>;
    
    // 检查键是否存在
    async fn exists(&self, key: &str) -> Result<bool, Box<dyn std::error::Error>>;
    
    // 设置过期时间
    async fn expire(&self, key: &str, ttl: Duration) -> Result<bool, Box<dyn std::error::Error>>;
    
    // 递增操作
    async fn increment(&self, key: &str, amount: i64) -> Result<i64, Box<dyn std::error::Error>>;
    
    // 设置如果不存在
    async fn set_nx<T: Serialize + Send + 'static>(&self, key: &str, value: T, ttl: Option<Duration>) -> Result<bool, Box<dyn std::error::Error>>;
}

// Redis缓存实现
struct RedisCache {
    client: Arc<redis::Client>,
    pool: Arc<r2d2::Pool<redis::Client>>,
}

impl RedisCache {
    fn new(uri: &str) -> Result<Self, Box<dyn std::error::Error>> {
        // 创建客户端
        let client = redis::Client::open(uri)?;
        
        // 创建连接池
        let pool = r2d2::Pool::builder()
            .max_size(15)
            .build(client.clone())?;
        
        Ok(Self {
            client: Arc::new(client),
            pool: Arc::new(pool),
        })
    }
}

#[async_trait]
impl DistributedCache for RedisCache {
    async fn get<T: for<'de> Deserialize<'de> + Send + 'static>(&self, key: &str) -> Result<Option<T>, Box<dyn std::error::Error>> {
        // 获取连接
        let mut conn = self.pool.get()?;
        
        // 获取值
        let result: Option<String> = redis::cmd("GET")
            .arg(key)
            .query(&mut *conn)
            .ok();
        
        // 反序列化
        match result {
            Some(value) => {
                let deserialized = serde_json::from_str(&value)?;
                Ok(Some(deserialized))
            },
            None => Ok(None),
        }
    }
    
    async fn set<T: Serialize + Send + 'static>(&self, key: &str, value: T, ttl: Option<Duration>) -> Result<(), Box<dyn std::error::Error>> {
        // 获取连接
        let mut conn = self.pool.get()?;
        
        // 序列化值
        let serialized = serde_json::to_string(&value)?;
        
        // 设置值
        match ttl {
            Some(duration) => {
                let _: () = redis::cmd("SETEX")
                    .arg(key)
                    .arg(duration.as_secs())
                    .arg(serialized)
                    .query(&mut *conn)?;
            },
            None => {
                let _: () = redis::cmd("SET")
                    .arg(key)
                    .arg(serialized)
                    .query(&mut *conn)?;
            }
        }
        
        Ok(())
    }
    
    async fn delete(&self, key: &str) -> Result<bool, Box<dyn std::error::Error>> {
        // 获取连接
        let mut conn = self.pool.get()?;
        
        // 删除键
        let count: i64 = redis::cmd("DEL")
            .arg(key)
            .query(&mut *conn)?;
        
        Ok(count > 0)
    }
    
    async fn exists(&self, key: &str) -> Result<bool, Box<dyn std::error::Error>> {
        // 获取连接
        let mut conn = self.pool.get()?;
        
        // 检查键是否存在
        let exists: bool = redis::cmd("EXISTS")
            .arg(key)
            .query(&mut *conn)?;
        
        Ok(exists)
    }
    
    async fn expire(&self, key: &str, ttl: Duration) -> Result<bool, Box<dyn std::error::Error>> {
        // 获取连接
        let mut conn = self.pool.get()?;
        
        // 设置过期时间
        let result: bool = redis::cmd("EXPIRE")
            .arg(key)
            .arg(ttl.as_secs())
            .query(&mut *conn)?;
        
        Ok(result)
    }
    
    async fn increment(&self, key: &str, amount: i64) -> Result<i64, Box<dyn std::error::Error>> {
        // 获取连接
        let mut conn = self.pool.get()?;
        
        // 递增
        let value: i64 = redis::cmd("INCRBY")
            .arg(key)
            .arg(amount)
            .query(&mut *conn)?;
        
        Ok(value)
    }
    
    async fn set_nx<T: Serialize + Send + 'static>(&self, key: &str, value: T, ttl: Option<Duration>) -> Result<bool, Box<dyn std::error::Error>> {
        // 获取连接
        let mut conn = self.pool.get()?;
        
        // 序列化值
        let serialized = serde_json::to_string(&value)?;
        
        // 设置NX
        let result: bool = match ttl {
            Some(duration) => {
                // 使用SET with NX and EX选项
                let result: Option<String> = redis::cmd("SET")
                    .arg(key)
                    .arg(&serialized)
                    .arg("NX")
                    .arg("EX")
                    .arg(duration.as_secs())
                    .query(&mut *conn)
                    .ok();
                
                result.is_some()
            },
            None => {
                // 使用SETNX
                let result: i64 = redis::cmd("SETNX")
                    .arg(key)
                    .arg(&serialized)
                    .query(&mut *conn)?;
                
                result == 1
            }
        };
        
        Ok(result)
    }
}

// 内存缓存实现（用于测试或本地开发）
struct InMemoryCache {
    cache: Arc<tokio::sync::RwLock<HashMap<String, CacheEntry>>>,
}

struct CacheEntry {
    value: String,
    expires_at: Option<std::time::Instant>,
}

impl InMemoryCache {
    fn new() -> Self {
        let cache = Arc::new(tokio::sync::RwLock::new(HashMap::new()));
        
        // 启动清理线程
        let cache_clone = cache.clone();
        tokio::spawn(async move {
            loop {
                tokio::time::sleep(Duration::from_secs(60)).await;
                
                // 清理过期项
                let now = std::time::Instant::now();
                let mut cache = cache_clone.write().await;
                
                cache.retain(|_, entry| {
                    entry.expires_at.map_or(true, |expiry| expiry > now)
                });
            }
        });
        
        Self { cache }
    }
}

#[async_trait]
impl DistributedCache for InMemoryCache {
    async fn get<T: for<'de> Deserialize<'de> + Send + 'static>(&self, key: &str) -> Result<Option<T>, Box<dyn std::error::Error>> {
        let cache = self.cache.read().await;
        
        if let Some(entry) = cache.get(key) {
            // 检查是否过期
            if let Some(expires_at) = entry.expires_at {
                if expires_at <= std::time::Instant::now() {
                    return Ok(None);
                }
            }
            
            // 反序列化
            let deserialized = serde_json::from_str(&entry.value)?;
            Ok(Some(deserialized))
        } else {
            Ok(None)
        }
    }
    
    async fn set<T: Serialize + Send + 'static>(&self, key: &str, value: T, ttl: Option<Duration>) -> Result<(), Box<dyn std::error::Error>> {
        // 序列化值
        let serialized = serde_json::to_string(&value)?;
        
        // 计算过期时间
        let expires_at = ttl.map(|duration| std::time::Instant::now() + duration);
        
        // 存储值
        let mut cache = self.cache.write().await;
        cache.insert(key.to_string(), CacheEntry {
            value: serialized,
            expires_at,
        });
        
        Ok(())
    }
    
    async fn delete(&self, key: &str) -> Result<bool, Box<dyn std::error::Error>> {
        let mut cache = self.cache.write().await;
        let removed = cache.remove(key).is_some();
        Ok(removed)
    }
    
    async fn exists(&self, key: &str) -> Result<bool, Box<dyn std::error::Error>> {
        let cache = self.cache.read().await;
        
        if let Some(entry) = cache.get(key) {
            // 检查是否过期
            if let Some(expires_at) = entry.expires_at {
                if expires_at <= std::time::Instant::now() {
                    return Ok(false);
                }
            }
            
            Ok(true)
        } else {
            Ok(false)
        }
    }
    
    async fn expire(&self, key: &str, ttl: Duration) -> Result<bool, Box<dyn std::error::Error>> {
        let mut cache = self.cache.write().await;
        
        if let Some(entry) = cache.get_mut(key) {
            entry.expires_at = Some(std::time::Instant::now() + ttl);
            Ok(true)
        } else {
            Ok(false)
        }
    }
    
    async fn increment(&self, key: &str, amount: i64) -> Result<i64, Box<dyn std::error::Error>> {
        let mut cache = self.cache.write().await;
        
        let new_value = if let Some(entry) = cache.get(key) {
            // 解析现有值
            let current: i64 = serde_json::from_str(&entry.value).unwrap_or(0);
            let new_value = current + amount;
            
            // 更新值
            let entry = cache.get_mut(key).unwrap();
            entry.value = serde_json::to_string(&new_value)?;
            
            new_value
        } else {
            // 键不存在，创建新值
            let new_value = amount;
            cache.insert(key.to_string(), CacheEntry {
                value: serde_json::to_string(&new_value)?,
                expires_at: None,
            });
            
            new_value
        };
        
        Ok(new_value)
    }
    
    async fn set_nx<T: Serialize + Send + 'static>(&self, key: &str, value: T, ttl: Option<Duration>) -> Result<bool, Box<dyn std::error::Error>> {
        let mut cache = self.cache.write().await;
        
        // 检查键是否已存在且未过期
        if let Some(entry) = cache.get(key) {
            if let Some(expires_at) = entry.expires_at {
                if expires_at <= std::time::Instant::now() {
                    // 已过期，可以设置
                } else {
                    // 未过期，不能设置
                    return Ok(false);
                }
            } else {
                // 永不过期，不能设置
                return Ok(false);
            }
        }
        
        // 序列化值
        let serialized = serde_json::to_string(&value)?;
        
        // 计算过期时间
        let expires_at = ttl.map(|duration| std::time::Instant::now() + duration);
        
        // 存储值
        cache.insert(key.to_string(), CacheEntry {
            value: serialized,
            expires_at,
        });
        
        Ok(true)
    }
}
```

**3. 带缓存的Repository模式**：

```rust
use std::sync::Arc;
use async_trait::async_trait;
use serde::{Serialize, Deserialize};

// 用户实体
#[derive(Clone, Debug, Serialize, Deserialize)]
struct User {
    id: u64,
    username: String,
    email: String,
    created_at: chrono::DateTime<chrono::Utc>,
    last_login: Option<chrono::DateTime<chrono::Utc>>,
}

// 用户仓库接口
#[async_trait]
trait UserRepository {
    async fn find_by_id(&self, id: u64) -> Result<Option<User>, Box<dyn std::error::Error>>;
    async fn find_by_username(&self, username: &str) -> Result<Option<User>, Box<dyn std::error::Error>>;
    async fn save(&self, user: &User) -> Result<(), Box<dyn std::error::Error>>;
    async fn delete(&self, id: u64) -> Result<bool, Box<dyn std::error::Error>>;
}

// 数据库实现
struct DbUserRepository {
    pool: Arc<sqlx::PgPool>,
}

#[async_trait]
impl UserRepository for DbUserRepository {
    async fn find_by_id(&self, id: u64) -> Result<Option<User>, Box<dyn std::error::Error>> {
        let user = sqlx::query_as!(
            User,
            r#"
            SELECT id, username, email, created_at, last_login
            FROM users
            WHERE id = $1
            "#,
            id as i64
        )
        .fetch_optional(&*self.pool)
        .await?;
        
        Ok(user)
    }
    
    async fn find_by_username(&self, username: &str) -> Result<Option<User>, Box<dyn std::error::Error>> {
        let user = sqlx::query_as!(
            User,
            r#"
            SELECT id, username, email, created_at, last_login
            FROM users
            WHERE username = $1
            "#,
            username
        )
        .fetch_optional(&*self.pool)
        .await?;
        
        Ok(user)
    }
    
    async fn save(&self, user: &User) -> Result<(), Box<dyn std::error::Error>> {
        sqlx::query!(
            r#"
            INSERT INTO users (id, username, email, created_at, last_login)
            VALUES ($1, $2, $3, $4, $5)
            ON CONFLICT (id) DO UPDATE
            SET username = $2, email = $3, last_login = $5
            "#,
            user.id as i64,
            user.username,
            user.email,
            user.created_at,
            user.last_login
        )
        .execute(&*self.pool)
        .await?;
        
        Ok(())
    }
    
    async fn delete(&self, id: u64) -> Result<bool, Box<dyn std::error::Error>> {
        let result = sqlx::query!(
            r#"
            DELETE FROM users
            WHERE id = $1
            "#,
            id as i64
        )
        .execute(&*self.pool)
        .await?;
        
        Ok(result.rows_affected() > 0)
    }
}

// 带缓存的用户仓库
struct CachedUserRepository {
    db_repo: Arc<dyn UserRepository + Send + Sync>,
    cache: Arc<dyn DistributedCache + Send + Sync>,
    cache_ttl: Duration,
}

impl CachedUserRepository {
    fn new(
        db_repo: Arc<dyn UserRepository + Send + Sync>,
        cache: Arc<dyn DistributedCache + Send + Sync>,
        cache_ttl: Duration,
    ) -> Self {
        Self {
            db_repo,
            cache,
            cache_ttl,
        }
    }
    
    // 构建缓存键
    fn cache_key_by_id(&self, id: u64) -> String {
        format!("user:id:{}", id)
    }
    
    fn cache_key_by_username(&self, username: &str) -> String {
        format!("user:username:{}", username)
    }
}

#[async_trait]
impl UserRepository for CachedUserRepository {
    async fn find_by_id(&self, id: u64) -> Result<Option<User>, Box<dyn std::error::Error>> {
        let cache_key = self.cache_key_by_id(id);
        
        // 尝试从缓存获取
        if let Ok(Some(user)) = self.cache.get::<User>(&cache_key).await {
            return Ok(Some(user));
        }
        
        // 从数据库获取
        let user_result = self.db_repo.find_by_id(id).await?;
        
        // 如果找到用户，更新缓存
        if let Some(user) = &user_result {
            // 缓存用户ID索引
            let _ = self.cache.set(&cache_key, user, Some(self.cache_ttl)).await;
            
            // 同时缓存用户名索引
            let username_key = self.cache_key_by_username(&user.username);
            let _ = self.cache.set(&username_key, user, Some(self.cache_ttl)).await;
        }
        
        Ok(user_result)
    }
    
    async fn find_by_username(&self, username: &str) -> Result<Option<User>, Box<dyn std::error::Error>> {
        let cache_key = self.cache_key_by_username(username);
        
        // 尝试从缓存获取
        if let Ok(Some(user)) = self.cache.get::<User>(&cache_key).await {
            return Ok(Some(user));
        }
        
        // 从数据库获取
        let user_result = self.db_repo.find_by_username(username).await?;
        
        // 如果找到用户，更新缓存
        if let Some(user) = &user_result {
            // 缓存用户名索引
            let _ = self.cache.set(&cache_key, user, Some(self.cache_ttl)).await;
            
            // 同时缓存用户ID索引
            let id_key = self.cache_key_by_id(user.id);
            let _ = self.cache.set(&id_key, user, Some(self.cache_ttl)).await;
        }
        
        Ok(user_result)
    }
    
    async fn save(&self, user: &User) -> Result<(), Box<dyn std::error::Error>> {
        // 保存到数据库
        self.db_repo.save(user).await?;
        
        // 更新缓存
        let id_key = self.cache_key_by_id(user.id);
        let username_key = self.cache_key_by_username(&user.username);
        
        // 使用管道更新多个缓存键
        let _ = self.cache.set(&id_key, user, Some(self.cache_ttl)).await;
        let _ = self.cache.set(&username_key, user, Some(self.cache_ttl)).await;
        
        Ok(())
    }
    
    async fn delete(&self, id: u64) -> Result<bool, Box<dyn std::error::Error>> {
        // 先获取用户信息（用于清除用户名缓存）
        let user = self.find_by_id(id).await?;
        
        // 从数据库删除
        let result = self.db_repo.delete(id).await?;
        
        if result {
            // 清除ID缓存
            let id_key = self.cache_key_by_id(id);
            let _ = self.cache.delete(&id_key).await;
            
            // 如果能获取到用户，也清除用户名缓存
            if let Some(user) = user {
                let username_key = self.cache_key_by_username(&user.username);
                let _ = self.cache.delete(&username_key).await;
            }
        }
        
        Ok(result)
    }
}

// 使用示例
async fn repository_example() -> Result<(), Box<dyn std::error::Error>> {
    // 创建数据库连接池
    let pool = Arc::new(
        sqlx::postgres::PgPoolOptions::new()
            .max_connections(5)
            .connect("postgres://postgres:password@localhost/mydb")
            .await?
    );
    
    // 创建数据库仓库
    let db_repo = Arc::new(DbUserRepository { pool });
    
    // 创建缓存
    let cache = Arc::new(RedisCache::new("redis://localhost")?);
    
    // 创建带缓存的仓库
    let user_repo = CachedUserRepository::new(
        db_repo,
        cache,
        Duration::from_secs(3600)  // 1小时缓存
    );
    
    // 使用仓库
    let user = User {
        id: 1,
        username: "zhang_san".to_string(),
        email: "zhangsan@example.com".to_string(),
        created_at: chrono::Utc::now(),
        last_login: Some(chrono::Utc::now()),
    };
    
    // 保存用户
    user_repo.save(&user).await?;
    
    // 查找用户（应该从缓存获取）
    let found_user = user_repo.find_by_id(1).await?;
    println!("找到用户: {:?}", found_user);
    
    // 删除用户
    user_repo.delete(1).await?;
    
    Ok(())
}
```

**4. 分布式锁实现**：

```rust
use async_trait::async_trait;
use std::time::Duration;
use std::sync::Arc;
use uuid::Uuid;

// 分布式锁接口
#[async_trait]
trait DistributedLock {
    // 尝试获取锁
    async fn try_lock(&self, key: &str, ttl: Duration) -> Result<Option<LockGuard>, Box<dyn std::error::Error>>;
    
    // 阻塞直到获取锁
    async fn lock(&self, key: &str, ttl: Duration, retry_interval: Duration, max_retries: Option<u32>) -> Result<Option<LockGuard>, Box<dyn std::error::Error>>;
    
    // 释放锁
    async fn unlock(&self, guard: LockGuard) -> Result<bool, Box<dyn std::error::Error>>;
}

// 锁保护器
#[derive(Debug, Clone)]
struct LockGuard {
    key: String,
    value: String,
    ttl: Duration,
}

// Redis实现的分布式锁
struct RedisLock {
    client: Arc<redis::Client>,
    pool: Arc<r2d2::Pool<redis::Client>>,
}

impl RedisLock {
    fn new(uri: &str) -> Result<Self, Box<dyn std::error::Error>> {
        // 创建客户端
        let client = redis::Client::open(uri)?;
        
        // 创建连接池
        let pool = r2d2::Pool::builder()
            .max_size(15)
            .build(client.clone())?;
        
        Ok(Self {
            client: Arc::new(client),
            pool: Arc::new(pool),
        })
    }
}

#[async_trait]
impl DistributedLock for RedisLock {
    async fn try_lock(&self, key: &str, ttl: Duration) -> Result<Option<LockGuard>, Box<dyn std::error::Error>> {
        // 创建锁值（唯一标识符）
        let value = Uuid::new_v4().to_string();
        
        // 格式化锁键
        let lock_key = format!("lock:{}", key);
        
        // 获取连接
        let mut conn = self.pool.get()?;
        
        // 尝试获取锁（使用SET NX EX）
        let result: Option<String> = redis::cmd("SET")
            .arg(&lock_key)
            .arg(&value)
            .arg("NX")
            .arg("EX")
            .arg(ttl.as_secs())
            .query(&mut *conn)
            .ok();
        
        if result.is_some() {
            // 成功获取锁
            Ok(Some(LockGuard {
                key: lock_key,
                value,
                ttl,
            }))
        } else {
            // 获取锁失败
            Ok(None)
        }
    }
    
    async fn lock(&self, key: &str, ttl: Duration, retry_interval: Duration, max_retries: Option<u32>) -> Result<Option<LockGuard>, Box<dyn std::error::Error>> {
        let mut retries = 0;
        
        loop {
            // 尝试获取锁
            if let Some(guard) = self.try_lock(key, ttl).await? {
                return Ok(Some(guard));
            }
            
            // 检查重试次数
            if let Some(max) = max_retries {
                retries += 1;
                if retries >= max {
                    return Ok(None);
                }
            }
            
            // 等待后重试
            tokio::time::sleep(retry_interval).await;
        }
    }
    
    async fn unlock(&self, guard: LockGuard) -> Result<bool, Box<dyn std::error::Error>> {
        // 获取连接
        let mut conn = self.pool.get()?;
        
        // 使用Lua脚本安全释放锁
        // 只有当锁的值匹配时才释放，防止释放别人的锁
        let script = r#"
            if redis.call("GET", KEYS[1]) == ARGV[1] then
                return redis.call("DEL", KEYS[1])
            else
                return 0
            end
        "#;
        
        // 执行脚本
        let result: i64 = redis::cmd("EVAL")
            .arg(script)
            .arg(1)  // 一个键
            .arg(&guard.key)
            .arg(&guard.value)
            .query(&mut *conn)?;
        
        Ok(result == 1)
    }
}

// 自动释放的锁包装器
struct AutoLock {
    lock: Arc<dyn DistributedLock + Send + Sync>,
    guard: Option<LockGuard>,
}

impl AutoLock {
    async fn new(
        lock: Arc<dyn DistributedLock + Send + Sync>,
        key: &str,
        ttl: Duration,
        retry_interval: Duration,
        max_retries: Option<u32>,
    ) -> Result<Option<Self>, Box<dyn std::error::Error>> {
        // 尝试获取锁
        let guard = lock.lock(key, ttl, retry_interval, max_retries).await?;
        
        Ok(guard.map(|g| Self {
            lock: lock.clone(),
            guard: Some(g),
        }))
    }
}

impl Drop for AutoLock {
    fn drop(&mut self) {
        // 获取guard并设置为None，避免多次释放
        if let Some(guard) = self.guard.take() {
            // 创建运行时以异步释放锁
            let lock = self.lock.clone();
            let rt = tokio::runtime::Runtime::new().unwrap();
            rt.block_on(async {
                if let Err(e) = lock.unlock(guard).await {
                    eprintln!("释放锁失败: {}", e);
                }
            });
        }
    }
}

// 使用示例
async fn distributed_lock_example() -> Result<(), Box<dyn std::error::Error>> {
    // 创建分布式锁
    let lock = Arc::new(RedisLock::new("redis://localhost")?);
    
    // 自动获取和释放锁
    if let Some(auto_lock) = AutoLock::new(
        lock.clone(),
        "my-resource",
        Duration::from_secs(30),
        Duration::from_millis(100),
        Some(10),
    ).await? {
        // 锁获取成功，执行受保护的操作
        println!("锁获取成功，执行关键操作");
        
        // 锁会在离开作用域时自动释放
    } else {
        println!("无法获取锁");
    }
    
    // 手动获取和释放锁
    if let Some(guard) = lock.try_lock("another-resource", Duration::from_secs(10)).await? {
        println!("锁获取成功，执行关键操作");
        
        // 手动释放锁
        if lock.unlock(guard).await? {
            println!("锁释放成功");
        } else {
            println!("锁释放失败");
        } else {
            println!("无法获取锁");
        }

    Ok(())
    }
}

```

**5. Redlock算法实现**:

```rust
// Redis分布式锁的Redlock实现（更强一致性）
struct RedlockClient {
    lock_clients: Vec<Arc<RedisLock>>,
    quorum: usize,
}

impl RedlockClient {
    fn new(redis_uris: Vec<String>) -> Result<Self, Box<dyn std::error::Error>> {
        let mut lock_clients = Vec::with_capacity(redis_uris.len());
        
        for uri in redis_uris {
            let lock = Arc::new(RedisLock::new(&uri)?);
            lock_clients.push(lock);
        }
        
        // 计算仲裁数（N/2+1）
        let quorum = lock_clients.len() / 2 + 1;
        
        Ok(Self {
            lock_clients,
            quorum,
        })
    }
    
    async fn try_lock(&self, key: &str, ttl: Duration) -> Result<Option<RedlockGuard>, Box<dyn std::error::Error>> {
        // 创建一个唯一的锁值
        let value = Uuid::new_v4().to_string();
        
        // 记录成功获取锁的实例和对应的锁保护器
        let mut acquired_locks = Vec::new();
        
        // 记录开始时间
        let start_time = std::time::Instant::now();
        
        // 尝试从所有Redis实例获取锁
        for lock_client in &self.lock_clients {
            match lock_client.try_lock(key, ttl).await {
                Ok(Some(guard)) => {
                    acquired_locks.push((lock_client.clone(), guard));
                }
                _ => {
                    // 这个实例获取锁失败，继续尝试其他实例
                }
            }
        }
        
        // 计算获取锁消耗的时间
        let elapsed = start_time.elapsed();
        
        // 检查是否达到仲裁数
        let valid_lock = if acquired_locks.len() >= self.quorum {
            // 计算剩余的有效锁时间
            let valid_time = ttl.checked_sub(elapsed).unwrap_or(Duration::from_secs(0));
            
            // 如果剩余时间大于0，则锁有效
            valid_time > Duration::from_secs(0)
        } else {
            false
        };
        
        if valid_lock {
            // 成功获取锁
            Ok(Some(RedlockGuard {
                key: key.to_string(),
                value,
                ttl,
                locks: acquired_locks,
            }))
        } else {
            // 获取锁失败，释放所有已获取的锁
            for (lock_client, guard) in acquired_locks {
                let _ = lock_client.unlock(guard).await;
            }
            
            Ok(None)
        }
    }
    
    async fn unlock(&self, guard: RedlockGuard) -> Result<bool, Box<dyn std::error::Error>> {
        let mut success_count = 0;
        
        // 在所有实例上释放锁
        for (lock_client, lock_guard) in guard.locks {
            if lock_client.unlock(lock_guard).await? {
                success_count += 1;
            }
        }
        
        // 如果大多数实例成功释放锁，则认为释放成功
        Ok(success_count >= self.quorum)
    }
}

struct RedlockGuard {
    key: String,
    value: String,
    ttl: Duration,
    locks: Vec<(Arc<RedisLock>, LockGuard)>,
}

// 使用Redlock示例
async fn redlock_example() -> Result<(), Box<dyn std::error::Error>> {
    // 创建连接到多个Redis实例的Redlock客户端
    let redlock = RedlockClient::new(vec![
        "redis://redis1:6379".to_string(),
        "redis://redis2:6379".to_string(),
        "redis://redis3:6379".to_string(),
        "redis://redis4:6379".to_string(),
        "redis://redis5:6379".to_string(),
    ])?;
    
    // 尝试获取锁
    if let Some(guard) = redlock.try_lock("critical-resource", Duration::from_secs(10)).await? {
        println!("成功通过Redlock获取锁");
        
        // 执行关键操作
        tokio::time::sleep(Duration::from_secs(2)).await;
        
        // 释放锁
        if redlock.unlock(guard).await? {
            println!("成功释放Redlock锁");
        } else {
            println!("释放Redlock锁失败");
        }
    } else {
        println!("无法获取Redlock锁");
    }
    
    Ok(())
}
```

### 4.6 服务发现与注册

在分布式系统中，服务发现和注册是构建可靠系统的核心机制。

**1. 服务注册与发现接口**：

```rust
use async_trait::async_trait;
use serde::{Serialize, Deserialize};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};

// 服务实例信息
#[derive(Clone, Debug, Serialize, Deserialize)]
struct ServiceInstance {
    id: String,
    service_name: String,
    host: String,
    port: u16,
    secure: bool,
    metadata: HashMap<String, String>,
    health_check_url: Option<String>,
    status: ServiceStatus,
    last_updated: chrono::DateTime<chrono::Utc>,
}

// 服务状态
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
enum ServiceStatus {
    UP,
    DOWN,
    STARTING,
    OUT_OF_SERVICE,
    UNKNOWN,
}

// 服务发现接口
#[async_trait]
trait ServiceDiscovery {
    // 注册服务实例
    async fn register(&self, instance: ServiceInstance) -> Result<(), Box<dyn std::error::Error>>;
    
    // 注销服务实例
    async fn deregister(&self, service_name: &str, instance_id: &str) -> Result<(), Box<dyn std::error::Error>>;
    
    // 查找服务实例
    async fn get_instances(&self, service_name: &str) -> Result<Vec<ServiceInstance>, Box<dyn std::error::Error>>;
    
    // 查找所有服务
    async fn get_services(&self) -> Result<Vec<String>, Box<dyn std::error::Error>>;
    
    // 监听服务变化
    async fn watch_service(&self, service_name: &str, callback: Arc<dyn Fn(Vec<ServiceInstance>) + Send + Sync>) -> Result<(), Box<dyn std::error::Error>>;
}

// 服务健康状态
#[async_trait]
trait HealthChecker {
    // 检查服务实例是否健康
    async fn check_health(&self, instance: &ServiceInstance) -> Result<bool, Box<dyn std::error::Error>>;
}

// HTTP健康检查实现
struct HttpHealthChecker {
    client: reqwest::Client,
    timeout: Duration,
}

impl HttpHealthChecker {
    fn new(timeout: Duration) -> Self {
        Self {
            client: reqwest::Client::builder()
                .timeout(timeout)
                .build()
                .unwrap(),
            timeout,
        }
    }
}

#[async_trait]
impl HealthChecker for HttpHealthChecker {
    async fn check_health(&self, instance: &ServiceInstance) -> Result<bool, Box<dyn std::error::Error>> {
        // 检查是否有指定的健康检查URL
        if let Some(url) = &instance.health_check_url {
            // 发送请求
            let response = self.client.get(url).send().await?;
            
            // 检查状态码
            return Ok(response.status().is_success());
        }
        
        // 如果没有健康检查URL，构造默认URL
        let schema = if instance.secure { "https" } else { "http" };
        let url = format!("{}://{}:{}/health", schema, instance.host, instance.port);
        
        // 发送请求
        match self.client.get(&url).send().await {
            Ok(response) => Ok(response.status().is_success()),
            Err(_) => Ok(false),
        }
    }
}

// 内存实现的服务发现（用于单机测试）
struct InMemoryServiceDiscovery {
    services: Arc<tokio::sync::RwLock<HashMap<String, HashMap<String, ServiceInstance>>>>,
    watchers: Arc<tokio::sync::RwLock<HashMap<String, Vec<Arc<dyn Fn(Vec<ServiceInstance>) + Send + Sync>>>>>,
    health_checker: Arc<dyn HealthChecker + Send + Sync>,
}

impl InMemoryServiceDiscovery {
    fn new(health_checker: Arc<dyn HealthChecker + Send + Sync>) -> Self {
        let discovery = Self {
            services: Arc::new(tokio::sync::RwLock::new(HashMap::new())),
            watchers: Arc::new(tokio::sync::RwLock::new(HashMap::new())),
            health_checker,
        };
        
        // 启动健康检查线程
        Self::start_health_check_task(
            discovery.services.clone(),
            discovery.watchers.clone(),
            health_checker.clone(),
        );
        
        discovery
    }
    
    fn start_health_check_task(
        services: Arc<tokio::sync::RwLock<HashMap<String, HashMap<String, ServiceInstance>>>>,
        watchers: Arc<tokio::sync::RwLock<HashMap<String, Vec<Arc<dyn Fn(Vec<ServiceInstance>) + Send + Sync>>>>>,
        health_checker: Arc<dyn HealthChecker + Send + Sync>,
    ) {
        tokio::spawn(async move {
            let check_interval = Duration::from_secs(10);
            let mut changed_services = HashSet::new();
            
            loop {
                tokio::time::sleep(check_interval).await;
                changed_services.clear();
                
                // 检查所有服务实例的健康状态
                let mut services_lock = services.write().await;
                
                for (service_name, instances) in services_lock.iter_mut() {
                    for (_, instance) in instances.iter_mut() {
                        let old_status = instance.status;
                        
                        // 检查健康状态
                        match health_checker.check_health(instance).await {
                            Ok(true) => {
                                instance.status = ServiceStatus::UP;
                            },
                            _ => {
                                instance.status = ServiceStatus::DOWN;
                            }
                        }
                        
                        // 如果状态变化了，记录服务名
                        if old_status != instance.status {
                            changed_services.insert(service_name.clone());
                            instance.last_updated = chrono::Utc::now();
                        }
                    }
                }
                
                // 释放锁
                drop(services_lock);
                
                // 通知监听者
                if !changed_services.is_empty() {
                    let watchers_lock = watchers.read().await;
                    
                    for service_name in &changed_services {
                        if let Some(callbacks) = watchers_lock.get(service_name) {
                            // 获取服务实例列表
                            let services_lock = services.read().await;
                            
                            if let Some(instances) = services_lock.get(service_name) {
                                let instances_vec: Vec<ServiceInstance> = instances.values().cloned().collect();
                                
                                // 通知所有监听者
                                for callback in callbacks {
                                    callback(instances_vec.clone());
                                }
                            }
                        }
                    }
                }
            }
        });
    }
}

#[async_trait]
impl ServiceDiscovery for InMemoryServiceDiscovery {
    async fn register(&self, mut instance: ServiceInstance) -> Result<(), Box<dyn std::error::Error>> {
        // 设置当前时间
        instance.last_updated = chrono::Utc::now();
        
        // 检查初始健康状态
        match self.health_checker.check_health(&instance).await {
            Ok(true) => {
                instance.status = ServiceStatus::UP;
            },
            _ => {
                instance.status = ServiceStatus::STARTING;
            }
        }
        
        // 注册服务
        let mut services = self.services.write().await;
        
        // 获取服务实例map，如果不存在则创建
        let instances = services
            .entry(instance.service_name.clone())
            .or_insert_with(HashMap::new);
        
        // 添加实例
        instances.insert(instance.id.clone(), instance.clone());
        
        // 释放锁
        drop(services);
        
        // 通知监听者
        let watchers = self.watchers.read().await;
        
        if let Some(callbacks) = watchers.get(&instance.service_name) {
            // 重新获取服务实例列表
            let services = self.services.read().await;
            
            if let Some(instances) = services.get(&instance.service_name) {
                let instances_vec: Vec<ServiceInstance> = instances.values().cloned().collect();
                
                // 通知所有监听者
                for callback in callbacks {
                    callback(instances_vec.clone());
                }
            }
        }
        
        Ok(())
    }
    
    async fn deregister(&self, service_name: &str, instance_id: &str) -> Result<(), Box<dyn std::error::Error>> {
        // 注销服务
        let mut services = self.services.write().await;
        
        if let Some(instances) = services.get_mut(service_name) {
            instances.remove(instance_id);
            
            // 如果服务没有实例了，删除服务
            if instances.is_empty() {
                services.remove(service_name);
            }
        }
        
        // 释放锁
        drop(services);
        
        // 通知监听者
        let watchers = self.watchers.read().await;
        
        if let Some(callbacks) = watchers.get(service_name) {
            // 重新获取服务实例列表
            let services = self.services.read().await;
            
            let instances_vec = if let Some(instances) = services.get(service_name) {
                instances.values().cloned().collect()
            } else {
                Vec::new()
            };
            
            // 通知所有监听者
            for callback in callbacks {
                callback(instances_vec.clone());
            }
        }
        
        Ok(())
    }
    
    async fn get_instances(&self, service_name: &str) -> Result<Vec<ServiceInstance>, Box<dyn std::error::Error>> {
        let services = self.services.read().await;
        
        let instances = if let Some(instances) = services.get(service_name) {
            instances.values().cloned().collect()
        } else {
            Vec::new()
        };
        
        Ok(instances)
    }
    
    async fn get_services(&self) -> Result<Vec<String>, Box<dyn std::error::Error>> {
        let services = self.services.read().await;
        let service_names: Vec<String> = services.keys().cloned().collect();
        
        Ok(service_names)
    }
    
    async fn watch_service(&self, service_name: &str, callback: Arc<dyn Fn(Vec<ServiceInstance>) + Send + Sync>) -> Result<(), Box<dyn std::error::Error>> {
        // 注册监听者
        let mut watchers = self.watchers.write().await;
        
        let callbacks = watchers
            .entry(service_name.to_string())
            .or_insert_with(Vec::new);
        
        callbacks.push(callback.clone());
        
        // 释放锁
        drop(watchers);
        
        // 立即通知当前状态
        let services = self.services.read().await;
        
        let instances = if let Some(instances) = services.get(service_name) {
            instances.values().cloned().collect()
        } else {
            Vec::new()
        };
        
        // 调用回调
        callback(instances);
        
        Ok(())
    }
}

// Consul服务发现实现
struct ConsulServiceDiscovery {
    client: reqwest::Client,
    consul_url: String,
    health_checker: Arc<dyn HealthChecker + Send + Sync>,
    watchers: Arc<tokio::sync::RwLock<HashMap<String, Vec<Arc<dyn Fn(Vec<ServiceInstance>) + Send + Sync>>>>>,
    local_cache: Arc<tokio::sync::RwLock<HashMap<String, Vec<ServiceInstance>>>>,
    service_catalog_index: Arc<tokio::sync::RwLock<String>>,
}

impl ConsulServiceDiscovery {
    fn new(consul_url: &str, health_checker: Arc<dyn HealthChecker + Send + Sync>) -> Self {
        let client = reqwest::Client::new();
        
        let discovery = Self {
            client,
            consul_url: consul_url.to_string(),
            health_checker,
            watchers: Arc::new(tokio::sync::RwLock::new(HashMap::new())),
            local_cache: Arc::new(tokio::sync::RwLock::new(HashMap::new())),
            service_catalog_index: Arc::new(tokio::sync::RwLock::new("0".to_string())),
        };
        
        // 启动监视任务
        Self::start_watch_task(
            discovery.client.clone(),
            discovery.consul_url.clone(),
            discovery.watchers.clone(),
            discovery.local_cache.clone(),
            discovery.service_catalog_index.clone(),
        );
        
        discovery
    }
    
    fn start_watch_task(
        client: reqwest::Client,
        consul_url: String,
        watchers: Arc<tokio::sync::RwLock<HashMap<String, Vec<Arc<dyn Fn(Vec<ServiceInstance>) + Send + Sync>>>>>,
        local_cache: Arc<tokio::sync::RwLock<HashMap<String, Vec<ServiceInstance>>>>,
        service_catalog_index: Arc<tokio::sync::RwLock<String>>,
    ) {
        tokio::spawn(async move {
            loop {
                // 获取索引
                let index = {
                    let index = service_catalog_index.read().await;
                    index.clone()
                };
                
                // 使用长轮询获取服务目录变化
                let url = format!("{}/v1/catalog/services", consul_url);
                let response = match client.get(&url)
                    .header("X-Consul-Index", &index)
                    .query(&[("wait", "30s")])
                    .send()
                    .await
                {
                    Ok(resp) => resp,
                    Err(e) => {
                        eprintln!("Consul服务监视错误: {}", e);
                        tokio::time::sleep(Duration::from_secs(5)).await;
                        continue;
                    }
                };
                
                // 获取新索引
                let new_index = response.headers()
                    .get("X-Consul-Index")
                    .and_then(|v| v.to_str().ok())
                    .unwrap_or("0")
                    .to_string();
                
                // 检查索引是否变化
                if new_index == index {
                    continue;
                }
                
                // 更新索引
                {
                    let mut idx = service_catalog_index.write().await;
                    *idx = new_index;
                }
                
                // 解析服务列表
                let services: HashMap<String, Vec<String>> = match response.json().await {
                    Ok(s) => s,
                    Err(e) => {
                        eprintln!("解析Consul服务列表错误: {}", e);
                        continue;
                    }
                };
                
                // 获取所有服务的实例
                let mut changed_services = HashSet::new();
                let mut updated_cache = HashMap::new();
                
                for service_name in services.keys() {
                    // 获取服务实例
                    let instances = Self::fetch_service_instances(&client, &consul_url, service_name).await;
                    
                    if let Ok(instances) = instances {
                        // 检查是否有变化
                        let cache = local_cache.read().await;
                        let cache_instances = cache.get(service_name);
                        
                        let has_changes = match cache_instances {
                            Some(cached) => {
                                if cached.len() != instances.len() {
                                    true
                                } else {
                                    // 比较实例
                                    let mut instance_ids: HashSet<&str> = HashSet::new();
                                    let mut instance_map: HashMap<&str, &ServiceInstance> = HashMap::new();
                                    
                                    for instance in cached {
                                        instance_ids.insert(&instance.id);
                                        instance_map.insert(&instance.id, instance);
                                    }
                                    
                                    for instance in &instances {
                                        if !instance_ids.contains(instance.id.as_str()) {
                                            // 新增实例
                                            true
                                        } else {
                                            // 检查实例是否变化
                                            let cached_instance = instance_map.get(instance.id.as_str()).unwrap();
                                            if instance.status != cached_instance.status {
                                                true
                                            } else {
                                                false
                                            }
                                        }
                                    }
                                    
                                    false // 如果上面没有返回true，则没有变化
                                }
                            },
                            None => true, // 新增服务
                        };
                        
                        if has_changes {
                            changed_services.insert(service_name.clone());
                        }
                        
                        updated_cache.insert(service_name.clone(), instances);
                    }
                }
                
                // 更新缓存
                {
                    let mut cache = local_cache.write().await;
                    *cache = updated_cache;
                }
                
                // 通知监听者
                if !changed_services.is_empty() {
                    let watchers_lock = watchers.read().await;
                    let cache = local_cache.read().await;
                    
                    for service_name in changed_services {
                        if let Some(callbacks) = watchers_lock.get(&service_name) {
                            if let Some(instances) = cache.get(&service_name) {
                                // 通知所有监听者
                                for callback in callbacks {
                                    callback(instances.clone());
                                }
                            }
                        }
                    }
                }
            }
        });
    }
    
    async fn fetch_service_instances(
        client: &reqwest::Client,
        consul_url: &str,
        service_name: &str,
    ) -> Result<Vec<ServiceInstance>, Box<dyn std::error::Error>> {
        // 构造URL
        let url = format!("{}/v1/health/service/{}", consul_url, service_name);
        
        // 发送请求
        let response = client.get(&url)
            .query(&[("passing", "true")])
            .send()
            .await?;
        
        // 解析响应
        let services: Vec<ConsulService> = response.json().await?;
        
        // 转换为ServiceInstance
        let instances = services.into_iter()
            .map(|s| {
                let status = if s.Checks.iter().all(|c| c.Status == "passing") {
                    ServiceStatus::UP
                } else {
                    ServiceStatus::DOWN
                };
                
                ServiceInstance {
                    id: s.Service.ID,
                    service_name: s.Service.Service,
                    host: s.Service.Address,
                    port: s.Service.Port,
                    secure: s.Service.Meta.get("secure").map_or(false, |v| v == "true"),
                    metadata: s.Service.Meta,
                    health_check_url: None,
                    status,
                    last_updated: chrono::Utc::now(),
                }
            })
            .collect();
        
        Ok(instances)
    }
}

#[derive(Deserialize)]
struct ConsulService {
    Service: ConsulServiceDetail,
    Checks: Vec<ConsulCheck>,
}

#[derive(Deserialize)]
struct ConsulServiceDetail {
    ID: String,
    Service: String,
    Address: String,
    Port: u16,
    Meta: HashMap<String, String>,
}

#[derive(Deserialize)]
struct ConsulCheck {
    Status: String,
}

#[async_trait]
impl ServiceDiscovery for ConsulServiceDiscovery {
    async fn register(&self, instance: ServiceInstance) -> Result<(), Box<dyn std::error::Error>> {
        // 构造Consul服务定义
        let service_def = ConsulRegisterRequest {
            ID: instance.id.clone(),
            Name: instance.service_name.clone(),
            Address: instance.host.clone(),
            Port: instance.port,
            Meta: instance.metadata.clone(),
            Check: ConsulCheck {
                HTTP: instance.health_check_url.clone(),
                Interval: "10s".to_string(),
                Timeout: "5s".to_string(),
            },
        };
        
        // 发送注册请求
        let url = format!("{}/v1/agent/service/register", self.consul_url);
        self.client.put(&url)
            .json(&service_def)
            .send()
            .await?
            .error_for_status()?;
        
        Ok(())
    }
    
    async fn deregister(&self, _service_name: &str, instance_id: &str) -> Result<(), Box<dyn std::error::Error>> {
        // 发送注销请求
        let url = format!("{}/v1/agent/service/deregister/{}", self.consul_url, instance_id);
        self.client.put(&url)
            .send()
            .await?
            .error_for_status()?;
        
        Ok(())
    }
    
    async fn get_instances(&self, service_name: &str) -> Result<Vec<ServiceInstance>, Box<dyn std::error::Error>> {
        // 首先检查缓存
        let cache = self.local_cache.read().await;
        
        if let Some(instances) = cache.get(service_name) {
            return Ok(instances.clone());
        }
        
        // 如果缓存中没有，直接从Consul获取
        Self::fetch_service_instances(&self.client, &self.consul_url, service_name).await
    }
    
    async fn get_services(&self) -> Result<Vec<String>, Box<dyn std::error::Error>> {
        // 构造URL
        let url = format!("{}/v1/catalog/services", self.consul_url);
        
        // 发送请求
        let response = self.client.get(&url)
            .send()
            .await?;
        
        // 解析响应
        let services: HashMap<String, Vec<String>> = response.json().await?;
        
        Ok(services.keys().cloned().collect())
    }
    
    async fn watch_service(&self, service_name: &str, callback: Arc<dyn Fn(Vec<ServiceInstance>) + Send + Sync>) -> Result<(), Box<dyn std::error::Error>> {
        // 注册监听者
        let mut watchers = self.watchers.write().await;
        
        let callbacks = watchers
            .entry(service_name.to_string())
            .or_insert_with(Vec::new);
        
        callbacks.push(callback.clone());
        
        // 释放锁
        drop(watchers);
        
        // 立即通知当前状态
        let instances = self.get_instances(service_name).await?;
        callback(instances);
        
        Ok(())
    }
}

#[derive(Serialize)]
struct ConsulRegisterRequest {
    ID: String,
    Name: String,
    Address: String,
    Port: u16,
    Meta: HashMap<String, String>,
    Check: ConsulCheck,
}

#[derive(Serialize)]
struct ConsulCheckDef {
    HTTP: Option<String>,
    Interval: String,
    Timeout: String,
}
```

**2. 服务客户端与负载均衡**：

```rust
use std::sync::Arc;
use std::fmt::Debug;
use rand::{thread_rng, Rng};
use async_trait::async_trait;

// 负载均衡策略
#[async_trait]
trait LoadBalancer<T: Clone + Debug + Send + Sync> {
    // 选择服务实例
    async fn choose(&self) -> Option<T>;
    
    // 更新可用实例
    async fn update_instances(&self, instances: Vec<T>);
}

// 随机负载均衡
struct RandomLoadBalancer<T: Clone + Debug + Send + Sync> {
    instances: Arc<tokio::sync::RwLock<Vec<T>>>,
}

impl<T: Clone + Debug + Send + Sync> RandomLoadBalancer<T> {
    fn new() -> Self {
        Self {
            instances: Arc::new(tokio::sync::RwLock::new(Vec::new())),
        }
    }
}

#[async_trait]
impl<T: Clone + Debug + Send + Sync> LoadBalancer<T> for RandomLoadBalancer<T> {
    async fn choose(&self) -> Option<T> {
        let instances = self.instances.read().await;
        
        if instances.is_empty() {
            return None;
        }
        
        let idx = thread_rng().gen_range(0..instances.len());
        Some(instances[idx].clone())
    }
    
    async fn update_instances(&self, instances: Vec<T>) {
        let mut instances_lock = self.instances.write().await;
        *instances_lock = instances;
    }
}

// 轮询负载均衡
struct RoundRobinLoadBalancer<T: Clone + Debug + Send + Sync> {
    instances: Arc<tokio::sync::RwLock<Vec<T>>>,
    next_index: Arc<std::sync::atomic::AtomicUsize>,
}

impl<T: Clone + Debug + Send + Sync> RoundRobinLoadBalancer<T> {
    fn new() -> Self {
        Self {
            instances: Arc::new(tokio::sync::RwLock::new(Vec::new())),
            next_index: Arc::new(std::sync::atomic::AtomicUsize::new(0)),
        }
    }
}

#[async_trait]
impl<T: Clone + Debug + Send + Sync> LoadBalancer<T> for RoundRobinLoadBalancer<T> {
    async fn choose(&self) -> Option<T> {
        let instances = self.instances.read().await;
        
        if instances.is_empty() {
            return None;
        }
        
        let idx = self.next_index.fetch_add(1, std::sync::atomic::Ordering::SeqCst) % instances.len();
        Some(instances[idx].clone())
    }
    
    async fn update_instances(&self, instances: Vec<T>) {
        let mut instances_lock = self.instances.write().await;
        *instances_lock = instances;
    }
}

// 权重负载均衡
struct WeightedLoadBalancer<T: Clone + Debug + Send + Sync> {
    instances: Arc<tokio::sync::RwLock<Vec<(T, u32)>>>, // (实例, 权重)
}

impl<T: Clone + Debug + Send + Sync> WeightedLoadBalancer<T> {
    fn new() -> Self {
        Self {
            instances: Arc::new(tokio::sync::RwLock::new(Vec::new())),
        }
    }
}

#[async_trait]
impl<T: Clone + Debug + Send + Sync> LoadBalancer<T> for WeightedLoadBalancer<T> {
    async fn choose(&self) -> Option<T> {
        let instances = self.instances.read().await;
        
        if instances.is_empty() {
            return None;
        }
        
        // 计算总权重
        let total_weight: u32 = instances.iter().map(|(_, w)| w).sum();
        
        if total_weight == 0 {
            // 如果总权重为0，随机选择
            let idx = thread_rng().gen_range(0..instances.len());
            return Some(instances[idx].0.clone());
        }
        
        // 生成随机值
        let value = thread_rng().gen_range(0..total_weight);
        
        // 根据权重选择
        let mut cumulative = 0;
        for (instance, weight) in instances.iter() {
            cumulative += weight;
            if cumulative > value {
                return Some(instance.clone());
            }
        }
        
        // 理论上不会到达这里
        Some(instances.last().unwrap().0.clone())
    }
    
    async fn update_instances(&self, instances: Vec<T>) {
        let instances_with_weight = instances.into_iter()
            .map(|instance| {
                // 这里可以从实例元数据中获取权重
                // 简化示例，使用默认权重
                (instance, 10)
            })
            .collect();
        
        let mut instances_lock = self.instances.write().await;
        *instances_lock = instances_with_weight;
    }
}

// 服务客户端（使用服务发现和负载均衡）
struct ServiceClient<T: Clone + Debug + Send + Sync> {
    service_name: String,
    discovery: Arc<dyn ServiceDiscovery + Send + Sync>,
    load_balancer: Arc<dyn LoadBalancer<T> + Send + Sync>,
}

impl ServiceClient<ServiceInstance> {
    async fn new(
        service_name: &str,
        discovery: Arc<dyn ServiceDiscovery + Send + Sync>,
        load_balancer: Arc<dyn LoadBalancer<ServiceInstance> + Send + Sync>,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        let client = Self {
            service_name: service_name.to_string(),
            discovery,
            load_balancer,
        };
        
        // 初始化负载均衡器
        client.refresh_instances().await?;
        
        // 监听服务变化
        let service_name_clone = service_name.to_string();
        let load_balancer_clone = load_balancer.clone();
        let discovery_clone = discovery.clone();
        
        tokio::spawn(async move {
            // 创建回调
            let callback = Arc::new(move |instances: Vec<ServiceInstance>| {
                // 过滤健康的实例
                let healthy_instances: Vec<ServiceInstance> = instances.into_iter()
                    .filter(|i| i.status == ServiceStatus::UP)
                    .collect();
                
                // 使用运行时执行异步操作
                tokio::spawn({
                    let lb = load_balancer_clone.clone();
                    async move {
                        lb.update_instances(healthy_instances).await;
                    }
                });
            });
            
            // 注册监听
            if let Err(e) = discovery_clone.watch_service(&service_name_clone, callback).await {
                eprintln!("注册服务监听失败: {}", e);
            }
        });
        
        Ok(client)
    }
    
    // 刷新服务实例
    async fn refresh_instances(&self) -> Result<(), Box<dyn std::error::Error>> {
        // 获取服务实例
        let instances = self.discovery.get_instances(&self.service_name).await?;
        
        // 过滤健康的实例
        let healthy_instances: Vec<ServiceInstance> = instances.into_iter()
            .filter(|i| i.status == ServiceStatus::UP)
            .collect();
        
        // 更新负载均衡器
        self.load_balancer.update_instances(healthy_instances).await;
        
        Ok(())
    }
    
// 获取服务实例
async fn get_instance(&self) -> Option<ServiceInstance> {
    self.load_balancer.choose().await
}

// 使用服务
async fn call_service<F, R>(&self, f: F) -> Result<R, Box<dyn std::error::Error>>
where
    F: FnOnce(ServiceInstance) -> Result<R, Box<dyn std::error::Error>> + Send + 'static,
    R: Send + 'static,
{
    // 获取服务实例
    let instance = self.get_instance().await
        .ok_or_else(|| "没有可用的服务实例".to_string())?;
    
    // 调用服务
    f(instance)
}

// 带重试的服务调用
async fn call_service_with_retry<F, R>(&self, f: F, max_retries: usize) -> Result<R, Box<dyn std::error::Error>>
where
    F: Fn(ServiceInstance) -> Result<R, Box<dyn std::error::Error>> + Send + Sync + 'static,
    R: Send + 'static,
{
    let mut last_error = None;
    
    for retry in 0..=max_retries {
        // 获取服务实例
        match self.get_instance().await {
            Some(instance) => {
                // 调用服务
                match f(instance.clone()) {
                    Ok(result) => {
                        return Ok(result);
                    },
                    Err(e) => {
                        println!("服务调用失败（重试 {}/{}）: {}", retry, max_retries, e);
                        last_error = Some(e);
                        
                        // 如果重试次数未达到上限，等待一小段时间
                        if retry < max_retries {
                            tokio::time::sleep(tokio::time::Duration::from_millis(100 * (retry as u64 + 1))).await;
                        }
                    }
                }
            },
            None => {
                // 尝试刷新实例列表
                if let Err(e) = self.refresh_instances().await {
                    println!("刷新服务实例失败: {}", e);
                }
                
                last_error = Some("没有可用的服务实例".into());
                
                // 如果重试次数未达到上限，等待一小段时间
                if retry < max_retries {
                    tokio::time::sleep(tokio::time::Duration::from_millis(100 * (retry as u64 + 1))).await;
                }
            }
        }
    }
    
    Err(last_error.unwrap_or_else(|| "服务调用失败".into()))
}
```

**3. 断路器模式实现**：

```rust
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

// 断路器状态
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CircuitState {
    Closed,      // 正常状态，请求允许通过
    Open,        // 断开状态，请求被拒绝
    HalfOpen,    // 半开状态，允许有限请求通过以测试服务是否恢复
}

// 断路器配置
struct CircuitBreakerConfig {
    failure_threshold: u32,      // 触发断路器打开的失败次数阈值
    success_threshold: u32,      // 半开状态下成功请求的阈值
    open_duration: Duration,     // 断路器打开后保持的时间
    request_timeout: Duration,   // 请求超时时间
}

impl Default for CircuitBreakerConfig {
    fn default() -> Self {
        Self {
            failure_threshold: 5,
            success_threshold: 3,
            open_duration: Duration::from_secs(60),
            request_timeout: Duration::from_secs(5),
        }
    }
}

// 断路器
struct CircuitBreaker {
    name: String,
    state: RwLock<CircuitState>,
    config: CircuitBreakerConfig,
    failure_count: RwLock<u32>,
    success_count: RwLock<u32>,
    last_state_change: RwLock<Instant>,
    metrics: RwLock<CircuitMetrics>,
}

// 断路器指标
struct CircuitMetrics {
    total_requests: u64,
    successful_requests: u64,
    failed_requests: u64,
    rejected_requests: u64,
    timeouts: u64,
}

impl CircuitBreaker {
    fn new(name: &str, config: CircuitBreakerConfig) -> Self {
        Self {
            name: name.to_string(),
            state: RwLock::new(CircuitState::Closed),
            config,
            failure_count: RwLock::new(0),
            success_count: RwLock::new(0),
            last_state_change: RwLock::new(Instant::now()),
            metrics: RwLock::new(CircuitMetrics {
                total_requests: 0,
                successful_requests: 0,
                failed_requests: 0,
                rejected_requests: 0,
                timeouts: 0,
            }),
        }
    }
    
    // 获取当前状态
    async fn get_state(&self) -> CircuitState {
        *self.state.read().await
    }
    
    // 检查是否允许请求通过
    async fn is_allowed(&self) -> bool {
        let current_state = self.get_state().await;
        
        match current_state {
            CircuitState::Closed => true,
            CircuitState::Open => {
                // 检查是否经过了足够的时间以进入半开状态
                let elapsed = {
                    let last_change = *self.last_state_change.read().await;
                    last_change.elapsed()
                };
                
                if elapsed >= self.config.open_duration {
                    // 转换为半开状态
                    self.transition_to_half_open().await;
                    true
                } else {
                    // 更新指标
                    let mut metrics = self.metrics.write().await;
                    metrics.total_requests += 1;
                    metrics.rejected_requests += 1;
                    
                    false
                }
            },
            CircuitState::HalfOpen => true,
        }
    }
    
    // 切换到半开状态
    async fn transition_to_half_open(&self) {
        let mut state = self.state.write().await;
        if *state == CircuitState::Open {
            *state = CircuitState::HalfOpen;
            
            // 重置计数器
            *self.success_count.write().await = 0;
            
            // 更新状态变化时间
            *self.last_state_change.write().await = Instant::now();
            
            println!("断路器 '{}' 状态从 Open 变为 HalfOpen", self.name);
        }
    }
    
    // 切换到打开状态
    async fn transition_to_open(&self) {
        let mut state = self.state.write().await;
        if *state != CircuitState::Open {
            *state = CircuitState::Open;
            
            // 重置计数器
            *self.failure_count.write().await = 0;
            
            // 更新状态变化时间
            *self.last_state_change.write().await = Instant::now();
            
            println!("断路器 '{}' 状态从 {:?} 变为 Open", self.name, *state);
        }
    }
    
    // 切换到关闭状态
    async fn transition_to_closed(&self) {
        let mut state = self.state.write().await;
        if *state != CircuitState::Closed {
            *state = CircuitState::Closed;
            
            // 重置计数器
            *self.success_count.write().await = 0;
            *self.failure_count.write().await = 0;
            
            // 更新状态变化时间
            *self.last_state_change.write().await = Instant::now();
            
            println!("断路器 '{}' 状态从 {:?} 变为 Closed", self.name, *state);
        }
    }
    
    // 记录成功
    async fn record_success(&self) {
        // 更新指标
        let mut metrics = self.metrics.write().await;
        metrics.total_requests += 1;
        metrics.successful_requests += 1;
        
        let current_state = self.get_state().await;
        
        match current_state {
            CircuitState::Closed => {
                // 在关闭状态下，重置失败计数
                *self.failure_count.write().await = 0;
            },
            CircuitState::HalfOpen => {
                // 在半开状态下，增加成功计数
                let mut success_count = self.success_count.write().await;
                *success_count += 1;
                
                // 检查是否达到成功阈值
                if *success_count >= self.config.success_threshold {
                    // 转换为关闭状态
                    drop(success_count); // 释放锁
                    self.transition_to_closed().await;
                }
            },
            CircuitState::Open => {
                // 不应该在打开状态下执行请求，但如果发生，记录成功
            }
        }
    }
    
    // 记录失败
    async fn record_failure(&self) {
        // 更新指标
        let mut metrics = self.metrics.write().await;
        metrics.total_requests += 1;
        metrics.failed_requests += 1;
        
        let current_state = self.get_state().await;
        
        match current_state {
            CircuitState::Closed => {
                // 在关闭状态下，增加失败计数
                let mut failure_count = self.failure_count.write().await;
                *failure_count += 1;
                
                // 检查是否达到失败阈值
                if *failure_count >= self.config.failure_threshold {
                    // 转换为打开状态
                    drop(failure_count); // 释放锁
                    self.transition_to_open().await;
                }
            },
            CircuitState::HalfOpen => {
                // 在半开状态下，一次失败就转换为打开状态
                self.transition_to_open().await;
            },
            CircuitState::Open => {
                // 不应该在打开状态下执行请求，但如果发生，记录失败
            }
        }
    }
    
    // 记录超时
    async fn record_timeout(&self) {
        // 更新指标
        let mut metrics = self.metrics.write().await;
        metrics.total_requests += 1;
        metrics.timeouts += 1;
        
        // 超时视为失败
        drop(metrics); // 释放锁
        self.record_failure().await;
    }
    
    // 使用断路器执行操作
    async fn execute<F, R>(&self, f: F) -> Result<R, Box<dyn std::error::Error>>
    where
        F: FnOnce() -> Result<R, Box<dyn std::error::Error>> + Send + 'static,
        R: Send + 'static,
    {
        // 检查是否允许请求通过
        if !self.is_allowed().await {
            return Err(format!("断路器 '{}' 打开，请求被拒绝", self.name).into());
        }
        
        // 使用超时包装操作
        match tokio::time::timeout(self.config.request_timeout, f()).await {
            Ok(result) => {
                match result {
                    Ok(value) => {
                        // 操作成功
                        self.record_success().await;
                        Ok(value)
                    },
                    Err(e) => {
                        // 操作失败
                        self.record_failure().await;
                        Err(e)
                    }
                }
            },
            Err(_) => {
                // 操作超时
                self.record_timeout().await;
                Err(format!("操作超时 ({}ms)", self.config.request_timeout.as_millis()).into())
            }
        }
    }
    
    // 获取断路器指标
    async fn get_metrics(&self) -> CircuitMetrics {
        self.metrics.read().await.clone()
    }
}

// 可克隆的指标结构
impl Clone for CircuitMetrics {
    fn clone(&self) -> Self {
        Self {
            total_requests: self.total_requests,
            successful_requests: self.successful_requests,
            failed_requests: self.failed_requests,
            rejected_requests: self.rejected_requests,
            timeouts: self.timeouts,
        }
    }
}

// 使用示例
async fn circuit_breaker_example() -> Result<(), Box<dyn std::error::Error>> {
    // 创建断路器
    let breaker = Arc::new(CircuitBreaker::new(
        "user-service",
        CircuitBreakerConfig {
            failure_threshold: 3,
            success_threshold: 2,
            open_duration: Duration::from_secs(5),
            request_timeout: Duration::from_secs(1),
        }
    ));
    
    // 模拟服务调用
    for i in 0..10 {
        let breaker_clone = breaker.clone();
        
        let result = breaker.execute(move || {
            // 模拟操作
            if i >= 3 && i < 7 {
                // 模拟失败
                Err("服务暂时不可用".into())
            } else if i == 8 {
                // 模拟超时
                tokio::time::sleep(Duration::from_secs(2)).await;
                Ok("操作结果")
            } else {
                // 模拟成功
                Ok("操作结果")
            }
        }).await;
        
        match result {
            Ok(value) => println!("请求 {} 成功: {}", i, value),
            Err(e) => println!("请求 {} 失败: {}", i, e),
        }
        
        // 打印当前状态
        println!("断路器状态: {:?}", breaker.get_state().await);
        
        // 短暂等待
        tokio::time::sleep(Duration::from_millis(500)).await;
    }
    
    // 打印指标
    let metrics = breaker.get_metrics().await;
    println!("断路器指标:");
    println!("  总请求数: {}", metrics.total_requests);
    println!("  成功请求数: {}", metrics.successful_requests);
    println!("  失败请求数: {}", metrics.failed_requests);
    println!("  拒绝请求数: {}", metrics.rejected_requests);
    println!("  超时请求数: {}", metrics.timeouts);
    
    Ok(())
}
```

**4. 带有服务发现和断路器的客户端**：

```rust
// 组合服务发现和断路器
struct ResilientServiceClient {
    service_client: ServiceClient<ServiceInstance>,
    circuit_breaker: Arc<CircuitBreaker>,
}

impl ResilientServiceClient {
    async fn new(
        service_name: &str,
        discovery: Arc<dyn ServiceDiscovery + Send + Sync>,
        load_balancer: Arc<dyn LoadBalancer<ServiceInstance> + Send + Sync>,
        circuit_breaker_config: CircuitBreakerConfig,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        // 创建服务客户端
        let service_client = ServiceClient::new(service_name, discovery, load_balancer).await?;
        
        // 创建断路器
        let circuit_breaker = Arc::new(CircuitBreaker::new(service_name, circuit_breaker_config));
        
        Ok(Self {
            service_client,
            circuit_breaker,
        })
    }
    
    // 调用服务
    async fn call_service<F, R>(&self, f: F) -> Result<R, Box<dyn std::error::Error>>
    where
        F: FnOnce(ServiceInstance) -> Result<R, Box<dyn std::error::Error>> + Send + 'static,
        R: Send + 'static,
    {
        let service_client = self.service_client.clone();
        
        // 使用断路器包装服务调用
        self.circuit_breaker.execute(move || {
            let instance = service_client.get_instance().await
                .ok_or_else(|| "没有可用的服务实例".to_string())?;
            
            // 调用服务
            f(instance)
        }).await
    }
    
    // 带重试的服务调用
    async fn call_service_with_retry<F, R>(&self, f: F, max_retries: usize) -> Result<R, Box<dyn std::error::Error>>
    where
        F: Fn(ServiceInstance) -> Result<R, Box<dyn std::error::Error>> + Send + Sync + Clone + 'static,
        R: Send + 'static,
    {
        let mut last_error = None;
        
        for retry in 0..=max_retries {
            let f_clone = f.clone();
            let result = self.call_service(move |instance| {
                f_clone(instance)
            }).await;
            
            match result {
                Ok(value) => return Ok(value),
                Err(e) => {
                    println!("服务调用失败（重试 {}/{}）: {}", retry, max_retries, e);
                    last_error = Some(e);
                    
                    // 如果当前断路器处于打开状态，不再重试
                    if self.circuit_breaker.get_state().await == CircuitState::Open {
                        println!("断路器打开，不再重试");
                        break;
                    }
                    
                    // 如果重试次数未达到上限，等待一小段时间
                    if retry < max_retries {
                        tokio::time::sleep(tokio::time::Duration::from_millis(100 * (retry as u64 + 1))).await;
                    }
                }
            }
        }
        
        Err(last_error.unwrap_or_else(|| "服务调用失败".into()))
    }
    
    // 获取断路器指标
    async fn get_metrics(&self) -> CircuitMetrics {
        self.circuit_breaker.get_metrics().await
    }
}

// 使用示例
async fn resilient_client_example() -> Result<(), Box<dyn std::error::Error>> {
    // 创建服务发现
    let health_checker = Arc::new(HttpHealthChecker::new(Duration::from_secs(5)));
    let discovery = Arc::new(InMemoryServiceDiscovery::new(health_checker));
    
    // 注册一些服务实例
    for i in 1..=3 {
        let instance = ServiceInstance {
            id: format!("user-service-{}", i),
            service_name: "user-service".to_string(),
            host: "localhost".to_string(),
            port: 8080 + i as u16,
            secure: false,
            metadata: HashMap::new(),
            health_check_url: Some(format!("http://localhost:{}/health", 8080 + i as u16)),
            status: ServiceStatus::UP,
            last_updated: chrono::Utc::now(),
        };
        
        discovery.register(instance).await?;
    }
    
    // 创建负载均衡器
    let load_balancer = Arc::new(RoundRobinLoadBalancer::<ServiceInstance>::new());
    
    // 创建弹性服务客户端
    let client = ResilientServiceClient::new(
        "user-service",
        discovery.clone(),
        load_balancer,
        CircuitBreakerConfig {
            failure_threshold: 3,
            success_threshold: 2,
            open_duration: Duration::from_secs(10),
            request_timeout: Duration::from_secs(2),
        },
    ).await?;
    
    // 使用客户端调用服务
    for i in 0..10 {
        let result = client.call_service_with_retry(move |instance| {
            println!("调用服务: {}:{}", instance.host, instance.port);
            
            // 模拟服务调用
            if i >= 3 && i < 7 {
                // 模拟失败
                Err("服务暂时不可用".into())
            } else {
                // 模拟成功
                Ok(format!("来自 {}:{} 的响应", instance.host, instance.port))
            }
        }, 2).await;
        
        match result {
            Ok(response) => println!("请求 {} 成功: {}", i, response),
            Err(e) => println!("请求 {} 失败: {}", i, e),
        }
        
        // 短暂等待
        tokio::time::sleep(Duration::from_millis(500)).await;
    }
    
    // 打印指标
    let metrics = client.get_metrics().await;
    println!("服务调用指标:");
    println!("  总请求数: {}", metrics.total_requests);
    println!("  成功请求数: {}", metrics.successful_requests);
    println!("  失败请求数: {}", metrics.failed_requests);
    println!("  拒绝请求数: {}", metrics.rejected_requests);
    println!("  超时请求数: {}", metrics.timeouts);
    
    Ok(())
}
```

### 4.7 分布式系统测试

测试分布式系统需要特殊的工具和方法，包括模拟网络故障、延迟、服务实例的故障等。

**1. 服务模拟**：

```rust
use warp::Filter;
use std::sync::Arc;
use tokio::sync::RwLock;
use std::collections::HashMap;
use serde::{Serialize, Deserialize};
use std::time::Duration;
use rand::Rng;

// 模拟服务配置
#[derive(Clone, Debug)]
struct MockServiceConfig {
    // 服务参数
    port: u16,
    name: String,
    
    // 故障注入
    failure_rate: f64,            // 失败概率 (0.0-1.0)
    min_latency: Duration,        // 最小延迟
    max_latency: Duration,        // 最大延迟
    timeout_rate: f64,            // 超时概率 (0.0-1.0)
    timeout_duration: Duration,   // 超时时长
}

impl Default for MockServiceConfig {
    fn default() -> Self {
        Self {
            port: 8080,
            name: "mock-service".to_string(),
            failure_rate: 0.0,
            min_latency: Duration::from_millis(10),
            max_latency: Duration::from_millis(50),
            timeout_rate: 0.0,
            timeout_duration: Duration::from_secs(30),
        }
    }
}

// 用户资源
#[derive(Clone, Debug, Serialize, Deserialize)]
struct User {
    id: u64,
    name: String,
    email: String,
}

// 模拟服务
struct MockService {
    config: Arc<RwLock<MockServiceConfig>>,
    users: Arc<RwLock<HashMap<u64, User>>>,
}

impl MockService {
    fn new(config: MockServiceConfig) -> Self {
        let mut users = HashMap::new();
        
        // 添加一些初始用户
        for i in 1..=5 {
            users.insert(i, User {
                id: i,
                name: format!("User {}", i),
                email: format!("user{}@example.com", i),
            });
        }
        
        Self {
            config: Arc::new(RwLock::new(config)),
            users: Arc::new(RwLock::new(users)),
        }
    }
    
    // 启动模拟服务
    async fn start(&self) {
        let config = self.config.clone();
        let users = self.users.clone();
        
        // 健康检查端点
        let health_route = warp::path("health")
            .and(warp::get())
            .and(with_config(config.clone()))
            .and_then(move |config: Arc<RwLock<MockServiceConfig>>| async move {
                // 注入故障
                if should_fail(&config).await {
                    return Err(warp::reject::custom(ServiceError::InternalError));
                }
                
                // 注入延迟
                inject_latency(&config).await;
                
                Ok::<_, warp::Rejection>(warp::reply::json(&serde_json::json!({ "status": "UP" })))
            });
        
        // 获取所有用户
        let get_users = warp::path("users")
            .and(warp::get())
            .and(with_config(config.clone()))
            .and(with_users(users.clone()))
            .and_then(move |config: Arc<RwLock<MockServiceConfig>>, users: Arc<RwLock<HashMap<u64, User>>>| async move {
                // 注入故障
                if should_fail(&config).await {
                    return Err(warp::reject::custom(ServiceError::InternalError));
                }
                
                // 注入延迟
                inject_latency(&config).await;
                
                // 获取用户列表
                let users_lock = users.read().await;
                let users_vec: Vec<User> = users_lock.values().cloned().collect();
                
                Ok::<_, warp::Rejection>(warp::reply::json(&users_vec))
            });
        
        // 获取单个用户
        let get_user = warp::path!("users" / u64)
            .and(warp::get())
            .and(with_config(config.clone()))
            .and(with_users(users.clone()))
            .and_then(move |id: u64, config: Arc<RwLock<MockServiceConfig>>, users: Arc<RwLock<HashMap<u64, User>>>| async move {
                // 注入故障
                if should_fail(&config).await {
                    return Err(warp::reject::custom(ServiceError::InternalError));
                }
                
                // 注入延迟
                inject_latency(&config).await;
                
                // 获取用户
                let users_lock = users.read().await;
                
                if let Some(user) = users_lock.get(&id) {
                    Ok(warp::reply::json(user))
                } else {
                    Err(warp::reject::custom(ServiceError::NotFound))
                }
            });
        
        // 创建用户
        let create_user = warp::path("users")
            .and(warp::post())
            .and(warp::body::json())
            .and(with_config(config.clone()))
            .and(with_users(users.clone()))
            .and_then(move |user: User, config: Arc<RwLock<MockServiceConfig>>, users: Arc<RwLock<HashMap<u64, User>>>| async move {
                // 注入故障
                if should_fail(&config).await {
                    return Err(warp::reject::custom(ServiceError::InternalError));
                }
                
                // 注入延迟
                inject_latency(&config).await;
                
                // 保存用户
                let mut users_lock = users.write().await;
                users_lock.insert(user.id, user.clone());
                
                Ok::<_, warp::Rejection>(warp::reply::with_status(
                    warp::reply::json(&user),
                    warp::http::StatusCode::CREATED,
                ))
            });
        
        // 更新用户
        let update_user = warp::path!("users" / u64)
            .and(warp::put())
            .and(warp::body::json())
            .and(with_config(config.clone()))
            .and(with_users(users.clone()))
            .and_then(move |id: u64, user_update: User, config: Arc<RwLock<MockServiceConfig>>, users: Arc<RwLock<HashMap<u64, User>>>| async move {
                // 注入故障
                if should_fail(&config).await {
                    return Err(warp::reject::custom(ServiceError::InternalError));
                }
                
                // 注入延迟
                inject_latency(&config).await;
                
                // 更新用户
                let mut users_lock = users.write().await;
                
                if users_lock.contains_key(&id) {
                    let mut updated_user = user_update;
                    updated_user.id = id; // 确保ID不变
                    users_lock.insert(id, updated_user.clone());
                    
                    Ok(warp::reply::json(&updated_user))
                } else {
                    Err(warp::reject::custom(ServiceError::NotFound))
                }
            });
        
        // 删除用户
        let delete_user = warp::path!("users" / u64)
            .and(warp::delete())
            .and(with_config(config.clone()))
            .and(with_users(users.clone()))
            .and_then(move |id: u64, config: Arc<RwLock<MockServiceConfig>>, users: Arc<RwLock<HashMap<u64, User>>>| async move {
                // 注入故障
                if should_fail(&config).await {
                    return Err(warp::reject::custom(ServiceError::InternalError));
                }
                
                // 注入延迟
                inject_latency(&config).await;
                
                // 删除用户
                let mut users_lock = users.write().await;
                
                if users_lock.remove(&id).is_some() {
                    Ok(warp::reply::with_status(
                        warp::reply::json(&serde_json::json!({ "success": true })),
                        warp::http::StatusCode::OK,
                    ))
                } else {
                    Err(warp::reject::custom(ServiceError::NotFound))
                }
            });
        
        // 配置端点
        let update_config = warp::path("_config")
            .and(warp::put())
            .and(warp::body::json())
            .and(with_config(config.clone()))
            .and_then(move |new_config: MockServiceConfig, config: Arc<RwLock<MockServiceConfig>>| async move {
                // 更新配置
                let mut config_lock = config.write().await;
                *config_lock = new_config.clone();
                
                Ok::<_, warp::Rejection>(warp::reply::json(&new_config))
            });
        
        // 组合所有路由
        let routes = health_route
            .or(get_users)
            .or(get_user)
            .or(create_user)
            .or(update_user)
            .or(delete_user)
            .or(update_config)
            .recover(handle_rejection);
        
        // 获取端口
        let port = {
            let config_lock = self.config.read().await;
            config_lock.port
        };
        
        println!("启动模拟服务 {} 在端口 {}", {
            let config_lock = self.config.read().await;
            config_lock.name.clone()
        }, port);
        
        // 启动服务器
        warp::serve(routes)
            .run(([0, 0, 0, 0], port))
            .await;
    }
}

// 帮助函数
async fn should_fail(config: &Arc<RwLock<MockServiceConfig>>) -> bool {
    let config_lock = config.read().await;
    let mut rng = rand::thread_rng();
    rng.gen::<f64>() < config_lock.failure_rate
}

async fn inject_latency(config: &Arc<RwLock<MockServiceConfig>>) {
    let config_lock = config.read().await;
    let mut rng = rand::thread_rng();
    
    // 检查是否应该超时
    if rng.gen::<f64>() < config_lock.timeout_rate {
        tokio::time::sleep(config_lock.timeout_duration).await;
        return;
    }
    
    // 正常延迟
    let min_ms = config_lock.min_latency.as_millis() as u64;
    let max_ms = config_lock.max_latency.as_millis() as u64;
    
    if min_ms < max_ms {
        let delay = rng.gen_range(min_ms..max_ms);
        tokio::time::sleep(Duration::from_millis(delay)).await;
    } else {
        tokio::time::sleep(config_lock.min_latency).await;
    }
}

// 辅助函数，用于传递状态
fn with_config(config: Arc<RwLock<MockServiceConfig>>) -> impl Filter<Extract = (Arc<RwLock<MockServiceConfig>>,), Error = std::convert::Infallible> + Clone {
    warp::any().map(move || config.clone())
}

fn with_users(users: Arc<RwLock<HashMap<u64, User>>>) -> impl Filter<Extract = (Arc<RwLock<HashMap<u64, User>>>,), Error = std::convert::Infallible> + Clone {
    warp::any().map(move || users.clone())
}

// 错误类型
#[derive(Debug)]
enum ServiceError {
    NotFound,
    InternalError,
}

impl warp::reject::Reject for ServiceError {}

// 错误处理
async fn handle_rejection(err: warp::Rejection) -> Result<impl warp::Reply, std::convert::Infallible> {
    let (code, message) = if err.is_not_found() {
        (warp::http::StatusCode::NOT_FOUND, "找不到资源".to_string())
    } else if let Some(ServiceError::NotFound) = err.find() {
        (warp::http::StatusCode::NOT_FOUND, "找不到用户".to_string())
    } else if let Some(ServiceError::InternalError) = err.find() {
        (warp::http::StatusCode::INTERNAL_SERVER_ERROR, "服务器内部错误".to_string())
    } else {
        eprintln!("未处理的拒绝: {:?}", err);
        (warp::http::StatusCode::INTERNAL_SERVER_ERROR, "未知错误".to_string())
    };
    
    Ok(warp::reply::with_status(
        warp::reply::json(&serde_json::json!({ "error": message })),
        code,
    ))
}

// 使用示例
async fn mock_service_example() {
    // 创建模拟服务配置
    let config = MockServiceConfig {
        port: 8080,
        name: "user-service".to_string(),
        failure_rate: 0.1,            // 10%的请求会失败
        min_latency: Duration::from_millis(50),
        max_latency: Duration::from_millis(200),
        timeout_rate: 0.05,           // 5%的请求会超时
        timeout_duration: Duration::from_secs(5),
    };
    
    // 创建并启动模拟服务
    let service = MockService::new(config);
    service.start().await;
}
```

**2. 混沌测试工具**：

```rust
use std::sync::Arc;
use tokio::sync::RwLock;
use std::collections::HashMap;
use std::time::{Duration, Instant};
use rand::{thread_rng, Rng};
use futures::future::join_all;

// 混沌测试配置
struct ChaosConfig {
    // 服务实例随机故障概率 (每分钟)
    service_failure_rate: f64,
    
    // 网络延迟
    network_latency_min: Duration,
    network_latency_max: Duration,
    
    // 网络分区概率 (每小时)
    network_partition_rate: f64,
    network_partition_duration: Duration,
    
    // 资源耗尽概率 (每小时)
    resource_exhaustion_rate: f64,
    resource_exhaustion_duration: Duration,
    
    // 时钟漂移概率 (每天)
    clock_drift_rate: f64,
    clock_drift_amount: Duration,
}

impl Default for ChaosConfig {
    fn default() -> Self {
        Self {
            service_failure_rate: 0.05,  // 每分钟5%的概率
            network_latency_min: Duration::from_millis(10),
            network_latency_max: Duration::from_millis(500),
            network_partition_rate: 0.01,  // 每小时1%的概率
            network_partition_duration: Duration::from_secs(300),  // 5分钟
            resource_exhaustion_rate: 0.01,  // 每小时1%的概率
            resource_exhaustion_duration: Duration::from_secs(180),  // 3分钟
            clock_drift_rate: 0.05,  // 每天5%的概率
            clock_drift_amount: Duration::from_secs(10),  // 10秒
        }
    }
}

// 混沌猴子类型
enum MonkeyType {
    ServiceKiller,     // 杀死服务实例
    LatencyMonkey,     // 注入网络延迟
    PartitionMonkey,   // 创建网络分区
    ResourceMonkey,    // 资源耗尽（CPU、内存）
    ClockMonkey,       // 时钟漂移
}

// 被测服务
#[derive(Clone, Debug)]
struct TargetService {
    id: String,
    name: String,
    host: String,
    port: u16,
    is_healthy: bool,
    last_failure: Option<Instant>,
}

// 混沌测试工具
struct ChaosMonkey {
    config: Arc<RwLock<ChaosConfig>>,
    services: Arc<RwLock<HashMap<String, TargetService>>>,
    active_failures: Arc<RwLock<HashMap<String, (MonkeyType, Instant, Duration)>>>,
    is_running: Arc<RwLock<bool>>,
}

impl ChaosMonkey {
    fn new(config: ChaosConfig) -> Self {
        Self {
            config: Arc::new(RwLock::new(config)),
            services: Arc::new(RwLock::new(HashMap::new())),
            active_failures: Arc::new(RwLock::new(HashMap::new())),
            is_running: Arc::new(RwLock::new(false)),
        }
    }
    
    // 添加被测服务
    async fn add_service(&self, service: TargetService) {
        let mut services = self.services.write().await;
        services.insert(service.id.clone(), service);
    }
    
    // 删除被测服务
    async fn remove_service(&self, service_id: &str) {
        let mut services = self.services.write().await;
        services.remove(service_id);
    }
    
    // 开始注入故障
    async fn start(&self) {
        let mut is_running = self.is_running.write().await;
        if *is_running {
            return;
        }
        
        *is_running = true;
        drop(is_running);  // 释放锁
        
        let config = self.config.clone();
        let services = self.services.clone();
        let active_failures = self.active_failures.clone();
        let is_running = self.is_running.clone();
        
        // 启动故障注入循环
        tokio::spawn(async move {
            println!("混沌测试开始");
            
            while *is_running.read().await {
                // 休眠一小段时间
                tokio::time::sleep(Duration::from_secs(1)).await;
                
                // 检查和恢复活跃故障
                Self::check_active_failures(&active_failures, &services).await;
                
                // 随机注入新故障
                Self::inject_random_failures(&config, &services, &active_failures).await;
            }
            
            println!("混沌测试结束");
        });
    }
    
    // 停止注入故障
    async fn stop(&self) {
        let mut is_running = self.is_running.write().await;
        *is_running = false;
        
        // 恢复所有故障
        let mut active_failures = self.active_failures.write().await;
        active_failures.clear();
        
        // 恢复所有服务健康状态
        let mut services = self.services.write().await;
        for (_, service) in services.iter_mut() {
            service.is_healthy = true;
        }
    }
    
    // 检查和恢复活跃故障
    async fn check_active_failures(
        active_failures: &Arc<RwLock<HashMap<String, (MonkeyType, Instant, Duration)>>>,
        services: &Arc<RwLock<HashMap<String, TargetService>>>,
    ) {
        let now = Instant::now();
        let mut failures_to_remove = Vec::new();
        
        // 检查需要恢复的故障
        {
            let failures = active_failures.read().await;
            
            for (id, (monkey_type, start_time, duration)) in failures.iter() {
                if now.duration_since(*start_time) >= *duration {
                    failures_to_remove.push((id.clone(), monkey_type.clone()));
                }
            }
        }
        
        // 恢复故障
        if !failures_to_remove.is_empty() {
            let mut failures = active_failures.write().await;
            let mut services_lock = services.write().await;
            
            for (id, monkey_type) in failures_to_remove {
                failures.remove(&id);
                
                match monkey_type {
                    MonkeyType::ServiceKiller => {
                        if let Some(service) = services_lock.get_mut(&id) {
                            service.is_healthy = true;
                            println!("恢复服务: {} ({}:{})", service.name, service.host, service.port);
                        }
                    },
                    MonkeyType::PartitionMonkey => {
                        println!("修复网络分区: {}", id);
                    },
                    MonkeyType::ResourceMonkey => {
                        println!("恢复资源利用: {}", id);
                    },
                    MonkeyType::ClockMonkey => {
                        println!("修复时钟漂移: {}", id);
                    },
                    _ => {}
                }
            }
        }
    }
    
    // 随机注入故障
    async fn inject_random_failures(
        config: &Arc<RwLock<ChaosConfig>>,
        services: &Arc<RwLock<HashMap<String, TargetService>>>,
        active_failures: &Arc<RwLock<HashMap<String, (MonkeyType, Instant, Duration)>>>,
    ) {
        let config_lock = config.read().await;
        let mut rng = thread_rng();
        
        // 服务故障
        if rng.gen::<f64>() < config_lock.service_failure_rate / 60.0 {  // 转换为每秒概率
            let services_lock = services.read().await;
            
            if !services_lock.is_empty() {
                // 随机选择一个服务
                let service_ids: Vec<String> = services_lock.keys().cloned().collect();
                let idx = rng.gen_range(0..service_ids.len());
                let service_id = &service_ids[idx];
                
                // 检查服务是否已有故障
                let failures_lock = active_failures.read().await;
                if !failures_lock.contains_key(service_id) {
                    drop(failures_lock);  // 释放锁
                    
                    // 杀死服务
                    Self::kill_service(service_id.clone(), services, active_failures).await;
                }
            }
        }
        
        // 网络分区
        if rng.gen::<f64>() < config_lock.network_partition_rate / 3600.0 {  // 转换为每秒概率
            Self::create_network_partition(
                config_lock.network_partition_duration,
                services,
                active_failures,
            ).await;
        }
        
        // 资源耗尽
        if rng.gen::<f64>() < config_lock.resource_exhaustion_rate / 3600.0 {  // 转换为每秒概率
            let services_lock = services.read().await;
            
            if !services_lock.is_empty() {
                // 随机选择一个服务
                let service_ids: Vec<String> = services_lock.keys().cloned().collect();
                let idx = rng.gen_range(0..service_ids.len());
                let service_id = &service_ids[idx];
                
                // 检查服务是否已有故障
                let failures_lock = active_failures.read().await;
                if !failures_lock.contains_key(service_id) {
                    drop(failures_lock);  // 释放锁
                    
                    // 耗尽资源
                    Self::exhaust_resources(
                        service_id.clone(),
                        config_lock.resource_exhaustion_duration,
                        active_failures,
                    ).await;
                }
            }
        }
        
        // 时钟漂移
        if rng.gen::<f64>() < config_lock.clock_drift_rate / 86400.0 {  // 转换为每秒概率
            let services_lock = services.read().await;
            
            if !services_lock.is_empty() {
                // 随机选择一个服务
                let service_ids: Vec<String> = services_lock.keys().cloned().collect();
                let idx = rng.gen_range(0..service_ids.len());
                let service_id = &service_ids[idx];
                
                // 检查服务是否已有故障
                let failures_lock = active_failures.read().await;
                if !failures_lock.contains_key(service_id) {
                    drop(failures_lock);  // 释放锁
                    
                    // 漂移时钟
                    Self::drift_clock(
                        service_id.clone(),
                        config_lock.clock_drift_amount,
                        Duration::from_hours(1),  // 假设漂移持续1小时
                        active_failures,
                    ).await;
                }
            }
        }
    }
    
    // 杀死服务
    async fn kill_service(
        service_id: String,
        services: &Arc<RwLock<HashMap<String, TargetService>>>,
        active_failures: &Arc<RwLock<HashMap<String, (MonkeyType, Instant, Duration)>>>,
    ) {
        let duration = Duration::from_secs(rng.gen_range(30..300));  // 30秒到5分钟
        
        // 更新服务状态
        {
            let mut services_lock = services.write().await;
            
            if let Some(service) = services_lock.get_mut(&service_id) {
                service.is_healthy = false;
                service.last_failure = Some(Instant::now());
                
                println!("杀死服务: {} ({}:{}) 持续 {:?}", 
                        service.name, service.host, service.port, duration);
            } else {
                return;
            }
        }
        
        // 记录故障
        let mut failures_lock = active_failures.write().await;
        failures_lock.insert(
            service_id,
            (MonkeyType::ServiceKiller, Instant::now(), duration),
        );
    }
    
    // 创建网络分区
    async fn create_network_partition(
        duration: Duration,
        services: &Arc<RwLock<HashMap<String, TargetService>>>,
        active_failures: &Arc<RwLock<HashMap<String, (MonkeyType, Instant, Duration)>>>,
    ) {
        let services_lock = services.read().await;
        
        if services_lock.len() < 2 {
            return;  // 至少需要两个服务才能形成分区
        }
        
        // 随机选择两组服务
        let service_ids: Vec<String> = services_lock.keys().cloned().collect();
        let split_point = rng.gen_range(1..service_ids.len());
        
        let group_a: Vec<String> = service_ids[0..split_point].to_vec();
        let group_b: Vec<String> = service_ids[split_point..].to_vec();
        
        println!("创建网络分区: 组A({})与组B({})之间 持续 {:?}", 
                group_a.len(), group_b.len(), duration);
        
        // 为每一对服务创建分区
        let mut failures_lock = active_failures.write().await;
        
        for a_id in &group_a {
            for b_id in &group_b {
                let partition_id = format!("partition:{}:{}", a_id, b_id);
                
                failures_lock.insert(
                    partition_id,
                    (MonkeyType::PartitionMonkey, Instant::now(), duration),
                );
            }
        }
    }
    
    // 耗尽资源
    async fn exhaust_resources(
        service_id: String,
        duration: Duration,
        active_failures: &Arc<RwLock<HashMap<String, (MonkeyType, Instant, Duration)>>>,
    ) {
        println!("耗尽服务资源: {} 持续 {:?}", service_id, duration);
        
        // 记录故障
        let mut failures_lock = active_failures.write().await;
        failures_lock.insert(
            service_id,
            (MonkeyType::ResourceMonkey, Instant::now(), duration),
        );
    }
    
    // 时钟漂移
    async fn drift_clock(
        service_id: String,
        amount: Duration,
        duration: Duration,
        active_failures: &Arc<RwLock<HashMap<String, (MonkeyType, Instant, Duration)>>>,
    ) {
        println!("服务时钟漂移: {} 偏移 {:?} 持续 {:?}", service_id, amount, duration);
        
        // 记录故障
        let mut failures_lock = active_failures.write().await;
        failures_lock.insert(
            service_id,
            (MonkeyType::ClockMonkey, Instant::now(), duration),
        );
    }
    
    // 获取当前活跃故障
    async fn get_active_failures(&self) -> HashMap<String, (MonkeyType, Instant, Duration)> {
        let failures = self.active_failures.read().await;
        failures.clone()
    }
    
    // 手动恢复所有故障
    async fn recover_all_failures(&self) {
        let mut active_failures = self.active_failures.write().await;
        active_failures.clear();
        
        let mut services = self.services.write().await;
        for (_, service) in services.iter_mut() {
            service.is_healthy = true;
        }
        
        println!("手动恢复所有故障");
    }
}

// 使用示例
async fn chaos_testing_example() {
    // 创建混沌测试配置
    let config = ChaosConfig {
        service_failure_rate: 0.1,  // 提高故障率以便于演示
        network_latency_min: Duration::from_millis(10),
        network_latency_max: Duration::from_millis(200),
        network_partition_rate: 0.05,
        network_partition_duration: Duration::from_secs(60),
        resource_exhaustion_rate: 0.05,
        resource_exhaustion_duration: Duration::from_secs(60),
        clock_drift_rate: 0.05,
        clock_drift_amount: Duration::from_secs(5),
    };
    
    // 创建混沌测试工具
    let chaos_monkey = Arc::new(ChaosMonkey::new(config));
    
    // 添加被测服务
    for i in 1..=5 {
        let service = TargetService {
            id: format!("service-{}", i),
            name: format!("Service {}", i),
            host: "localhost".to_string(),
            port: 8080 + i,
            is_healthy: true,
            last_failure: None,
        };
        
        chaos_monkey.add_service(service).await;
    }
    
    // 启动混沌测试
    chaos_monkey.start().await;
    
    // 运行一段时间
    println!("混沌测试运行中，按Ctrl+C停止...");
    
    // 模拟运行1分钟
    tokio::time::sleep(Duration::from_secs(60)).await;
    
    // 打印当前活跃故障
    let active_failures = chaos_monkey.get_active_failures().await;
    println!("当前活跃故障数: {}", active_failures.len());
    
    for (id, (monkey_type, start_time, duration)) in active_failures {
        let elapsed = start_time.elapsed();
        let remaining = if duration > elapsed {
            duration - elapsed
        } else {
            Duration::from_secs(0)
        };
        
        println!("故障ID: {}, 类型: {:?}, 已持续: {:?}, 剩余: {:?}", 
                 id, monkey_type, elapsed, remaining);
    }
    
    // 停止混沌测试
    chaos_monkey.stop().await;
    println!("混沌测试已停止");
}
```

**3. 分布式系统一致性验证**：

```rust
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use serde::{Serialize, Deserialize};
use rand::{thread_rng, Rng};
use futures::future::join_all;

// 待验证数据
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
struct DataItem {
    id: String,
    value: String,
    version: u64,
    last_modified: chrono::DateTime<chrono::Utc>,
}

// 一致性验证器
struct ConsistencyVerifier {
    endpoints: Vec<String>,
    client: reqwest::Client,
    results: Arc<RwLock<HashMap<String, ConsistencyResult>>>,
}

// 验证结果
#[derive(Clone, Debug)]
struct ConsistencyResult {
    data_id: String,
    is_consistent: bool,
    values: HashMap<String, DataItem>,  // 端点 -> 数据
    errors: HashMap<String, String>,    // 端点 -> 错误信息
    verification_time: chrono::DateTime<chrono::Utc>,
}

impl ConsistencyVerifier {
    fn new(endpoints: Vec<String>) -> Self {
        Self {
            endpoints,
            client: reqwest::Client::builder()
                .timeout(Duration::from_secs(5))
                .build()
                .unwrap(),
            results: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    // 验证单个数据项
    async fn verify_data_item(&self, data_id: &str, path: &str) -> ConsistencyResult {
        let mut values = HashMap::new();
        let mut errors = HashMap::new();
        
        // 创建并发请求
        let mut futures = Vec::new();
        
        for endpoint in &self.endpoints {
            let url = format!("{}/{}/{}", endpoint, path, data_id);
            let client = self.client.clone();
            
            futures.push(async move {
                match client.get(&url).send().await {
                    Ok(response) => {
                        if response.status().is_success() {
                            match response.json::<DataItem>().await {
                                Ok(data) => (endpoint.clone(), Ok(data)),
                                Err(e) => (endpoint.clone(), Err(format!("解析错误: {}", e))),
                            }
                        } else {
                            (endpoint.clone(), Err(format!("HTTP错误: {}", response.status())))
                        }
                    },
                    Err(e) => (endpoint.clone(), Err(format!("请求错误: {}", e))),
                }
            });
        }
        
        // 等待所有请求完成
        let results = join_all(futures).await;
        
        // 处理结果
        for (endpoint, result) in results {
            match result {
                Ok(data) => {
                    values.insert(endpoint, data);
                },
                Err(error) => {
                    errors.insert(endpoint, error);
                },
            }
        }
        
        // 检查一致性
        let mut reference_data: Option<&DataItem> = None;
        let mut is_consistent = true;
        
        for (_, data) in &values {
            if let Some(ref_data) = reference_data {
                if ref_data != data {
                    is_consistent = false;
                    break;
                }
            } else {
                reference_data = Some(data);
            }
        }
        
        // 如果有错误，也视为不一致
        if !errors.is_empty() {
            is_consistent = false;
        }
        
        ConsistencyResult {
            data_id: data_id.to_string(),
            is_consistent,
            values,
            errors,
            verification_time: chrono::Utc::now(),
        }
    }
    
    // 批量验证数据
    async fn verify_data_items(&self, data_ids: Vec<String>, path: &str) -> Vec<ConsistencyResult> {
        let mut results = Vec::new();
        
        for data_id in data_ids {
            let result = self.verify_data_item(&data_id, path).await;
            
            // 存储结果
            {
                let mut results_lock = self.results.write().await;
                results_lock.insert(data_id.clone(), result.clone());
            }
            
            results.push(result);
        }
        
        results
    }
    
    // 生成一致性报告
    async fn generate_report(&self) -> ConsistencyReport {
        let results_lock = self.results.read().await;
        
        let mut consistent_count = 0;
        let mut inconsistent_count = 0;
        let mut error_count = 0;
        
        for result in results_lock.values() {
            if result.is_consistent {
                consistent_count += 1;
            } else {
                inconsistent_count += 1;
                
                if !result.errors.is_empty() {
                    error_count += 1;
                }
            }
        }
        
        ConsistencyReport {
            total_items: results_lock.len(),
            consistent_items: consistent_count,
            inconsistent_items: inconsistent_count,
            items_with_errors: error_count,
            endpoints: self.endpoints.clone(),
            verification_time: chrono::Utc::now(),
        }
    }
    
    // 获取不一致的数据项
    async fn get_inconsistent_items(&self) -> Vec<ConsistencyResult> {
        let results_lock = self.results.read().await;
        
        results_lock.values()
            .filter(|r| !r.is_consistent)
            .cloned()
            .collect()
    }
}

// 一致性报告
#[derive(Clone, Debug, Serialize)]
struct ConsistencyReport {
    total_items: usize,
    consistent_items: usize,
    inconsistent_items: usize,
    items_with_errors: usize,
    endpoints: Vec<String>,
    verification_time: chrono::DateTime<chrono::Utc>,
}

// 使用示例
async fn consistency_verification_example() {
    // 创建一致性验证器
    let verifier = ConsistencyVerifier::new(vec![
        "http://localhost:8081".to_string(),
        "http://localhost:8082".to_string(),
        "http://localhost:8083".to_string(),
    ]);
    
    // 验证一些数据项
    let data_ids = vec![
        "item-1".to_string(),
        "item-2".to_string(),
        "item-3".to_string(),
        "item-4".to_string(),
        "item-5".to_string(),
    ];
    
    let results = verifier.verify_data_items(data_ids, "api/data").await;
    
    // 打印每个数据项的验证结果
    for result in &results {
        println!("数据ID: {}", result.data_id);
        println!("一致性: {}", if result.is_consistent { "一致" } else { "不一致" });
        
        if !result.is_consistent {
            println!("数据值:");
            for (endpoint, data) in &result.values {
                println!("  {}: {:?}", endpoint, data);
            }
            
            for (endpoint, error) in &result.errors {
                println!("  {}: 错误: {}", endpoint, error);
            }
        }
        
        println!();
    }
    
    // 生成报告
    let report = verifier.generate_report().await;
    
    println!("一致性报告:");
    println!("  总数据项: {}", report.total_items);
    println!("  一致数据项: {}", report.consistent_items);
    println!("  不一致数据项: {}", report.inconsistent_items);
    println!("  有错误的数据项: {}", report.items_with_errors);
    println!("  验证时间: {}", report.verification_time);
}
```

**4. 分布式系统测试框架**：

```rust
use std::sync::Arc;
use std::collections::HashMap;
use tokio::sync::{RwLock, Mutex};
use async_trait::async_trait;
use serde::{Serialize, Deserialize};
use futures::future::join_all;

// 测试场景
#[async_trait]
trait TestScenario {
    // 获取场景名称
    fn name(&self) -> &str;
    
    // 场景初始化
    async fn setup(&self) -> Result<(), Box<dyn std::error::Error>>;
    
    // 场景清理
    async fn teardown(&self) -> Result<(), Box<dyn std::error::Error>>;
    
    // 运行测试
    async fn run(&self) -> Result<TestResult, Box<dyn std::error::Error>>;
}

// 测试断言
#[derive(Clone, Debug)]
struct Assertion {
    name: String,
    passed: bool,
    message: Option<String>,
}

// 测试结果
#[derive(Clone, Debug)]
struct TestResult {
    scenario_name: String,
    success: bool,
    assertions: Vec<Assertion>,
    execution_time: Duration,
    error_message: Option<String>,
}

// 测试框架
struct DistributedTestFramework {
    scenarios: Vec<Arc<dyn TestScenario + Send + Sync>>,
    results: Arc<RwLock<HashMap<String, TestResult>>>,
    config: TestConfig,
}

// 测试配置
#[derive(Clone, Debug)]
struct TestConfig {
    parallel_execution: bool,
    timeout: Duration,
    retry_count: u32,
    retry_delay: Duration,
}

impl Default for TestConfig {
    fn default() -> Self {
        Self {
            parallel_execution: true,
            timeout: Duration::from_secs(60),
            retry_count: 3,
            retry_delay: Duration::from_secs(5),
        }
    }
}

impl DistributedTestFramework {
    fn new(config: TestConfig) -> Self {
        Self {
            scenarios: Vec::new(),
            results: Arc::new(RwLock::new(HashMap::new())),
            config,
        }
    }
    
    // 添加测试场景
    fn add_scenario(&mut self, scenario: Arc<dyn TestScenario + Send + Sync>) {
        self.scenarios.push(scenario);
    }
    
    // 运行所有测试
    async fn run_all(&self) -> Vec<TestResult> {
        if self.config.parallel_execution {
            self.run_parallel().await
        } else {
            self.run_sequential().await
        }
    }
    
    // 并行运行测试
    async fn run_parallel(&self) -> Vec<TestResult> {
        let mut futures = Vec::new();
        
        for scenario in &self.scenarios {
            let scenario_clone = scenario.clone();
            let config = self.config.clone();
            let results = self.results.clone();
            
            futures.push(async move {
                let result = Self::run_scenario_with_retry(scenario_clone, config).await;
                
                // 存储结果
                let mut results_lock = results.write().await;
                results_lock.insert(scenario_clone.name().to_string(), result.clone());
                
                result
            });
        }
        
        // 等待所有测试完成
        join_all(futures).await
    }
    
    // 顺序运行测试
    async fn run_sequential(&self) -> Vec<TestResult> {
        let mut results = Vec::new();
        
        for scenario in &self.scenarios {
            let result = Self::run_scenario_with_retry(scenario.clone(), self.config.clone()).await;
            
            // 存储结果
            {
                let mut results_lock = self.results.write().await;
                results_lock.insert(scenario.name().to_string(), result.clone());
            }
            
            results.push(result);
        }
        
        results
    }
    
    // 运行单个场景（带重试）
    async fn run_scenario_with_retry(
        scenario: Arc<dyn TestScenario + Send + Sync>,
        config: TestConfig,
    ) -> TestResult {
        let scenario_name = scenario.name().to_string();
        let start_time = Instant::now();
        
        for retry in 0..=config.retry_count {
            if retry > 0 {
                println!("重试场景 '{}' ({}/{})", scenario_name, retry, config.retry_count);
                tokio::time::sleep(config.retry_delay).await;
            }
            
            // 设置场景
            match scenario.setup().await {
                Ok(_) => {},
                Err(e) => {
                    // 设置失败，继续重试
                    println!("场景 '{}' 设置失败: {}", scenario_name, e);
                    continue;
                }
            }
            
            // 运行场景
            let result = match tokio::time::timeout(config.timeout, scenario.run()).await {
                Ok(result) => match result {
                    Ok(r) => r,
                    Err(e) => {
                        // 运行失败，清理并重试
                        let _ = scenario.teardown().await;
                        
                        if retry == config.retry_count {
                            // 最后一次重试，返回错误
                            TestResult {
                                scenario_name: scenario_name.clone(),
                                success: false,
                                assertions: Vec::new(),
                                execution_time: start_time.elapsed(),
                                error_message: Some(format!("执行错误: {}", e)),
                            }
                        } else {
                            continue;
                        }
                    }
                },
                Err(_) => {
                    // 超时，清理并重试
                    let _ = scenario.teardown().await;
                    
                    if retry == config.retry_count {
                        // 最后一次重试，返回超时错误
                        TestResult {
                            scenario_name: scenario_name.clone(),
                            success: false,
                            assertions: Vec::new(),
                            execution_time: config.timeout,
                            error_message: Some(format!("场景执行超时 ({}s)", config.timeout.as_secs())),
                        }
                    } else {
                        continue;
                    }
                }
            };
            
            // 清理场景
            if let Err(e) = scenario.teardown().await {
                println!("场景 '{}' 清理失败: {}", scenario_name, e);
            }
            
            // 如果测试成功或已经是最后一次重试，返回结果
            if result.success || retry == config.retry_count {
                return result;
            }
        }
        
        // 所有重试都失败
        TestResult {
            scenario_name,
            success: false,
            assertions: Vec::new(),
            execution_time: start_time.elapsed(),
            error_message: Some("所有重试都失败".to_string()),
        }
    }
    
    // 生成测试报告
    async fn generate_report(&self) -> TestReport {
        let results_lock = self.results.read().await;
        
        let mut passed_count = 0;
        let mut failed_count = 0;
        let mut total_duration = Duration::from_secs(0);
        
        for result in results_lock.values() {
            if result.success {
                passed_count += 1;
            } else {
                failed_count += 1;
            }
            
            total_duration += result.execution_time;
        }
        
        TestReport {
            total_scenarios: results_lock.len(),
            passed_scenarios: passed_count,
            failed_scenarios: failed_count,
            total_duration,
            scenarios: results_lock.values().cloned().collect(),
            timestamp: chrono::Utc::now(),
        }
    }
}

// 测试报告
#[derive(Clone, Debug, Serialize)]
struct TestReport {
    total_scenarios: usize,
    passed_scenarios: usize,
    failed_scenarios: usize,
    total_duration: Duration,
    scenarios: Vec<TestResult>,
    timestamp: chrono::DateTime<chrono::Utc>,
}

// 示例测试场景
struct ServiceAvailabilityScenario {
    service_urls: Vec<String>,
    client: reqwest::Client,
}

#[async_trait]
impl TestScenario for ServiceAvailabilityScenario {
    fn name(&self) -> &str {
        "服务可用性测试"
    }
    
    async fn setup(&self) -> Result<(), Box<dyn std::error::Error>> {
        println!("设置服务可用性测试");
        // 这里可以启动必要的服务或准备测试数据
        Ok(())
    }
    
    async fn teardown(&self) -> Result<(), Box<dyn std::error::Error>> {
        println!("清理服务可用性测试");
        // 这里可以关闭服务或清理测试数据
        Ok(())
    }
    
    async fn run(&self) -> Result<TestResult, Box<dyn std::error::Error>> {
        let start_time = Instant::now();
        let mut assertions = Vec::new();
        
        // 检查所有服务是否可用
        for url in &self.service_urls {
            let response = self.client.get(url).send().await;
            
            let assertion = match response {
                Ok(resp) => {
                    let passed = resp.status().is_success();
                    
                    Assertion {
                        name: format!("服务 {} 是否可用", url),
                        passed,
                        message: if passed {
                            None
                        } else {
                            Some(format!("服务返回状态码: {}", resp.status()))
                        },
                    }
                },
                Err(e) => {
                    Assertion {
                        name: format!("服务 {} 是否可用", url),
                        passed: false,
                        message: Some(format!("请求错误: {}", e)),
                    }
                }
            };
            
            assertions.push(assertion);
        }
        
        // 检查测试是否成功
        let success = assertions.iter().all(|a| a.passed);
        
        Ok(TestResult {
            scenario_name: self.name().to_string(),
            success,
            assertions,
            execution_time: start_time.elapsed(),
            error_message: None,
        })
    }
}

// 数据一致性场景
struct DataConsistencyScenario {
    verifier: Arc<ConsistencyVerifier>,
    data_ids: Vec<String>,
}

#[async_trait]
impl TestScenario for DataConsistencyScenario {
    fn name(&self) -> &str {
        "数据一致性测试"
    }
    
    async fn setup(&self) -> Result<(), Box<dyn std::error::Error>> {
        println!("设置数据一致性测试");
        // 这里可以准备测试数据
        Ok(())
    }
    
    async fn teardown(&self) -> Result<(), Box<dyn std::error::Error>> {
        println!("清理数据一致性测试");
        // 这里可以清理测试数据
        Ok(())
    }
    
    async fn run(&self) -> Result<TestResult, Box<dyn std::error::Error>> {
        let start_time = Instant::now();
        
        // 验证数据一致性
        let results = self.verifier.verify_data_items(self.data_ids.clone(), "api/data").await;
        
        // 创建断言
        let mut assertions = Vec::new();
        
        for result in results {
            let assertion = Assertion {
                name: format!("数据项 {} 是否一致", result.data_id),
                passed: result.is_consistent,
                message: if result.is_consistent {
                    None
                } else {
                    let mut message = String::new();
                    
                    // 收集错误信息
                    for (endpoint, error) in &result.errors {
                        message.push_str(&format!("{}出错: {}\n", endpoint, error));
                    }
                    
                    // 收集不一致的数据
                    if !result.values.is_empty() {
                        message.push_str("值不一致:\n");
                        
                        for (endpoint, data) in &result.values {
                            message.push_str(&format!("{}的值: 版本 {}, 值 {}\n", 
                                          endpoint, data.version, data.value));
                        }
                    }
                    
                    Some(message)
                },
            };
            
            assertions.push(assertion);
        }
        
        // 检查测试是否成功
        let success = assertions.iter().all(|a| a.passed);
        
        Ok(TestResult {
            scenario_name: self.name().to_string(),
            success,
            assertions,
            execution_time: start_time.elapsed(),
            error_message: None,
        })
    }
}

// 故障恢复场景
struct FailureRecoveryScenario {
    chaos_monkey: Arc<ChaosMonkey>,
    service_client: Arc<ResilientServiceClient>,
    recovery_timeout: Duration,
}

#[async_trait]
impl TestScenario for FailureRecoveryScenario {
    fn name(&self) -> &str {
        "故障恢复测试"
    }
    
    async fn setup(&self) -> Result<(), Box<dyn std::error::Error>> {
        println!("设置故障恢复测试");
        // 启动混沌测试
        self.chaos_monkey.start().await;
        Ok(())
    }
    
    async fn teardown(&self) -> Result<(), Box<dyn std::error::Error>> {
        println!("清理故障恢复测试");
        // 停止混沌测试
        self.chaos_monkey.stop().await;
        self.chaos_monkey.recover_all_failures().await;
        Ok(())
    }
    
    async fn run(&self) -> Result<TestResult, Box<dyn std::error::Error>> {
        let start_time = Instant::now();
        let mut assertions = Vec::new();
        
        // 记录初始服务状态
        let mut initial_success = false;
        
        // 尝试调用服务
        let result = self.service_client.call_service(|instance| {
            Ok(format!("服务 {}:{} 正常响应", instance.host, instance.port))
        }).await;
        
        if result.is_ok() {
            initial_success = true;
        }
        
        assertions.push(Assertion {
            name: "初始服务状态".to_string(),
            passed: initial_success,
            message: result.err().map(|e| format!("初始错误: {}", e)),
        });
        
        // 注入故障
        println!("注入服务故障");
        
        // 等待一段时间使故障生效
        tokio::time::sleep(Duration::from_secs(5)).await;
        
        // 检查服务是否失败
        let failure_result = self.service_client.call_service(|instance| {
            Ok(format!("服务 {}:{} 正常响应", instance.host, instance.port))
        }).await;
        
        let service_failed = failure_result.is_err();
        
        assertions.push(Assertion {
            name: "服务是否故障".to_string(),
            passed: service_failed,
            message: if service_failed {
                failure_result.err().map(|e| format!("预期的故障: {}", e))
            } else {
                Some("服务应该失败但仍然可用".to_string())
            },
        });
        
        // 恢复所有故障
        self.chaos_monkey.recover_all_failures().await;
        
        // 等待恢复
        println!("等待服务恢复");
        
        let recovery_start = Instant::now();
        let mut recovered = false;
        
        while recovery_start.elapsed() < self.recovery_timeout {
            let recovery_result = self.service_client.call_service(|instance| {
                Ok(format!("服务 {}:{} 正常响应", instance.host, instance.port))
            }).await;
            
            if recovery_result.is_ok() {
                recovered = true;
                break;
            }
            
            tokio::time::sleep(Duration::from_secs(1)).await;
        }
        
        assertions.push(Assertion {
            name: "服务是否恢复".to_string(),
            passed: recovered,
            message: if recovered {
                Some(format!("服务在 {:?} 内恢复", recovery_start.elapsed()))
            } else {
                Some(format!("服务在 {:?} 内未恢复", self.recovery_timeout))
            },
        });
        
        // 检查测试是否成功
        let success = assertions.iter().all(|a| a.passed);
        
        Ok(TestResult {
            scenario_name: self.name().to_string(),
            success,
            assertions,
            execution_time: start_time.elapsed(),
            error_message: None,
        })
    }
}

// 负载测试场景
struct LoadTestScenario {
    endpoint: String,
    client: reqwest::Client,
    concurrent_users: u32,
    duration: Duration,
    request_interval: Duration,
    expected_success_rate: f64,
    expected_max_latency: Duration,
}

#[async_trait]
impl TestScenario for LoadTestScenario {
    fn name(&self) -> &str {
        "负载测试"
    }
    
    async fn setup(&self) -> Result<(), Box<dyn std::error::Error>> {
        println!("设置负载测试");
        Ok(())
    }
    
    async fn teardown(&self) -> Result<(), Box<dyn std::error::Error>> {
        println!("清理负载测试");
        Ok(())
    }
    
    async fn run(&self) -> Result<TestResult, Box<dyn std::error::Error>> {
        let start_time = Instant::now();
        
        // 存储响应时间和成功/失败计数
        let success_count = Arc::new(std::sync::atomic::AtomicU64::new(0));
        let failure_count = Arc::new(std::sync::atomic::AtomicU64::new(0));
        let response_times = Arc::new(Mutex::new(Vec::new()));
        
        // 创建用户任务
        let mut user_tasks = Vec::new();
        
        for user_id in 0..self.concurrent_users {
            let client = self.client.clone();
            let endpoint = self.endpoint.clone();
            let request_interval = self.request_interval;
            let test_duration = self.duration;
            let success_count = success_count.clone();
            let failure_count = failure_count.clone();
            let response_times = response_times.clone();
            
            // 启动用户任务
            user_tasks.push(tokio::spawn(async move {
                let user_start_time = Instant::now();
                
                while user_start_time.elapsed() < test_duration {
                    let request_start = Instant::now();
                    
                    // 发送请求
                    match client.get(&endpoint)
                        .header("User-Agent", format!("LoadTester/1.0 (User {})", user_id))
                        .send()
                        .await
                    {
                        Ok(response) => {
                            let response_time = request_start.elapsed();
                            
                            // 记录响应时间
                            {
                                let mut times = response_times.lock().await;
                                times.push(response_time);
                            }
                            
                            if response.status().is_success() {
                                success_count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                            } else {
                                failure_count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                            }
                        },
                        Err(_) => {
                            failure_count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        }
                    }
                    
                    // 等待下一个请求周期
                    tokio::time::sleep(request_interval).await;
                }
            }));
        }
        
        // 等待所有用户任务完成
        join_all(user_tasks).await;
        
        // 计算指标
        let total_success = success_count.load(std::sync::atomic::Ordering::Relaxed);
        let total_failure = failure_count.load(std::sync::atomic::Ordering::Relaxed);
        let total_requests = total_success + total_failure;
        
        let success_rate = if total_requests > 0 {
            total_success as f64 / total_requests as f64
        } else {
            0.0
        };
        
        // 计算响应时间统计
        let times = response_times.lock().await;
        let mut max_response_time = Duration::from_secs(0);
        let mut total_response_time = Duration::from_secs(0);
        
        for time in &*times {
            if *time > max_response_time {
                max_response_time = *time;
            }
            total_response_time += *time;
        }
        
        let avg_response_time = if !times.is_empty() {
            total_response_time / times.len() as u32
        } else {
            Duration::from_secs(0)
        };
        
        // 创建断言
        let mut assertions = Vec::new();
        
        assertions.push(Assertion {
            name: "成功率是否达到预期".to_string(),
            passed: success_rate >= self.expected_success_rate,
            message: Some(format!(
                "成功率: {:.2}% (预期 >= {:.2}%), 成功: {}, 失败: {}, 总请求: {}",
                success_rate * 100.0,
                self.expected_success_rate * 100.0,
                total_success,
                total_failure,
                total_requests
            )),
        });
        
        assertions.push(Assertion {
            name: "最大响应时间是否在预期范围内".to_string(),
            passed: max_response_time <= self.expected_max_latency,
            message: Some(format!(
                "最大响应时间: {:?} (预期 <= {:?}), 平均响应时间: {:?}",
                max_response_time,
                self.expected_max_latency,
                avg_response_time
            )),
        });
        
        // 检查测试是否成功
        let success = assertions.iter().all(|a| a.passed);
        
        Ok(TestResult {
            scenario_name: self.name().to_string(),
            success,
            assertions,
            execution_time: start_time.elapsed(),
            error_message: None,
        })
    }
}

// 使用示例
async fn distributed_testing_example() {
    // 创建测试配置
    let config = TestConfig {
        parallel_execution: true,
        timeout: Duration::from_secs(180),
        retry_count: 2,
        retry_delay: Duration::from_secs(10),
    };
    
    // 创建测试框架
    let mut framework = DistributedTestFramework::new(config);
    
    // 添加服务可用性测试
    let availability_scenario = Arc::new(ServiceAvailabilityScenario {
        service_urls: vec![
            "http://localhost:8081/health".to_string(),
            "http://localhost:8082/health".to_string(),
            "http://localhost:8083/health".to_string(),
        ],
        client: reqwest::Client::new(),
    });
    
    framework.add_scenario(availability_scenario);
    
    // 添加数据一致性测试
    let verifier = Arc::new(ConsistencyVerifier::new(vec![
        "http://localhost:8081".to_string(),
        "http://localhost:8082".to_string(),
        "http://localhost:8083".to_string(),
    ]));
    
    let consistency_scenario = Arc::new(DataConsistencyScenario {
        verifier: verifier.clone(),
        data_ids: vec![
            "item-1".to_string(),
            "item-2".to_string(),
            "item-3".to_string(),
        ],
    });
    
    framework.add_scenario(consistency_scenario);
    
    // 添加负载测试
    let load_scenario = Arc::new(LoadTestScenario {
        endpoint: "http://localhost:8081/api/data".to_string(),
        client: reqwest::Client::new(),
        concurrent_users: 50,
        duration: Duration::from_secs(30),
        request_interval: Duration::from_millis(100),
        expected_success_rate: 0.95,  // 95%
        expected_max_latency: Duration::from_millis(500),
    });
    
    framework.add_scenario(load_scenario);
    
    // 运行测试
    println!("开始运行分布式系统测试...");
    let results = framework.run_all().await;
    
    // 打印结果
    for result in &results {
        println!("\n场景: {}", result.scenario_name);
        println!("结果: {}", if result.success { "通过" } else { "失败" });
        println!("执行时间: {:?}", result.execution_time);
        
        if let Some(error) = &result.error_message {
            println!("错误: {}", error);
        }
        
        println!("断言:");
        for assertion in &result.assertions {
            println!("  {}: {}", 
                    assertion.name, 
                    if assertion.passed { "通过" } else { "失败" });
            
            if let Some(message) = &assertion.message {
                println!("    {}", message);
            }
        }
    }
    
    // 生成报告
    let report = framework.generate_report().await;
    
    println!("\n测试报告:");
    println!("总场景数: {}", report.total_scenarios);
    println!("通过场景数: {}", report.passed_scenarios);
    println!("失败场景数: {}", report.failed_scenarios);
    println!("总执行时间: {:?}", report.total_duration);
    println!("测试时间: {}", report.timestamp);
    
    // 可以将报告保存为JSON
    let report_json = serde_json::to_string_pretty(&report).unwrap();
    std::fs::write("test_report.json", report_json).unwrap();
    println!("测试报告已保存至 test_report.json");
}
```

### 5. 总结与最佳实践

分布式系统开发是一项复杂的任务，需要考虑许多因素。
以下是一些关键的最佳实践：

#### 5.1 系统设计原则

1. **分区容忍性**：
   - 设计系统时假设网络分区会发生
   - 使用一致性算法处理分区（如Paxos、Raft）
   - 实现自动恢复机制

2. **可扩展性**：
   - 采用水平扩展而非垂直扩展
   - 使用分片和分区策略
   - 避免单点瓶颈

3. **弹性**：
   - 实现熔断器模式
   - 添加退避和重试机制
   - 规划容量和资源限制

4. **可观察性**：
   - 实现全面的日志记录
   - 设置关键指标的监控
   - 启用分布式跟踪

#### 5.2 Rust在分布式系统中的优势

1. **安全并发**：
   - 所有权系统防止数据竞争
   - 类型系统和模式匹配帮助处理错误
   - 无运行时开销的抽象

2. **性能**：
   - 接近C/C++的性能
   - 零成本抽象
   - 精确的内存控制

3. **异步编程模型**：
   - `async`/`await`简化异步代码
   - 高效的任务调度
   - 基于Future的组合

#### 5.3 常见陷阱与解决方法

1. **分布式死锁**：
   - 使用超时控制所有远程调用
   - 实现死锁检测
   - 避免环形资源依赖

2. **雪崩效应**：
   - 适当限流
   - 使用断路器保护依赖
   - 实现舱壁模式隔离故障

3. **数据不一致**：
   - 选择合适的一致性模型
   - 实现数据验证机制
   - 提供冲突解决策略

4. **测试难度**：
   - 使用混沌工程方法
   - 开发针对分布式系统的测试框架
   - 模拟各种故障场景

#### 5.4 持续改进

1. **性能基准测试**：
   - 定期运行负载测试
   - 监控关键指标趋势
   - 分析瓶颈并优化

2. **故障分析**：
   - 进行事故回顾
   - 收集和分析故障数据
   - 改进系统设计

3. **知识共享**：
   - 记录架构决策
   - 维护系统模型文档
   - 培训团队成员

在分布式系统开发中，使用Rust的类型安全和内存安全特性，
结合完善的分布式模式，可以构建既可靠又高性能的系统。
本文介绍的各种组件和模式可以作为构建分布式系统的基础，
但每个系统都有其独特的需求和挑战，需要根据具体情况进行调整和优化。

通过遵循这些最佳实践，开发人员可以减少常见问题，
提高系统的可靠性和可维护性，同时充分利用Rust语言的优势。
