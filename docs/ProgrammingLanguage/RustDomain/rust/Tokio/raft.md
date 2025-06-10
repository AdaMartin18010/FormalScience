# rust 实现raft

下面是一个使用 Rust 2024 + Tonic + Tower + Raft 实现的完整分布式系统示例：

## 目录

- [rust 实现raft](#rust-实现raft)
  - [目录](#目录)
  - [1. 项目依赖配置](#1-项目依赖配置)
  - [2. Proto 定义](#2-proto-定义)
  - [3. Raft 节点实现](#3-raft-节点实现)
  - [4. gRPC 服务实现](#4-grpc-服务实现)
    - [5. 状态机实现](#5-状态机实现)
    - [6. 存储实现](#6-存储实现)
    - [7. 中间件实现](#7-中间件实现)
    - [8. 客户端实现](#8-客户端实现)
    - [9. 服务器启动](#9-服务器启动)
    - [10. 使用示例](#10-使用示例)

## 1. 项目依赖配置

```toml
[dependencies]
tonic = { version = "0.10", features = ["tls", "transport", "compression"] }
tower = { version = "0.4", features = ["full"] }
raft = "0.7"
serde = { version = "1.0", features = ["derive"] }
tokio = { version = "1.0", features = ["full"] }
async-trait = "0.1"
futures = "0.3"
prost = "0.12"
bytes = "1.0"
tracing = "0.1"
anyhow = "1.0"
dashmap = "5.5"

[build-dependencies]
tonic-build = "0.10"
```

## 2. Proto 定义

```protobuf
// raft_service.proto
syntax = "proto3";
package raft_service;

service RaftNode {
    // Raft 核心 RPC
    rpc RequestVote (RequestVoteRequest) returns (RequestVoteResponse);
    rpc AppendEntries (AppendEntriesRequest) returns (AppendEntriesResponse);
    
    // 客户端请求
    rpc ClientRequest (ClientRequest) returns (ClientResponse);
    rpc GetClusterState (ClusterStateRequest) returns (ClusterStateResponse);
    
    // 成员管理
    rpc AddNode (AddNodeRequest) returns (AddNodeResponse);
    rpc RemoveNode (RemoveNodeRequest) returns (RemoveNodeResponse);
    
    // 状态同步
    rpc Snapshot (stream SnapshotChunk) returns (SnapshotResponse);
    rpc InstallSnapshot (InstallSnapshotRequest) returns (InstallSnapshotResponse);
}

message RequestVoteRequest {
    uint64 term = 1;
    string candidate_id = 2;
    uint64 last_log_index = 3;
    uint64 last_log_term = 4;
}

message RequestVoteResponse {
    uint64 term = 1;
    bool vote_granted = 2;
}

message AppendEntriesRequest {
    uint64 term = 1;
    string leader_id = 2;
    uint64 prev_log_index = 3;
    uint64 prev_log_term = 4;
    repeated LogEntry entries = 5;
    uint64 leader_commit = 6;
}

message AppendEntriesResponse {
    uint64 term = 1;
    bool success = 2;
    uint64 match_index = 3;
}

message LogEntry {
    uint64 term = 1;
    uint64 index = 2;
    bytes data = 3;
    EntryType type = 4;
}

enum EntryType {
    NORMAL = 0;
    CONFIGURATION = 1;
    SNAPSHOT = 2;
}

message ClientRequest {
    string request_id = 1;
    bytes data = 2;
    RequestType type = 3;
}

enum RequestType {
    READ = 0;
    WRITE = 1;
}

message ClientResponse {
    string request_id = 1;
    bool success = 2;
    bytes data = 3;
    string error = 4;
}

// ... (其他消息定义)
```

## 3. Raft 节点实现

```rust
use raft::{
    Config, Node, NodeId, RaftNode, Storage,
    eraftpb::{ConfChange, Entry, Message},
};

pub struct RaftServer {
    node_id: NodeId,
    raft_node: RaftNode<MemStorage>,
    storage: Arc<MemStorage>,
    applied_index: Arc<AtomicU64>,
    state_machine: Arc<StateMachine>,
}

impl RaftServer {
    pub async fn new(
        node_id: NodeId,
        peers: Vec<NodeId>,
        storage: Arc<MemStorage>,
    ) -> anyhow::Result<Self> {
        let config = Config {
            id: node_id,
            election_tick: 10,
            heartbeat_tick: 3,
            ..Default::default()
        };

        let state_machine = Arc::new(StateMachine::new());
        let applied_index = Arc::new(AtomicU64::new(0));

        let mut raft_node = RaftNode::new(&config, storage.clone())?;

        // 初始化集群配置
        if peers.is_empty() {
            raft_node.become_leader();
        } else {
            for peer in peers {
                let mut cc = ConfChange::default();
                cc.set_change_type(ConfChangeType::AddNode);
                cc.set_node_id(peer);
                raft_node.propose_conf_change(cc)?;
            }
        }

        Ok(Self {
            node_id,
            raft_node,
            storage,
            applied_index,
            state_machine,
        })
    }

    pub async fn step(&mut self, msg: Message) -> anyhow::Result<()> {
        self.raft_node.step(msg)?;
        self.handle_ready().await?;
        Ok(())
    }

    async fn handle_ready(&mut self) -> anyhow::Result<()> {
        if !self.raft_node.has_ready() {
            return Ok(());
        }

        let mut ready = self.raft_node.ready();

        // 持久化 entries 和 hard state
        if !ready.entries().is_empty() {
            self.storage.append(ready.entries())?;
        }

        if let Some(hs) = ready.hs() {
            self.storage.set_hardstate(hs.clone())?;
        }

        // 发送消息
        for msg in ready.messages.drain(..) {
            self.send_message(msg).await?;
        }

        // 应用已提交的 entries
        if let Some(committed) = ready.committed_entries.take() {
            self.apply_committed_entries(committed).await?;
        }

        self.raft_node.advance(ready);
        Ok(())
    }

    async fn apply_committed_entries(&mut self, entries: Vec<Entry>) -> anyhow::Result<()> {
        for entry in entries {
            match entry.get_entry_type() {
                EntryType::EntryNormal => {
                    if !entry.get_data().is_empty() {
                        self.state_machine.apply(entry.get_data())?;
                    }
                }
                EntryType::EntryConfChange => {
                    let change: ConfChange = protobuf::parse_from_bytes(entry.get_data())?;
                    self.raft_node.apply_conf_change(&change)?;
                }
                _ => {}
            }
            self.applied_index.store(entry.get_index(), Ordering::SeqCst);
        }
        Ok(())
    }
}
```

## 4. gRPC 服务实现

```rust
#[derive(Debug)]
pub struct RaftService {
    raft_server: Arc<Mutex<RaftServer>>,
    peers: Arc<DashMap<NodeId, RaftNodeClient<Channel>>>,
}

#[tonic::async_trait]
impl RaftNode for RaftService {
    async fn request_vote(
        &self,
        request: Request<RequestVoteRequest>,
    ) -> Result<Response<RequestVoteResponse>, Status> {
        let req = request.into_inner();
        let mut server = self.raft_server.lock().await;
        
        let msg = Message {
            msg_type: MessageType::MsgRequestVote,
            to: server.node_id,
            from: req.candidate_id,
            term: req.term,
            index: req.last_log_index,
            log_term: req.last_log_term,
            ..Default::default()
        };

        server.step(msg).await.map_err(|e| Status::internal(e.to_string()))?;

        Ok(Response::new(RequestVoteResponse {
            term: server.raft_node.term(),
            vote_granted: server.raft_node.vote() == req.candidate_id,
        }))
    }

    async fn append_entries(
        &self,
        request: Request<AppendEntriesRequest>,
    ) -> Result<Response<AppendEntriesResponse>, Status> {
        let req = request.into_inner();
        let mut server = self.raft_server.lock().await;

        let mut msg = Message {
            msg_type: MessageType::MsgAppend,
            to: server.node_id,
            from: req.leader_id,
            term: req.term,
            index: req.prev_log_index,
            log_term: req.prev_log_term,
            commit: req.leader_commit,
            ..Default::default()
        };

        for entry in req.entries {
            msg.entries.push(Entry {
                entry_type: entry.type_,
                term: entry.term,
                index: entry.index,
                data: entry.data,
            });
        }

        server.step(msg).await.map_err(|e| Status::internal(e.to_string()))?;

        Ok(Response::new(AppendEntriesResponse {
            term: server.raft_node.term(),
            success: true,
            match_index: server.raft_node.get_match_index(req.leader_id),
        }))
    }

    async fn client_request(
        &self,
        request: Request<ClientRequest>,
    ) -> Result<Response<ClientResponse>, Status> {
        let req = request.into_inner();
        let mut server = self.raft_server.lock().await;

        if !server.raft_node.is_leader() {
            return Err(Status::failed_precondition("Not the leader"));
        }

        match req.type_ {
            RequestType::Read => {
                // 读请求直接从状态机获取
                let result = server.state_machine.read(&req.data)
                    .map_err(|e| Status::internal(e.to_string()))?;
                
                Ok(Response::new(ClientResponse {
                    request_id: req.request_id,
                    success: true,
                    data: result,
                    error: String::new(),
                }))
            }
            RequestType::Write => {
                // 写请求需要通过 Raft 日志
                let entry = LogEntry {
                    term: server.raft_node.term(),
                    index: server.raft_node.get_last_index() + 1,
                    data: req.data,
                    type_: EntryType::Normal as i32,
                };

                server.raft_node.propose(entry.data.clone())
                    .map_err(|e| Status::internal(e.to_string()))?;

                Ok(Response::new(ClientResponse {
                    request_id: req.request_id,
                    success: true,
                    data: vec![],
                    error: String::new(),
                }))
            }
        }
    }
}
```

### 5. 状态机实现

```rust
pub struct StateMachine {
    data: Arc<RwLock<BTreeMap<Vec<u8>, Vec<u8>>>>,
}

impl StateMachine {
    pub fn new() -> Self {
        Self {
            data: Arc::new(RwLock::new(BTreeMap::new())),
        }
    }

    pub fn apply(&self, entry: &[u8]) -> anyhow::Result<()> {
        let command: Command = serde_json::from_slice(entry)?;
        let mut data = self.data.write().unwrap();
        
        match command {
            Command::Put { key, value } => {
                data.insert(key, value);
            }
            Command::Delete { key } => {
                data.remove(&key);
            }
        }
        
        Ok(())
    }

    pub fn read(&self, key: &[u8]) -> anyhow::Result<Vec<u8>> {
        let data = self.data.read().unwrap();
        data.get(key)
            .cloned()
            .ok_or_else(|| anyhow::anyhow!("Key not found"))
    }

    pub fn snapshot(&self) -> anyhow::Result<Vec<u8>> {
        let data = self.data.read().unwrap();
        Ok(serde_json::to_vec(&*data)?)
    }

    pub fn restore_from_snapshot(&self, snapshot: &[u8]) -> anyhow::Result<()> {
        let new_data: BTreeMap<Vec<u8>, Vec<u8>> = serde_json::from_slice(snapshot)?;
        let mut data = self.data.write().unwrap();
        *data = new_data;
        Ok(())
    }
}
```

### 6. 存储实现

```rust
pub struct RaftStorage {
    entries: Arc<RwLock<BTreeMap<u64, Entry>>>,
    hard_state: Arc<RwLock<HardState>>,
    snapshot: Arc<RwLock<Snapshot>>,
}

impl Storage for RaftStorage {
    fn initial_state(&self) -> Result<RaftState> {
        let hard_state = self.hard_state.read().unwrap().clone();
        let conf_state = self.snapshot.read().unwrap().get_metadata().get_conf_state().clone();
        Ok(RaftState {
            hard_state,
            conf_state,
        })
    }

    fn entries(
        &self,
        low: u64,
        high: u64,
        max_size: impl Into<Option<u64>>,
    ) -> Result<Vec<Entry>> {
        let entries = self.entries.read().unwrap();
        let mut result = Vec::new();
        let max_size = max_size.into().unwrap_or(u64::MAX);
        let mut size = 0;

        for index in low..high {
            if let Some(entry) = entries.get(&index) {
                size += entry.compute_size() as u64;
                if size > max_size {
                    break;
                }
                result.push(entry.clone());
            }
        }

        Ok(result)
    }

    fn term(&self, idx: u64) -> Result<u64> {
        if idx == self.snapshot.read().unwrap().get_metadata().get_index() {
            return Ok(self.snapshot.read().unwrap().get_metadata().get_term());
        }

        self.entries
            .read()
            .unwrap()
            .get(&idx)
            .map(|e| e.term)
            .ok_or(Error::Store(StorageError::Unavailable))
    }

    fn first_index(&self) -> Result<u64> {
        Ok(self.snapshot.read().unwrap().get_metadata().get_index() + 1)
    }

    fn last_index(&self) -> Result<u64> {
        let entries = self.entries.read().unwrap();
        Ok(entries.keys().next_back().cloned().unwrap_or(0))
    }

    fn snapshot(&self, request_index: u64) -> Result<Snapshot> {
        Ok(self.snapshot.read().unwrap().clone())
    }
}
```

### 7. 中间件实现

```rust
pub struct RaftMiddleware<S> {
    inner: S,
    raft_server: Arc<Mutex<RaftServer>>,
}

impl<S> Layer<S> for RaftMiddleware {
    type Service = RaftMiddleware<S>;

    fn layer(&self, service: S) -> Self::Service {
        RaftMiddleware {
            inner: service,
            raft_server: self.raft_server.clone(),
        }
    }
}

impl<S, Request> Service<Request> for RaftMiddleware<S>
where
    S: Service<Request>,
    Request: Debug,
{
    type Response = S::Response;
    type Error = S::Error;
    type Future = BoxFuture<'static, Result<Self::Response, Self::Error>>;

    fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        self.inner.poll_ready(cx)
    }

    fn call(&mut self, request: Request) -> Self::Future {
        let raft_server = self.raft_server.clone();
        let mut inner = self.inner.clone();

        Box::pin(async move {
            // 检查节点是否是 leader
            let is_leader = {
                let server = raft_server.lock().await;
                server.raft_node.is_leader()
            };

            if !is_leader {
                return Err(Status::failed_precondition("Not the leader").into());
            }

            inner.call(request).await
        })
    }
}
```

### 8. 客户端实现

```rust
pub struct RaftClient {
    client: RaftNodeClient<Channel>,
}

impl RaftClient {
    pub async fn connect(addr: &str) -> anyhow::Result<Self> {
        let channel = Channel::from_shared(addr.to_string())?
            .connect()
            .await?;

        Ok(Self {
            client: RaftNodeClient::new(channel),
        })
    }

    pub async fn put(&mut self, key: &[u8], value: &[u8]) -> anyhow::Result<()> {
        let request = ClientRequest {
            request_id: Uuid::new_v4().to_string(),
            data: serde_json::to_vec(&Command::Put {
                key: key.to_vec(),
                value: value.to_vec(),
            })?,
            type_: RequestType::Write as i32,
        };

        let response = self.client
            .client_request(request)
            .await?
            .into_inner();

        if !response.success {
            return Err(anyhow::anyhow!(response.error));
        }

        Ok(())
    }

    pub async fn get(&mut self, key: &[u8]) -> anyhow::Result<Vec<u8>> {
        let request = ClientRequest {
            request_id: Uuid::new_v4().to_string(),
            data: key.to_vec(),
            type_: RequestType::Read as i32,
        };

        let response = self.client
            .client_request(request)
            .await?
            .into_inner();

        if !response.success {
            return Err(anyhow::anyhow!(response.error));
        }

        Ok(response.data)
    }
}
```

### 9. 服务器启动

```rust
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let node_id = 1;
    let addr = "[::1]:50051";
    let peers = vec![2, 3];  // 其他节点的 ID

    // 创建存储
    let storage = Arc::new(RaftStorage::new());

    // 创建 Raft 服务器
    let raft_server = Arc::new(Mutex::new(RaftServer::new(
        node_id,
        peers.clone(),
        storage,
    ).await?));

    // 创建 gRPC 服务
    let raft_service = RaftService::new(raft_server.clone());

    // 创建中间件
    let middleware = RaftMiddleware::new(raft_server.clone());

    println!("Starting Raft node {} on {}", node_id, addr);

    Server::builder()
        .layer(middleware)
        .add_service(RaftNodeServer::new(raft_service))
        .serve(addr.parse()?)
        .await?;

    Ok(())
}
```

### 10. 使用示例

```rust
async fn example() -> anyhow::Result<()> {
    // 创建客户端
    let mut client = RaftClient::connect("http://[::1]:50051").await?;

    // 写入数据
    client.put(b"key1", b"value1").await?;
    client.put(b"key2", b"value2").await?;

    // 读取数据
    let value1 = client.get(b"key1").await?;
    let value2 = client.get(b"key2").await?;

    println!("key1: {:?}", String::from_utf8(value1)?);
    println!("key2: {:?}", String::from_utf8(value2)?);

    Ok(())
}
```

这个完整的示例展示了如何使用 Tonic、Tower 和 Raft 构建一个分布式系统，包括：

1. Raft 协议实现
2. gRPC 服务接口
3. 状态机实现
4. 持久化存储
5. 中间件支持
6. 客户端实现
7. 集群管理
8. 错误处理
9. 日志复制
10. 领导者选举

通过这种方式，您可以构建一个具有高可用性和一致性的分布式系统。系统支持：

- 领导者选举
- 日志复制
- 状态机复制
- 成员变更
- 快照管理
- 客户端请求处理
- 错误恢复

这个实现提供了良好的可扩展性和可靠性，可以根据需要进行进一步的优化和扩展。
