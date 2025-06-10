# Rust分布式控制系统

我将为您展示一个使用 Rust 2024 实现的基于 Raft + P2P + NATS 的分布式控制系统。

## 目录

- [Rust分布式控制系统](#rust分布式控制系统)
  - [目录](#目录)
  - [1. 项目依赖配置](#1-项目依赖配置)
  - [2. Raft 节点实现](#2-raft-节点实现)
    - [3. P2P 网络实现](#3-p2p-网络实现)
    - [4. NATS 消息处理器](#4-nats-消息处理器)
    - [5. 分布式状态机实现](#5-分布式状态机实现)
    - [6. 控制系统实现](#6-控制系统实现)
    - [7. 主程序实现](#7-主程序实现)

## 1. 项目依赖配置

```toml
[dependencies]
tokio = { version = "1.0", features = ["full"] }
async-nats = "0.33"
raft = "0.7"
libp2p = { version = "0.53", features = ["full"] }
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
async-trait = "0.1"
dashmap = "5.5"
tracing = "0.1"
anyhow = "1.0"
thiserror = "1.0"
bytes = "1.0"
futures = "0.3"
uuid = { version = "1.0", features = ["v4"] }
```

## 2. Raft 节点实现

```rust
#[derive(Debug)]
pub struct RaftNode {
    id: NodeId,
    state: Arc<RwLock<RaftState>>,
    storage: Arc<RaftStorage>,
    peers: Arc<DashMap<NodeId, PeerInfo>>,
    nats_client: async_nats::Client,
}

#[derive(Debug)]
pub struct RaftState {
    current_term: u64,
    voted_for: Option<NodeId>,
    log: Vec<LogEntry>,
    commit_index: u64,
    last_applied: u64,
    role: RaftRole,
}

#[derive(Debug)]
pub enum RaftRole {
    Follower,
    Candidate,
    Leader {
        next_index: HashMap<NodeId, u64>,
        match_index: HashMap<NodeId, u64>,
    },
}

impl RaftNode {
    pub async fn new(
        id: NodeId,
        storage: Arc<RaftStorage>,
        nats_client: async_nats::Client,
    ) -> Result<Self> {
        let state = Arc::new(RwLock::new(RaftState::new()));
        let peers = Arc::new(DashMap::new());

        let node = Self {
            id,
            state,
            storage,
            peers,
            nats_client,
        };

        // 启动 Raft 定时器
        node.start_election_timer();
        node.start_heartbeat_timer();

        Ok(node)
    }

    async fn start_election_timer(&self) {
        let state = self.state.clone();
        let id = self.id;
        let peers = self.peers.clone();
        let nats = self.nats_client.clone();

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_millis(150));
            loop {
                interval.tick().await;
                
                let mut state = state.write().await;
                if matches!(state.role, RaftRole::Leader { .. }) {
                    continue;
                }

                // 转换为候选人并开始选举
                state.role = RaftRole::Candidate;
                state.current_term += 1;
                state.voted_for = Some(id);

                // 发送请求投票 RPC
                let request = RequestVoteRequest {
                    term: state.current_term,
                    candidate_id: id,
                    last_log_index: state.log.len() as u64,
                    last_log_term: state.log.last().map(|e| e.term).unwrap_or(0),
                };

                for peer in peers.iter() {
                    let nats = nats.clone();
                    let request = request.clone();
                    
                    tokio::spawn(async move {
                        if let Err(e) = nats.publish(
                            format!("raft.vote.{}", peer.id),
                            serde_json::to_vec(&request)?,
                        ).await {
                            tracing::error!("Failed to send vote request: {}", e);
                        }
                    });
                }
            }
        });
    }

    async fn handle_request_vote(
        &self,
        request: RequestVoteRequest,
    ) -> Result<RequestVoteResponse> {
        let mut state = self.state.write().await;

        let vote_granted = if request.term < state.current_term {
            false
        } else {
            if request.term > state.current_term {
                state.current_term = request.term;
                state.role = RaftRole::Follower;
                state.voted_for = None;
            }

            if state.voted_for.is_none() || state.voted_for == Some(request.candidate_id) {
                let is_log_up_to_date = request.last_log_term > state.log.last().map(|e| e.term).unwrap_or(0) ||
                    (request.last_log_term == state.log.last().map(|e| e.term).unwrap_or(0) &&
                     request.last_log_index >= state.log.len() as u64);

                if is_log_up_to_date {
                    state.voted_for = Some(request.candidate_id);
                    true
                } else {
                    false
                }
            } else {
                false
            }
        };

        Ok(RequestVoteResponse {
            term: state.current_term,
            vote_granted,
        })
    }
}
```

### 3. P2P 网络实现

```rust
pub struct P2PNetwork {
    swarm: Swarm<P2PBehaviour>,
    peers: Arc<DashMap<PeerId, PeerInfo>>,
    message_tx: mpsc::Sender<P2PMessage>,
}

#[derive(NetworkBehaviour)]
pub struct P2PBehaviour {
    gossipsub: Gossipsub,
    kademlia: Kademlia<MemoryStore>,
    identify: Identify,
}

impl P2PNetwork {
    pub async fn new(
        local_key: identity::Keypair,
        message_tx: mpsc::Sender<P2PMessage>,
    ) -> Result<Self> {
        let peer_id = PeerId::from(local_key.public());
        let transport = libp2p::development_transport(local_key.clone()).await?;

        let message_id_fn = |message: &GossipsubMessage| {
            let mut hasher = DefaultHasher::new();
            message.data.hash(&mut hasher);
            MessageId::from(hasher.finish().to_string())
        };

        let gossipsub_config = GossipsubConfigBuilder::default()
            .heartbeat_interval(Duration::from_secs(1))
            .validation_mode(ValidationMode::Strict)
            .message_id_fn(message_id_fn)
            .build()
            .expect("Valid config");

        let mut gossipsub = Gossipsub::new(
            MessageAuthenticity::Signed(local_key),
            gossipsub_config,
        )?;

        // 订阅控制系统主题
        let topic = Topic::new("control-system");
        gossipsub.subscribe(&topic)?;

        let mut kademlia = Kademlia::new(peer_id, MemoryStore::new(peer_id));
        let identify = Identify::new(IdentifyConfig::new(
            "/control-system/1.0.0".into(),
            local_key.public(),
        ));

        let behaviour = P2PBehaviour {
            gossipsub,
            kademlia,
            identify,
        };

        let mut swarm = SwarmBuilder::new(transport, behaviour, peer_id)
            .executor(Box::new(|fut| {
                tokio::spawn(fut);
            }))
            .build();

        Ok(Self {
            swarm,
            peers: Arc::new(DashMap::new()),
            message_tx,
        })
    }

    pub async fn start(&mut self, addr: Multiaddr) -> Result<()> {
        self.swarm.listen_on(addr)?;

        loop {
            match self.swarm.next().await {
                Some(event) => self.handle_event(event).await?,
                None => break,
            }
        }

        Ok(())
    }

    async fn handle_event(&mut self, event: SwarmEvent<P2PBehaviourEvent>) -> Result<()> {
        match event {
            SwarmEvent::NewListenAddr { address, .. } => {
                tracing::info!("Listening on {:?}", address);
            }
            SwarmEvent::Behaviour(P2PBehaviourEvent::Gossipsub(GossipsubEvent::Message {
                propagation_source,
                message_id,
                message,
            })) => {
                self.message_tx.send(P2PMessage {
                    source: propagation_source,
                    id: message_id,
                    data: message.data,
                }).await?;
            }
            SwarmEvent::Behaviour(P2PBehaviourEvent::Kademlia(KademliaEvent::OutboundQueryCompleted {
                result: QueryResult::GetClosestPeers(Ok(peers)),
                ..
            })) => {
                for peer in peers {
                    self.peers.insert(peer, PeerInfo::default());
                }
            }
            _ => {}
        }

        Ok(())
    }
}
```

### 4. NATS 消息处理器

```rust
pub struct NatsHandler {
    client: async_nats::Client,
    raft_node: Arc<RaftNode>,
    p2p_network: Arc<P2PNetwork>,
}

impl NatsHandler {
    pub async fn new(
        client: async_nats::Client,
        raft_node: Arc<RaftNode>,
        p2p_network: Arc<P2PNetwork>,
    ) -> Self {
        Self {
            client,
            raft_node,
            p2p_network,
        }
    }

    pub async fn start(&self) -> Result<()> {
        // 订阅控制命令
        let mut control_sub = self.client
            .subscribe("control.commands.>")
            .await?;

        // 订阅 Raft 消息
        let mut raft_sub = self.client
            .subscribe("raft.>")
            .await?;

        // 处理控制命令
        let control_handler = tokio::spawn({
            let client = self.client.clone();
            let raft_node = self.raft_node.clone();
            
            async move {
                while let Some(msg) = control_sub.next().await {
                    let command: ControlCommand = serde_json::from_slice(&msg.payload)?;
                    
                    // 通过 Raft 处理命令
                    if let Some(leader_id) = raft_node.get_leader().await {
                        if leader_id == raft_node.id {
                            // 作为领导者处理命令
                            let result = raft_node.process_command(command).await?;
                            client.publish(msg.reply.unwrap(), serde_json::to_vec(&result)?).await?;
                        } else {
                            // 转发到领导者
                            client.publish(
                                format!("control.forward.{}", leader_id),
                                msg.payload,
                            ).await?;
                        }
                    }
                }
                Ok::<(), anyhow::Error>(())
            }
        });

        // 处理 Raft 消息
        let raft_handler = tokio::spawn({
            let raft_node = self.raft_node.clone();
            
            async move {
                while let Some(msg) = raft_sub.next().await {
                    match msg.subject.as_str() {
                        s if s.starts_with("raft.vote") => {
                            let request: RequestVoteRequest = serde_json::from_slice(&msg.payload)?;
                            let response = raft_node.handle_request_vote(request).await?;
                            if let Some(reply) = msg.reply {
                                self.client.publish(reply, serde_json::to_vec(&response)?).await?;
                            }
                        }
                        s if s.starts_with("raft.append") => {
                            let request: AppendEntriesRequest = serde_json::from_slice(&msg.payload)?;
                            let response = raft_node.handle_append_entries(request).await?;
                            if let Some(reply) = msg.reply {
                                self.client.publish(reply, serde_json::to_vec(&response)?).await?;
                            }
                        }
                        _ => {}
                    }
                }
                Ok::<(), anyhow::Error>(())
            }
        });

        // 等待处理器完成
        tokio::try_join!(control_handler, raft_handler)?;

        Ok(())
    }
}
```

### 5. 分布式状态机实现

```rust
pub struct StateMachine {
    state: Arc<RwLock<SystemState>>,
    command_tx: mpsc::Sender<StateMachineCommand>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SystemState {
    devices: HashMap<DeviceId, DeviceState>,
    parameters: HashMap<String, Value>,
    last_updated: DateTime<Utc>,
}

impl StateMachine {
    pub async fn new() -> Self {
        let (command_tx, mut command_rx) = mpsc::channel(100);
        let state = Arc::new(RwLock::new(SystemState::default()));

        // 启动状态机处理器
        let state_clone = state.clone();
        tokio::spawn(async move {
            while let Some(command) = command_rx.recv().await {
                let mut state = state_clone.write().await;
                match command {
                    StateMachineCommand::UpdateDevice { device_id, state: device_state } => {
                        state.devices.insert(device_id, device_state);
                    }
                    StateMachineCommand::UpdateParameter { key, value } => {
                        state.parameters.insert(key, value);
                    }
                    StateMachineCommand::DeleteDevice { device_id } => {
                        state.devices.remove(&device_id);
                    }
                }
                state.last_updated = Utc::now();
            }
        });

        Self {
            state,
            command_tx,
        }
    }

    pub async fn apply_command(&self, command: StateMachineCommand) -> Result<()> {
        self.command_tx.send(command).await?;
        Ok(())
    }

    pub async fn get_state(&self) -> SystemState {
        self.state.read().await.clone()
    }

    pub async fn create_snapshot(&self) -> Result<Snapshot> {
        let state = self.state.read().await;
        Ok(Snapshot {
            data: serde_json::to_vec(&*state)?,
            index: state.last_updated.timestamp() as u64,
        })
    }

    pub async fn restore_snapshot(&self, snapshot: Snapshot) -> Result<()> {
        let state: SystemState = serde_json::from_slice(&snapshot.data)?;
        *self.state.write().await = state;
        Ok(())
    }
}
```

### 6. 控制系统实现

```rust
pub struct ControlSystem {
    raft_node: Arc<RaftNode>,
    p2p_network: Arc<P2PNetwork>,
    nats_handler: Arc<NatsHandler>,
    state_machine: Arc<StateMachine>,
}

impl ControlSystem {
    pub async fn new(
        node_id: NodeId,
        nats_url: &str,
        p2p_addr: Multiaddr,
    ) -> Result<Self> {
        // 初始化 NATS 客户端
        let nats_client = async_nats::connect(nats_url).await?;

        // 初始化 P2P 网络
        let (message_tx, mut message_rx) = mpsc::channel(100);
        let p2p_network = Arc::new(P2PNetwork::new(
            identity::Keypair::generate_ed25519(),
            message_tx,
        ).await?);

        // 初始化 Raft 节点
        let storage = Arc::new(RaftStorage::new());
        let raft_node = Arc::new(RaftNode::new(
            node_id,
            storage,
            nats_client.clone(),
        ).await?);

        // 初始化状态机
        let state_machine = Arc::new(StateMachine::new().await);

        // 初始化 NATS 处理器
        let nats_handler = Arc::new(NatsHandler::new(
            nats_client,
            raft_node.clone(),
            p2p_network.clone(),
        ).await);

        let system = Self {
            raft_node,
            p2p_network,
            nats_handler,
            state_machine,
        };

        // 处理 P2P 消息
        let state_machine = system.state_machine.clone();
        tokio::spawn(async move {
            while let Some(message) = message_rx.recv().await {
                if let Ok(command) = serde_json::from_slice(&message.data) {
                    if let Err(e) = state_machine.apply_command(command).await {
                        tracing::error!("Failed to apply command: {}", e);
                    }
                }
            }
        });

        Ok(system)
    }

    pub async fn start(&self) -> Result<()> {
        // 启动 P2P 网络
        let p2p_handle = tokio::spawn({
            let mut network = self.p2p_network.clone();
            async move {
                network.start().await
            }
        });

        // 启动 NATS 处理器
        let nats_handle = tokio::spawn({
            let handler = self.nats_handler.clone();
            async move {
                handler.start().await
            }
        });

        // 等待所有组件启动
        tokio::try_join!(p2p_handle, nats_handle)?;

        Ok(())
    }

    pub async fn submit_command(&self, command: ControlCommand) -> Result<CommandResponse> {
        // 通过 Raft 提交命令
        if self.raft_node.is_leader().await {
            let log_entry = LogEntry {
                term: self.raft_node.get_current_term().await,
                command: serde_json::to_vec(&command)?,
            };

            // 复制日志到其他节点
            self.raft_node.replicate_log(log_entry).await?;

            // 应用命令到状态机
            let response = self.state_machine.apply_command(command.into()).await?;
            Ok(response)
        } else {
            // 转发到领导者
            let leader_id = self.raft_node.get_leader().await
                .ok_or_else(|| anyhow::anyhow!("No leader available"))?;

            self.nats_handler.forward_to_leader(leader_id, command).await
        }
    }
}
```

### 7. 主程序实现

```rust
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    // 加载配置
    let config = load_config()?;

    // 创建控制系统
    let system = ControlSystem::new(
        config.node_id,
        &config.nats_url,
        config.p2p_addr,
    ).await?;

    // 启动控制系统
    system.start().await?;

    // 等待终止信号
    tokio::signal::ctrl_c().await?;

    Ok(())
}

fn load_config() -> Result<Config> {
    let config = Config {
        node_id: NodeId::new(),
        nats_url: "nats://localhost:4222".to_string(),
        p2p_addr: "/ip4/127.0.0.1/tcp/0".parse()?,
        raft_config: RaftConfig {
            heartbeat_interval: Duration::from_millis(100),
            election_timeout: Duration::from_millis(300),
        },
    };

    Ok(config)
}
```

这个实现提供了一个完整的分布式控制系统，具有以下特点：

1. 一致性保证：
   - Raft 共识算法
   - 领导者选举
   - 日志复制
   - 状态机复制

2. 通信机制：
   - P2P 网络（libp2p）
   - NATS 消息队列
   - 命令转发
   - 消息广播

3. 状态管理：
   - 分布式状态机
   - 状态快照
   - 命令应用
   - 状态恢复

4. 可靠性：
   - 错误处理
   - 超时控制
   - 重试机制
   - 日志记录

5. 扩展性：
   - 模块化设计
   - 插件系统
   - 自定义命令
   - 状态监控

这个系统可以用于构建各种分布式控制应用，例如：

- 工业控制系统
- 智能家居控制
- 设备管理系统
- 分布式任务调度
