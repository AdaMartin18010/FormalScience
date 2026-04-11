# 案例8：分布式数据库系统

## 1. 背景介绍

### 1.1 问题背景

分布式数据库系统是现代云计算基础设施的核心组件，需要在网络分区、节点故障等异常情况下保持一致性和可用性。CAP定理表明，在分区容忍的情况下，必须在一致性和可用性之间做出权衡。

形式化方法可以帮助我们在设计阶段验证分布式数据库协议的正确性，确保在各种故障场景下：

- 事务满足ACID属性
- 副本之间保持一致
- 故障恢复后数据不丢失

### 1.2 挑战与目标

**主要挑战：**

- 网络分区导致的脑裂问题
- 并发事务的冲突检测与解决
- 节点故障时的数据复制和恢复
- 性能与一致性级别的权衡

**验证目标：**

- 证明复制协议的一致性保证
- 验证事务的串行化正确性
- 证明故障恢复的完整性
- 分析不同一致性级别的形式化语义

### 1.3 相关研究

- **Spanner**: TrueTime API与外部一致性
- **CockroachDB**: 基于Raft的分布式事务
- **TiDB**: MySQL兼容的分布式数据库
- **Calm定理**: 一致性、可用性与单调性的关系

---

## 2. 形式化规约

### 2.1 分布式数据库模型

```
DistributedDB = (Nodes, Data, Replication, Transactions, Consistency)
```

其中：

- `Nodes`: 节点集合，每个节点存储数据分片
- `Data`: 数据模型（键值对、文档、关系等）
- `Replication`: 复制策略和配置
- `Transactions`: 事务管理系统
- `Consistency`: 一致性协议

### 2.2 复制状态机模型

```lean4
-- 节点标识
abbrev NodeId := Nat

-- 数据分片
structure Shard where
  id : Nat
  range : Range Key
  primary : NodeId
  replicas : List NodeId

-- 复制组（Raft组）
structure RaftGroup where
  shard_id : Nat
  leader : NodeId
  followers : List NodeId
  log : List LogEntry
  commit_index : Nat

-- 日志条目
structure LogEntry where
  index : Nat
  term : Nat
  command : Command

inductive Command
  | Put (key : Key) (value : Value)
  | Delete (key : Key)
  | Txn (ops : List TxnOp)
```

### 2.3 事务形式化

```lean4
-- 事务操作
inductive TxnOp
  | Read (key : Key) (version : Option Nat)
  | Write (key : Key) (value : Value)
  | Delete (key : Key)

-- 事务状态
inductive TxnState
  | Active        -- 活跃状态
  | Prepared      -- 准备提交（2PC）
  | Committed     -- 已提交
  | Aborted       -- 已回滚

-- 事务结构
structure Transaction where
  id : TxnId
  ops : List TxnOp
  state : TxnState
  snapshot_ts : Timestamp
  commit_ts : Option Timestamp

-- 可串行化图
def SerializationGraph (transactions : List Transaction) : Graph TxnId :=
  let edges := transactions.bind (fun t1 =>
    transactions.filterMap (fun t2 =>
      if t1.id ≠ t2.id ∧ conflicts t1 t2 then
        some (t1.id, t2.id)
      else
        none))
  Graph.mk (transactions.map (·.id)) edges

-- 冲突检测
def conflicts (t1 t2 : Transaction) : Prop :=
  ∃ op1 ∈ t1.ops, ∃ op2 ∈ t2.ops,
    (op1.isWrite ∧ op2.isWrite ∧ op1.key = op2.key) ∨  -- WW冲突
    (op1.isRead ∧ op2.isWrite ∧ op1.key = op2.key) ∨  -- RW冲突
    (op1.isWrite ∧ op2.isRead ∧ op1.key = op2.key)    -- WR冲突
```

### 2.4 一致性级别形式化

```lean4
-- 一致性级别定义
inductive ConsistencyLevel
  | Linearizable    -- 线性一致性（最强）
  | Sequential      -- 顺序一致性
  | Causal          -- 因果一致性
  | Eventual        -- 最终一致性
  | ReadCommitted   -- 读已提交
  | Snapshot        -- 快照隔离

-- 线性一致性：所有操作看起来在全局时间点原子执行
def Linearizable (history : List Operation) : Prop :=
  ∃ (seq : List Operation),
    seq.Perm history ∧
    (∀ op ∈ seq, respectsRealTime op history) ∧
    (∀ key, sequentialConsistency (filterKey key seq))

-- 因果一致性：因果相关的操作按顺序可见
def CausalConsistent (history : List Operation) : Prop :=
  ∀ op1 op2 ∈ history,
    happensBefore op1 op2 →
    ∀ node, visibleAt op1 node → visibleAt op2 node
```

---

## 3. 证明/验证过程

### 3.1 Raft共识正确性证明

```lean4
-- Raft安全属性：已提交的条目不会再改变
theorem raft_safety :
  ∀ (group : RaftGroup) (entry : LogEntry),
    committed group entry →
    ∀ (future_group : RaftGroup),
      reachable group future_group →
      entry ∈ future_group.log := by
  intros group entry h_committed future_group h_reachable
  -- 证明思路：
  -- 1. 条目提交需要大多数节点确认
  -- 2. 选举需要大多数节点投票
  -- 3. 两个"大多数"必有交集
  -- 4. 因此新leader必然包含已提交条目
  sorry

-- Raft活性：在稳定leader下，请求最终会被处理
theorem raft_liveness :
  ∀ (group : RaftGroup) (cmd : Command),
    -- 稳定条件：leader不变且多数节点存活
    stableLeader group →
    majorityAlive group →
    -- 请求最终会被提交
    ∃ (group' : RaftGroup),
      reachable group group' ∧
      ∃ entry ∈ group'.log, entry.command = cmd := by
  -- 证明依赖于超时机制和重试策略
  sorry

-- 选举安全性：每个任期最多一个leader
theorem election_safety :
  ∀ (group : RaftGroup) (t : Nat),
    let leaders := group.nodes.filter (λ n => n.isLeader ∧ n.currentTerm = t)
    leaders.length ≤ 1 := by
  -- 证明基于：
  -- 1. 节点只会为任期更高的候选者投票
  -- 2. 每个节点每任期只投一票
  sorry
```

### 3.2 分布式事务正确性

```lean4
-- 两阶段提交（2PC）协议形式化

inductive CoordinatorState
  | Init
  | Waiting        -- 等待参与者响应
  | Decided (decision : Bool)  -- 已决定提交/回滚

inductive ParticipantState
  | Idle
  | Prepared (vote : Bool)
  | Committed
  | Aborted

-- 2PC安全定理：所有参与者最终达成一致
theorem twopc_consistency :
  ∀ (coord : CoordinatorState) (parts : List ParticipantState),
    -- 如果协调者决定提交
    coord = CoordinatorState.Decided true →
    -- 那么所有参与者都提交（或最终提交）
    ∀ p ∈ parts, p = ParticipantState.Committed ∨
                 reachable p ParticipantState.Committed := by
  -- 证明基于协调者的决定基于所有参与者的Yes投票
  sorry

-- 可串行化定理：调度等价于某个串行调度
theorem serializability :
  ∀ (transactions : List Transaction) (schedule : Schedule),
    strictTwoPhaseLocking schedule →
    acyclic (SerializationGraph transactions) →
    ∃ (serial_schedule : Schedule),
      serial_schedule.isSerial ∧
      viewEquivalent schedule serial_schedule := by
  -- 使用串行化图定理
  sorry
```

### 3.3 故障恢复正确性

```lean4
-- 故障恢复模型
inductive FailureMode
  | Crash          -- 崩溃停止
  | CrashRecovery  -- 崩溃恢复
  | Byzantine      -- 拜占庭故障

-- 恢复点目标（RPO）保证
def RPO (system : DistributedDB) (max_loss : Duration) : Prop :=
  ∀ (failure : FailureEvent),
    system.recoverable failure →
    dataLoss failure ≤ max_loss

-- 恢复时间目标（RTO）保证
def RTO (system : DistributedDB) (max_downtime : Duration) : Prop :=
  ∀ (failure : FailureEvent),
    recoveryTime failure ≤ max_downtime

-- 恢复完整性定理
theorem recovery_integrity :
  ∀ (db : DistributedDB) (node : NodeId),
    -- 前提：副本冗余足够
    replicationFactor db ≥ 3 →
    majorityQuorum db →
    -- 崩溃后恢复的数据完整性
    let recovered = recover db node
    recovered.consistentWithReplicas ∧
    recovered.noDataLoss := by
  -- 证明基于副本同步和日志回放
  sorry
```

---

## 4. 代码实现

### 4.1 Raft共识实现（Rust）

```rust
//! Raft共识协议实现
//! 用于分布式数据库的复制层

use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::{mpsc, oneshot};
use serde::{Serialize, Deserialize};

/// 节点ID
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct NodeId(pub u64);

/// 日志索引
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct LogIndex(pub u64);

/// 任期号
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Term(pub u64);

/// Raft消息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RaftMessage {
    AppendEntries {
        term: Term,
        leader_id: NodeId,
        prev_log_index: LogIndex,
        prev_log_term: Term,
        entries: Vec<LogEntry>,
        leader_commit: LogIndex,
    },
    AppendEntriesResponse {
        term: Term,
        success: bool,
        match_index: LogIndex,
    },
    RequestVote {
        term: Term,
        candidate_id: NodeId,
        last_log_index: LogIndex,
        last_log_term: Term,
    },
    RequestVoteResponse {
        term: Term,
        vote_granted: bool,
    },
}

/// 日志条目
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogEntry {
    pub index: LogIndex,
    pub term: Term,
    pub command: Vec<u8>,
}

/// Raft状态机状态
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RaftState {
    Follower,
    Candidate,
    Leader,
}

/// Raft节点
pub struct RaftNode {
    // 持久状态
    pub id: NodeId,
    pub current_term: Term,
    pub voted_for: Option<NodeId>,
    pub log: Vec<LogEntry>,

    // 易失状态
    pub state: RaftState,
    pub commit_index: LogIndex,
    pub last_applied: LogIndex,

    // 领导者状态（仅在Leader时有效）
    pub next_index: HashMap<NodeId, LogIndex>,
    pub match_index: HashMap<NodeId, LogIndex>,

    // 配置
    pub peers: Vec<NodeId>,

    // 超时管理
    pub election_timeout: Duration,
    pub heartbeat_interval: Duration,
    pub last_heartbeat: Instant,

    // 通信通道
    pub message_tx: mpsc::Sender<RaftMessage>,
    pub message_rx: mpsc::Receiver<RaftMessage>,

    // 应用状态机
    pub apply_tx: mpsc::Sender<LogEntry>,
}

impl RaftNode {
    pub fn new(
        id: NodeId,
        peers: Vec<NodeId>,
        apply_tx: mpsc::Sender<LogEntry>,
    ) -> Self {
        let (message_tx, message_rx) = mpsc::channel(100);

        Self {
            id,
            current_term: Term(0),
            voted_for: None,
            log: vec![],
            state: RaftState::Follower,
            commit_index: LogIndex(0),
            last_applied: LogIndex(0),
            next_index: HashMap::new(),
            match_index: HashMap::new(),
            peers,
            election_timeout: Duration::from_millis(150 + rand::random::<u64>() % 150),
            heartbeat_interval: Duration::from_millis(50),
            last_heartbeat: Instant::now(),
            message_tx,
            message_rx,
            apply_tx,
        }
    }

    /// 处理接收到的消息
    pub async fn handle_message(&mut self, msg: RaftMessage) {
        match msg {
            RaftMessage::AppendEntries { term, leader_id, prev_log_index, prev_log_term, entries, leader_commit } => {
                self.handle_append_entries(term, leader_id, prev_log_index, prev_log_term, entries, leader_commit).await;
            }
            RaftMessage::AppendEntriesResponse { term, success, match_index } => {
                self.handle_append_entries_response(term, success, match_index).await;
            }
            RaftMessage::RequestVote { term, candidate_id, last_log_index, last_log_term } => {
                self.handle_request_vote(term, candidate_id, last_log_index, last_log_term).await;
            }
            RaftMessage::RequestVoteResponse { term, vote_granted } => {
                self.handle_request_vote_response(term, vote_granted).await;
            }
        }
    }

    async fn handle_append_entries(
        &mut self,
        term: Term,
        leader_id: NodeId,
        prev_log_index: LogIndex,
        prev_log_term: Term,
        entries: Vec<LogEntry>,
        leader_commit: LogIndex,
    ) {
        // 1. 如果任期小于当前任期，拒绝
        if term < self.current_term {
            self.send_message(leader_id, RaftMessage::AppendEntriesResponse {
                term: self.current_term,
                success: false,
                match_index: LogIndex(0),
            }).await;
            return;
        }

        // 2. 更新任期，转为Follower
        if term > self.current_term {
            self.current_term = term;
            self.voted_for = None;
            self.state = RaftState::Follower;
        }

        self.last_heartbeat = Instant::now();

        // 3. 检查日志连续性
        if !self.log_contains(prev_log_index, prev_log_term) {
            self.send_message(leader_id, RaftMessage::AppendEntriesResponse {
                term: self.current_term,
                success: false,
                match_index: LogIndex(0),
            }).await;
            return;
        }

        // 4. 添加新条目
        let insert_pos = prev_log_index.0 as usize;
        for (i, entry) in entries.iter().enumerate() {
            let pos = insert_pos + i + 1;
            if pos < self.log.len() {
                if self.log[pos].term != entry.term {
                    // 冲突，删除后续所有条目
                    self.log.truncate(pos);
                    self.log.push(entry.clone());
                }
            } else {
                self.log.push(entry.clone());
            }
        }

        // 5. 更新提交索引
        if leader_commit > self.commit_index {
            let last_new_entry = if entries.is_empty() {
                prev_log_index
            } else {
                entries.last().unwrap().index
            };
            self.commit_index = std::cmp::min(leader_commit, last_new_entry);
            self.apply_committed().await;
        }

        self.send_message(leader_id, RaftMessage::AppendEntriesResponse {
            term: self.current_term,
            success: true,
            match_index: if entries.is_empty() { prev_log_index } else { entries.last().unwrap().index },
        }).await;
    }

    async fn handle_request_vote(
        &mut self,
        term: Term,
        candidate_id: NodeId,
        last_log_index: LogIndex,
        last_log_term: Term,
    ) {
        // 更新任期
        if term > self.current_term {
            self.current_term = term;
            self.voted_for = None;
            self.state = RaftState::Follower;
        }

        let mut vote_granted = false;

        if term == self.current_term {
            if self.voted_for.is_none() || self.voted_for == Some(candidate_id) {
                // 检查候选者日志是否至少一样新
                if self.is_log_up_to_date(last_log_index, last_log_term) {
                    vote_granted = true;
                    self.voted_for = Some(candidate_id);
                    self.last_heartbeat = Instant::now();
                }
            }
        }

        self.send_message(candidate_id, RaftMessage::RequestVoteResponse {
            term: self.current_term,
            vote_granted,
        }).await;
    }

    async fn handle_append_entries_response(&mut self, term: Term, success: bool, match_index: LogIndex) {
        if term < self.current_term {
            return;
        }

        if term > self.current_term {
            self.current_term = term;
            self.voted_for = None;
            self.state = RaftState::Follower;
            return;
        }

        if self.state != RaftState::Leader {
            return;
        }

        // 更新next_index和match_index以跟踪日志复制进度
        // 如果成功，推进next_index; 如果失败，回退next_index进行重试
    }

    async fn handle_request_vote_response(&mut self, term: Term, vote_granted: bool) {
        // 处理投票响应，统计票数
        // 如果获得多数票，成为Leader
    }

    /// 发起选举
    pub async fn start_election(&mut self) {
        self.state = RaftState::Candidate;
        self.current_term = Term(self.current_term.0 + 1);
        self.voted_for = Some(self.id);

        let last_log_index = self.log.last().map(|e| e.index).unwrap_or(LogIndex(0));
        let last_log_term = self.log.last().map(|e| e.term).unwrap_or(Term(0));

        // 向所有peer发送RequestVote
        for peer in &self.peers {
            self.send_message(*peer, RaftMessage::RequestVote {
                term: self.current_term,
                candidate_id: self.id,
                last_log_index,
                last_log_term,
            }).await;
        }
    }

    /// 发送心跳（Leader专用）
    pub async fn send_heartbeat(&mut self) {
        if self.state != RaftState::Leader {
            return;
        }

        for peer in &self.peers {
            let next_idx = self.next_index.get(peer).copied().unwrap_or(LogIndex(1));
            let prev_log_index = LogIndex(next_idx.0.saturating_sub(1));
            let prev_log_term = if prev_log_index.0 > 0 {
                self.log.get(prev_log_index.0 as usize - 1)
                    .map(|e| e.term)
                    .unwrap_or(Term(0))
            } else {
                Term(0)
            };

            // 获取需要发送的条目
            let entries: Vec<LogEntry> = self.log
                .iter()
                .skip((next_idx.0 - 1) as usize)
                .cloned()
                .collect();

            self.send_message(*peer, RaftMessage::AppendEntries {
                term: self.current_term,
                leader_id: self.id,
                prev_log_index,
                prev_log_term,
                entries,
                leader_commit: self.commit_index,
            }).await;
        }
    }

    async fn apply_committed(&mut self) {
        while self.last_applied < self.commit_index {
            self.last_applied = LogIndex(self.last_applied.0 + 1);
            if let Some(entry) = self.log.get(self.last_applied.0 as usize - 1) {
                let _ = self.apply_tx.send(entry.clone()).await;
            }
        }
    }

    fn log_contains(&self, index: LogIndex, term: Term) -> bool {
        if index.0 == 0 {
            return true; // 特殊：索引0表示空日志
        }
        self.log
            .get(index.0 as usize - 1)
            .map(|e| e.term == term)
            .unwrap_or(false)
    }

    fn is_log_up_to_date(&self, last_index: LogIndex, last_term: Term) -> bool {
        let my_last = self.log.last();
        let my_last_term = my_last.map(|e| e.term).unwrap_or(Term(0));
        let my_last_index = my_last.map(|e| e.index).unwrap_or(LogIndex(0));

        last_term > my_last_term ||
        (last_term == my_last_term && last_index >= my_last_index)
    }

    async fn send_message(&self, to: NodeId, msg: RaftMessage) {
        // 实际实现通过网络发送消息
        // 这里简化处理
        let _ = to;
        let _ = msg;
    }
}
```

### 4.2 分布式事务管理器（Rust）

```rust
//! 分布式事务管理器
//! 实现两阶段提交（2PC）协议

use std::collections::{HashMap, HashSet};
use std::time::Duration;
use tokio::sync::{mpsc, oneshot};
use serde::{Serialize, Deserialize};
use uuid::Uuid;

/// 事务ID
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TransactionId(pub Uuid);

impl TransactionId {
    pub fn new() -> Self {
        Self(Uuid::new_v4())
    }
}

/// 事务参与者ID
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ParticipantId(pub u64);

/// 事务操作
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TransactionOp {
    Read { key: String, version: Option<u64> },
    Write { key: String, value: Vec<u8> },
    Delete { key: String },
}

/// 事务状态
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum TransactionState {
    Active,
    Preparing,
    Prepared,
    Committing,
    Committed,
    Aborting,
    Aborted,
}

/// 事务上下文
#[derive(Debug, Clone)]
pub struct TransactionContext {
    pub id: TransactionId,
    pub ops: Vec<TransactionOp>,
    pub state: TransactionState,
    pub participants: HashSet<ParticipantId>,
    pub prepare_responses: HashMap<ParticipantId, bool>,
    pub read_set: HashMap<String, u64>,   // key -> version
    pub write_set: HashMap<String, Vec<u8>>,
}

/// 两阶段提交协调者
pub struct Coordinator {
    pub id: NodeId,
    pub transactions: HashMap<TransactionId, TransactionContext>,
    pub participants: HashMap<ParticipantId, ParticipantHandle>,
    pub tx: mpsc::Sender<CoordinatorMessage>,
    pub rx: mpsc::Receiver<CoordinatorMessage>,
}

/// 参与者句柄
#[derive(Debug, Clone)]
pub struct ParticipantHandle {
    pub id: ParticipantId,
    pub tx: mpsc::Sender<ParticipantMessage>,
}

/// 协调者消息
#[derive(Debug)]
pub enum CoordinatorMessage {
    StartTransaction {
        ops: Vec<TransactionOp>,
        participants: Vec<ParticipantId>,
        respond_to: oneshot::Sender<TransactionId>,
    },
    PrepareResponse {
        txn_id: TransactionId,
        participant: ParticipantId,
        vote: bool,
        reason: Option<String>,
    },
    CommitAck {
        txn_id: TransactionId,
        participant: ParticipantId,
    },
    AbortAck {
        txn_id: TransactionId,
        participant: ParticipantId,
    },
    Timeout(TransactionId),
}

/// 参与者消息
#[derive(Debug)]
pub enum ParticipantMessage {
    Prepare {
        txn_id: TransactionId,
        ops: Vec<TransactionOp>,
        respond_to: oneshot::Sender<PrepareResult>,
    },
    Commit {
        txn_id: TransactionId,
    },
    Abort {
        txn_id: TransactionId,
    },
}

#[derive(Debug)]
pub enum PrepareResult {
    Yes,
    No(String),
}

impl Coordinator {
    pub fn new(id: NodeId) -> Self {
        let (tx, rx) = mpsc::channel(100);
        Self {
            id,
            transactions: HashMap::new(),
            participants: HashMap::new(),
            tx,
            rx,
        }
    }

    /// 开始新事务
    pub async fn begin_transaction(
        &self,
        ops: Vec<TransactionOp>,
        participants: Vec<ParticipantId>,
    ) -> Result<TransactionId, String> {
        let (respond_to, rx) = oneshot::channel();
        self.tx.send(CoordinatorMessage::StartTransaction {
            ops,
            participants: participants.iter().copied().collect(),
            respond_to,
        }).await.map_err(|e| e.to_string())?;

        rx.await.map_err(|e| e.to_string())
    }

    /// 主事件循环
    pub async fn run(&mut self) {
        while let Some(msg) = self.rx.recv().await {
            match msg {
                CoordinatorMessage::StartTransaction { ops, participants, respond_to } => {
                    let txn_id = TransactionId::new();
                    let ctx = TransactionContext {
                        id: txn_id,
                        ops,
                        state: TransactionState::Active,
                        participants: participants.iter().copied().collect(),
                        prepare_responses: HashMap::new(),
                        read_set: HashMap::new(),
                        write_set: HashMap::new(),
                    };
                    self.transactions.insert(txn_id, ctx);
                    let _ = respond_to.send(txn_id);

                    // 进入准备阶段
                    self.prepare_phase(txn_id).await;
                }
                CoordinatorMessage::PrepareResponse { txn_id, participant, vote, reason } => {
                    if let Some(ctx) = self.transactions.get_mut(&txn_id) {
                        ctx.prepare_responses.insert(participant, vote);

                        // 检查是否收到所有响应
                        if ctx.prepare_responses.len() == ctx.participants.len() {
                            let all_yes = ctx.prepare_responses.values().all(|&v| v);
                            if all_yes {
                                self.commit_phase(txn_id).await;
                            } else {
                                log::warn!("Transaction {:?} prepare failed: {:?}", txn_id, reason);
                                self.abort_phase(txn_id).await;
                            }
                        }
                    }
                }
                CoordinatorMessage::CommitAck { txn_id, participant } => {
                    log::info!("Transaction {:?} commit ack from {:?}", txn_id, participant);
                    // 可以在这里清理事务状态
                }
                CoordinatorMessage::AbortAck { txn_id, participant } => {
                    log::info!("Transaction {:?} abort ack from {:?}", txn_id, participant);
                }
                CoordinatorMessage::Timeout(txn_id) => {
                    log::warn!("Transaction {:?} timed out, aborting", txn_id);
                    self.abort_phase(txn_id).await;
                }
            }
        }
    }

    /// 准备阶段
    async fn prepare_phase(&self, txn_id: TransactionId) {
        if let Some(ctx) = self.transactions.get(&txn_id) {
            let ops = ctx.ops.clone();

            for participant_id in &ctx.participants {
                if let Some(handle) = self.participants.get(participant_id) {
                    let (tx, rx) = oneshot::channel();
                    let _ = handle.tx.send(ParticipantMessage::Prepare {
                        txn_id,
                        ops: ops.clone(),
                        respond_to: tx,
                    }).await;

                    // 异步处理参与者响应，根据结果决定提交或回滚事务
                    tokio::spawn(async move {
                        match tokio::time::timeout(Duration::from_secs(5), rx).await {
                            Ok(Ok(PrepareResult::Yes)) => {
                                // 发送PrepareResponse到协调者
                            }
                            Ok(Ok(PrepareResult::No(reason))) => {
                                // 发送否定的PrepareResponse
                            }
                            _ => {
                                // 超时或其他错误
                            }
                        }
                    });
                }
            }
        }
    }

    /// 提交阶段
    async fn commit_phase(&self, txn_id: TransactionId) {
        if let Some(ctx) = self.transactions.get(&txn_id) {
            log::info!("Committing transaction {:?}", txn_id);

            for participant_id in &ctx.participants {
                if let Some(handle) = self.participants.get(participant_id) {
                    let _ = handle.tx.send(ParticipantMessage::Commit { txn_id }).await;
                }
            }
        }
    }

    /// 回滚阶段
    async fn abort_phase(&self, txn_id: TransactionId) {
        if let Some(ctx) = self.transactions.get(&txn_id) {
            log::info!("Aborting transaction {:?}", txn_id);

            for participant_id in &ctx.participants {
                if let Some(handle) = self.participants.get(participant_id) {
                    let _ = handle.tx.send(ParticipantMessage::Abort { txn_id }).await;
                }
            }
        }
    }

    pub fn register_participant(&mut self, id: ParticipantId, tx: mpsc::Sender<ParticipantMessage>) {
        self.participants.insert(id, ParticipantHandle { id, tx });
    }
}
```

---

## 5. 经验总结

### 5.1 关键经验

1. **分层架构**：将共识层、存储层、事务层分离，每层独立验证
2. **日志优先**：所有修改先写入日志，保证可恢复性
3. **多数派原则**：基于Quorum的决策保证容错性

### 5.2 挑战与解决方案

| 挑战 | 解决方案 |
|------|----------|
| 网络分区 | 使用多数派Quorum决策 |
| 性能瓶颈 | 批量处理和流水线优化 |
| 时钟同步 | 使用逻辑时钟或原子钟（Spanner） |
| 存储开销 | 日志压缩和快照机制 |

### 5.3 未来方向

- 新硬件（RDMA、持久内存）的优化
- Serverless数据库的形式化验证
- 跨数据中心复制的强一致性
- 自动化故障注入测试

---

## 参考文献

1. Corbett, J. C., et al. (2013). Spanner: Google's globally distributed database. TOCS.
2. Ongaro, D., & Ousterhout, J. (2014). In search of an understandable consensus algorithm. USENIX ATC.
3. Bernstein, P. A., & Goodman, N. (1981). Concurrency control in distributed database systems. ACM Computing Surveys.
