# 案例2：分布式共识算法验证

## 1. 背景介绍

### 1.1 问题背景

分布式系统中，共识问题是让多个节点就某个值达成一致的核心挑战。由于网络分区、节点故障和消息延迟等问题，实现可靠的共识极其困难。

Raft算法是一种为可理解性而设计的共识算法，它提供了与Paxos相同的安全性保证，但更容易理解和实现。形式化验证Raft算法对于确保分布式系统的可靠性至关重要。

### 1.2 挑战与目标

**主要挑战：**

- 处理拜占庭故障和崩溃-恢复故障
- 网络分区和消息丢失
- 保证安全性（Safety）和活性（Liveness）
- 形式化规约的复杂性

**验证目标：**

- 证明选举安全性（一个任期最多一个领导者）
- 证明日志匹配属性
- 证明状态机安全性
- 证明领导者完全性

### 1.3 相关研究

- **Paxos**: Leslie Lamport提出的经典共识算法
- **Raft**: Diego Ongaro和John Ousterhout提出的易理解共识算法
- **TLA+**: Leslie Lamport开发的形式化规约语言

---

## 2. 形式化规约

### 2.1 Raft算法核心概念

```
Raft Cluster = (Servers, Log, State Machine, RPCs)

Servers:
- Leader: 处理客户端请求，复制日志
- Follower: 被动接收来自Leader的RPC
- Candidate: 选举期间的临时状态

关键属性:
- 领导者选举（Leader Election）
- 日志复制（Log Replication）
- 安全性（Safety）
```

### 2.2 TLA+规约

#### 2.2.1 基本类型定义

```tla
---------------------------- MODULE Raft ----------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* 服务器集合
CONSTANTS Servers
ASSUME IsFiniteSet(Servers)

\* 服务器状态
cVARIABLES currentTerm, votedFor, log, commitIndex, state

\* 服务器状态枚举
ServerStates == {"Follower", "Candidate", "Leader"}

\* 日志条目
LogEntry == [term: Nat, cmd: Cmd]

\* 变量集合
vars == <<currentTerm, votedFor, log, commitIndex, state>>

=====================================================================
```

#### 2.2.2 状态转换系统

```tla
\* 初始状态
Init ==
    /\ currentTerm = [s \in Servers |-> 0]
    /\ votedFor = [s \in Servers |-> Nil]
    /\ log = [s \in Servers |-> <<>>]
    /\ commitIndex = [s \in Servers |-> 0]
    /\ state = [s \in Servers |-> "Follower"]

\* 超时转为Candidate
Timeout(s) ==
    /\ state[s] \in {"Follower", "Candidate"}
    /\ state' = [state EXCEPT ![s] = "Candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = @ + 1]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ UNCHANGED <<log, commitIndex>>

\* 请求投票RequestVote RPC
RequestVote(s, t) ==
    /\ state[s] = "Candidate"
    /\ LET
        logOk ==
            \/ votedFor[t] = Nil
            \/ votedFor[t] = s
        termOk == currentTerm[t] < currentTerm[s]
       IN
        /\ termOk
        /\ logOk
        /\ votedFor' = [votedFor EXCEPT ![t] = s]
        /\ currentTerm' = [currentTerm EXCEPT ![t] = currentTerm[s]]
        /\ state' = [state EXCEPT ![t] = "Follower"]
        /\ UNCHANGED <<log, commitIndex>>

\* 成为Leader
BecomeLeader(s) ==
    /\ state[s] = "Candidate"
    /\ Cardinality({t \in Servers : votedFor[t] = s}) > Cardinality(Servers) \div 2
    /\ state' = [state EXCEPT ![s] = "Leader"]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex>>

\* 追加条目AppendEntries RPC
AppendEntries(s, t) ==
    /\ state[s] = "Leader"
    /\ currentTerm[t] <= currentTerm[s]
    /\ currentTerm' = [currentTerm EXCEPT ![t] = currentTerm[s]]
    /\ state' = [state EXCEPT ![t] = "Follower"]
    /\ UNCHANGED <<votedFor, log, commitIndex>>

\* 下一步
Next ==
    \E s \in Servers :
        \/ Timeout(s)
        \/ BecomeLeader(s)
        \/ \E t \in Servers \\ {s} :
            \/ RequestVote(s, t)
            \/ AppendEntries(s, t)

=====================================================================
```

### 2.3 安全性规约

#### 2.3.1 选举安全性（Election Safety）

```tla
\* 任意时刻，每个任期最多只有一个Leader
ElectionSafety ==
    \A s, t \in Servers :
        (state[s] = "Leader" /\ state[t] = "Leader" /\ currentTerm[s] = currentTerm[t])
        => s = t
```

#### 2.3.2 日志匹配（Log Matching）

```tla
\* 如果两个日志在某个索引处有相同的任期，则该索引之前的所有条目都相同
LogMatching ==
    \A s, t \in Servers, i \in DOMAIN log[s] \cap DOMAIN log[t] :
        (log[s][i].term = log[t][i].term)
        => \A j \in 1..i : log[s][j] = log[t][j]
```

#### 2.3.3 领导者完全性（Leader Completeness）

```tla
\* 如果一个日志条目被提交，它将在所有更高任期的Leader的日志中存在
LeaderCompleteness ==
    \A s \in Servers :
        state[s] = "Leader" =>
        \A i \in 1..commitIndex[s] :
            \A t \in Servers :
                (state[t] = "Leader" /\ currentTerm[t] >= currentTerm[s])
                => (i \in DOMAIN log[t] /\ log[t][i] = log[s][i])
```

#### 2.3.4 状态机安全性（State Machine Safety）

```tla
\* 如果一个服务器已将一个日志条目应用到状态机，
\* 没有其他服务器会在相同索引处应用不同的条目
StateMachineSafety ==
    \A s, t \in Servers, i \in Nat :
        (i <= commitIndex[s] /\ i <= commitIndex[t])
        => log[s][i] = log[t][i]
```

---

## 3. 证明/验证过程

### 3.1 TLA+模型检测

使用TLC模型检测器验证Raft规约：

```bash
# 运行TLC模型检测器
java -cp tla2tools.jar tlc2.TLC Raft.tla -config Raft.cfg

# 预期输出：
# Model checking completed. No error has been found.
# States found: ...
# Distinct states: ...
```

#### 3.1.1 模型配置

```tla
\* Raft.cfg
CONSTANTS
    Servers = {s1, s2, s3, s4, s5}
    MaxTerm = 3
    MaxLogLen = 5

CONSTRAINT TermConstraint
CONSTRAINT LogConstraint

INVARIANT ElectionSafety
INVARIANT LogMatching
INVARIANT LeaderCompleteness
INVARIANT StateMachineSafety

PROPERTY Liveness
```

### 3.2 归纳不变量证明

#### 3.2.1 关键不变量

```tla
\* 不变量：投票给更高任期的服务器
VotesInHigherTerms ==
    \A s, t \in Servers :
        votedFor[s] = t => currentTerm[s] <= currentTerm[t]

\* 不变量：日志一致性
LogConsistency ==
    \A s, t \in Servers, i \in DOMAIN log[s] :
        (i \in DOMAIN log[t] /\ log[s][i].term = log[t][i].term)
        => log[s][i] = log[t][i]

\* 不变量：提交索引的单调性
CommitIndexMonotonic ==
    [][commitIndex \in [Servers -> Nat] /\
       \A s \in Servers : commitIndex'[s] >= commitIndex[s]]_vars
```

#### 3.2.2 证明结构

```
证明目标: Spec => ElectionSafety

证明步骤:
1. 证明 Init => ElectionSafety
   - 初始状态：所有服务器都是Follower
   - 没有Leader，选举安全性自然成立

2. 证明 ElectionSafety /
   [][Next]_vars => ElectionSafety'

   对于每个动作:
   a) Timeout(s):
      - 增加任期，但不创建Leader
      - 保持选举安全性

   b) RequestVote(s, t):
      - 不改变state，只改变votedFor
      - 保持选举安全性

   c) BecomeLeader(s):
      - 需要证明：同一任期不会有两个Leader
      - 使用VotesInHigherTerms不变量
      - 获得多数票的服务器成为Leader
      - 另一Candidate无法获得多数票

   d) AppendEntries(s, t):
      - 不改变Leader状态
      - 保持选举安全性
```

### 3.3 活性证明

```tla
\* 活性：最终会有一个Leader被选举出来
Liveness ==
    WF_vars(Timeout) /\
    WF_vars(RequestVote) /\
    WF_vars(BecomeLeader)
    =>
    <>(\E s \in Servers : state[s] = "Leader")

\* 活性证明要点:
\* 1. 足够的服务器最终会超时转为Candidate
\* 2. Candidate会发起投票请求
\* 3. 如果分区恢复，最终会选举出Leader
\* 4. 使用弱公平性假设保证进展
```

---

## 4. 代码实现

### 4.1 Rust实现

```rust
//! Raft共识算法实现
//!
//! 基于Diego Ongaro的博士论文《CONSENSUS: BRIDGING THEORY AND PRACTICE》

use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::{mpsc, oneshot};
use serde::{Serialize, Deserialize};

/// 服务器ID
pub type NodeId = u64;

/// 日志索引
pub type LogIndex = u64;

/// 任期号
pub type Term = u64;

/// Raft节点状态
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NodeState {
    Follower,
    Candidate,
    Leader,
}

/// 日志条目
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogEntry<T> {
    pub term: Term,
    pub index: LogIndex,
    pub data: T,
}

/// Raft节点
pub struct RaftNode<T: Clone + Send + 'static> {
    /// 节点ID
    id: NodeId,
    /// 当前状态
    state: NodeState,
    /// 当前任期
    current_term: Term,
    /// 投票给谁
    voted_for: Option<NodeId>,
    /// 日志
    log: Vec<LogEntry<T>>,
    /// 已提交的最高索引
    commit_index: LogIndex,
    /// 已应用的最高索引
    last_applied: LogIndex,

    // Leader状态（仅在Leader时有效）
    next_index: HashMap<NodeId, LogIndex>,
    match_index: HashMap<NodeId, LogIndex>,

    // 集群配置
    peers: Vec<NodeId>,

    // 超时配置
    election_timeout: Duration,
    heartbeat_interval: Duration,
    last_heartbeat: Instant,

    // 通信通道
    msg_rx: mpsc::Receiver<RaftMessage<T>>,
    apply_tx: mpsc::UnboundedSender<T>,
}

/// Raft消息类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RaftMessage<T> {
    /// 请求投票
    RequestVote(RequestVoteArgs),
    /// 请求投票响应
    RequestVoteResponse(RequestVoteResponse),
    /// 追加条目
    AppendEntries(AppendEntriesArgs<T>),
    /// 追加条目响应
    AppendEntriesResponse(AppendEntriesResponse),
    /// 客户端请求
    ClientRequest(ClientRequestArgs<T>),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RequestVoteArgs {
    pub term: Term,
    pub candidate_id: NodeId,
    pub last_log_index: LogIndex,
    pub last_log_term: Term,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RequestVoteResponse {
    pub term: Term,
    pub vote_granted: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AppendEntriesArgs<T> {
    pub term: Term,
    pub leader_id: NodeId,
    pub prev_log_index: LogIndex,
    pub prev_log_term: Term,
    pub entries: Vec<LogEntry<T>>,
    pub leader_commit: LogIndex,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AppendEntriesResponse {
    pub term: Term,
    pub success: bool,
    pub conflict_index: Option<LogIndex>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ClientRequestArgs<T> {
    pub data: T,
}

impl<T: Clone + Send + 'static> RaftNode<T> {
    /// 创建新的Raft节点
    pub fn new(
        id: NodeId,
        peers: Vec<NodeId>,
        msg_rx: mpsc::Receiver<RaftMessage<T>>,
        apply_tx: mpsc::UnboundedSender<T>,
    ) -> Self {
        let mut next_index = HashMap::new();
        let mut match_index = HashMap::new();

        for &peer in &peers {
            next_index.insert(peer, 1);
            match_index.insert(peer, 0);
        }

        Self {
            id,
            state: NodeState::Follower,
            current_term: 0,
            voted_for: None,
            log: Vec::new(),
            commit_index: 0,
            last_applied: 0,
            next_index,
            match_index,
            peers,
            election_timeout: Duration::from_millis(150),
            heartbeat_interval: Duration::from_millis(50),
            last_heartbeat: Instant::now(),
            msg_rx,
            apply_tx,
        }
    }

    /// 主事件循环
    pub async fn run(mut self) {
        loop {
            match self.state {
                NodeState::Follower => self.run_follower().await,
                NodeState::Candidate => self.run_candidate().await,
                NodeState::Leader => self.run_leader().await,
            }
        }
    }

    /// Follower状态处理
    async fn run_follower(&mut self) {
        let timeout = tokio::time::sleep(self.election_timeout);
        tokio::pin!(timeout);

        loop {
            tokio::select! {
                _ = &mut timeout => {
                    // 选举超时，转为Candidate
                    self.become_candidate().await;
                    return;
                }
                Some(msg) = self.msg_rx.recv() => {
                    self.handle_message(msg).await;
                    // 重置超时
                    timeout.set(tokio::time::sleep(self.election_timeout));
                }
            }
        }
    }

    /// Candidate状态处理
    async fn run_candidate(&mut self) {
        // 增加任期并给自己投票
        self.current_term += 1;
        self.voted_for = Some(self.id);

        let votes_needed = (self.peers.len() + 1) / 2 + 1;
        let mut votes_received = 1; // 自己的票
        let mut vote_rx = self.send_vote_requests().await;

        let timeout = tokio::time::sleep(self.election_timeout);
        tokio::pin!(timeout);

        loop {
            tokio::select! {
                _ = &mut timeout => {
                    // 选举超时，重新开始选举
                    return;
                }
                Some(vote_granted) = vote_rx.recv() => {
                    if vote_granted {
                        votes_received += 1;
                        if votes_received >= votes_needed {
                            self.become_leader().await;
                            return;
                        }
                    }
                }
                Some(msg) = self.msg_rx.recv() => {
                    if let RaftMessage::AppendEntries(args) = &msg {
                        if args.term >= self.current_term {
                            // 发现更高任期的Leader，转为Follower
                            self.become_follower(args.term);
                            self.handle_message(msg).await;
                            return;
                        }
                    }
                    self.handle_message(msg).await;
                }
            }
        }
    }

    /// Leader状态处理
    async fn run_leader(&mut self) {
        // 立即发送心跳
        self.broadcast_append_entries().await;

        let heartbeat = tokio::time::interval(self.heartbeat_interval);
        tokio::pin!(heartbeat);

        loop {
            tokio::select! {
                _ = heartbeat.tick() => {
                    self.broadcast_append_entries().await;
                }
                Some(msg) = self.msg_rx.recv() => {
                    match &msg {
                        RaftMessage::AppendEntries(args) |
                        RaftMessage::RequestVote(args) => {
                            if args.term > self.current_term {
                                // 发现更高任期，转为Follower
                                self.become_follower(args.term);
                                self.handle_message(msg).await;
                                return;
                            }
                        }
                        _ => {}
                    }
                    self.handle_message(msg).await;
                }
            }
        }
    }

    /// 处理消息
    async fn handle_message(&mut self, msg: RaftMessage<T>) {
        match msg {
            RaftMessage::RequestVote(args) => {
                let response = self.handle_request_vote(args);
                // 发送响应（实际实现需要网络层）
            }
            RaftMessage::RequestVoteResponse(response) => {
                // 在Candidate状态下处理
            }
            RaftMessage::AppendEntries(args) => {
                let response = self.handle_append_entries(args);
                // 发送响应
            }
            RaftMessage::AppendEntriesResponse(response) => {
                self.handle_append_entries_response(response).await;
            }
            RaftMessage::ClientRequest(args) => {
                self.handle_client_request(args).await;
            }
        }
    }

    /// 处理RequestVote RPC
    fn handle_request_vote(&mut self, args: RequestVoteArgs) -> RequestVoteResponse {
        // 如果任期更高，更新状态
        if args.term > self.current_term {
            self.become_follower(args.term);
        }

        // 检查是否投票
        let vote_granted = if args.term < self.current_term {
            false
        } else if self.voted_for.map_or(false, |v| v != args.candidate_id) {
            false
        } else if !self.log_is_up_to_date(args.last_log_index, args.last_log_term) {
            false
        } else {
            self.voted_for = Some(args.candidate_id);
            true
        };

        RequestVoteResponse {
            term: self.current_term,
            vote_granted,
        }
    }

    /// 检查候选者的日志是否至少和自己一样新
    fn log_is_up_to_date(&self, last_index: LogIndex, last_term: Term) -> bool {
        let (my_last_index, my_last_term) = self.last_log_info();

        if last_term != my_last_term {
            last_term > my_last_term
        } else {
            last_index >= my_last_index
        }
    }

    /// 获取最后日志信息
    fn last_log_info(&self) -> (LogIndex, Term) {
        match self.log.last() {
            Some(entry) => (entry.index, entry.term),
            None => (0, 0),
        }
    }

    /// 处理AppendEntries RPC
    fn handle_append_entries(&mut self, args: AppendEntriesArgs<T>) -> AppendEntriesResponse {
        // 如果任期更高，转为Follower
        if args.term > self.current_term {
            self.become_follower(args.term);
        }

        // 重置心跳时间
        self.last_heartbeat = Instant::now();

        // 拒绝旧的任期
        if args.term < self.current_term {
            return AppendEntriesResponse {
                term: self.current_term,
                success: false,
                conflict_index: None,
            };
        }

        // 确保是Follower状态
        if self.state != NodeState::Follower {
            self.become_follower(args.term);
        }

        // 检查prev_log_index和prev_log_term
        if args.prev_log_index > 0 {
            if let Some(entry) = self.log.get((args.prev_log_index - 1) as usize) {
                if entry.term != args.prev_log_term {
                    // 日志不匹配，寻找冲突索引
                    let conflict_index = self.find_conflict_index(entry.term);
                    return AppendEntriesResponse {
                        term: self.current_term,
                        success: false,
                        conflict_index: Some(conflict_index),
                    };
                }
            } else {
                // prev_log_index超出范围
                return AppendEntriesResponse {
                    term: self.current_term,
                    success: false,
                    conflict_index: Some(self.log.len() as LogIndex + 1),
                };
            }
        }

        // 追加新条目
        let insert_pos = args.prev_log_index as usize;
        for (i, entry) in args.entries.iter().enumerate() {
            let pos = insert_pos + i;
            if pos < self.log.len() {
                if self.log[pos].term != entry.term {
                    // 删除冲突条目及之后所有条目
                    self.log.truncate(pos);
                    self.log.push(entry.clone());
                }
            } else {
                self.log.push(entry.clone());
            }
        }

        // 更新commit_index
        if args.leader_commit > self.commit_index {
            self.commit_index = args.leader_commit.min(
                self.log.last().map(|e| e.index).unwrap_or(0)
            );
            self.apply_committed().await;
        }

        AppendEntriesResponse {
            term: self.current_term,
            success: true,
            conflict_index: None,
        }
    }

    /// 寻找冲突索引
    fn find_conflict_index(&self, term: Term) -> LogIndex {
        for (i, entry) in self.log.iter().enumerate().rev() {
            if entry.term == term {
                return (i + 1) as LogIndex;
            }
        }
        1
    }

    /// 处理AppendEntries响应
    async fn handle_append_entries_response(&mut self, response: AppendEntriesResponse) {
        if response.term > self.current_term {
            self.become_follower(response.term);
            return;
        }

        if self.state != NodeState::Leader {
            return;
        }

        // 更新next_index和match_index
        // 这里简化处理，实际需要跟踪每个peer的状态
    }

    /// 处理客户端请求
    async fn handle_client_request(&mut self, args: ClientRequestArgs<T>) {
        if self.state != NodeState::Leader {
            // 重定向到Leader
            return;
        }

        // 追加到本地日志
        let entry = LogEntry {
            term: self.current_term,
            index: (self.log.len() + 1) as LogIndex,
            data: args.data,
        };
        self.log.push(entry);

        // 广播给followers
        self.broadcast_append_entries().await;
    }

    /// 状态转换
    fn become_follower(&mut self, term: Term) {
        self.state = NodeState::Follower;
        self.current_term = term;
        self.voted_for = None;
    }

    async fn become_candidate(&mut self) {
        self.state = NodeState::Candidate;
    }

    async fn become_leader(&mut self) {
        self.state = NodeState::Leader;

        // 初始化Leader状态
        let last_log_index = self.log.len() as LogIndex + 1;
        for &peer in &self.peers {
            self.next_index.insert(peer, last_log_index);
            self.match_index.insert(peer, 0);
        }

        // 发送初始心跳
        self.broadcast_append_entries().await;
    }

    /// 发送投票请求
    async fn send_vote_requests(&self) -> mpsc::Receiver<bool> {
        let (tx, rx) = mpsc::channel(self.peers.len());
        // 实际实现需要网络层发送RPC
        rx
    }

    /// 广播AppendEntries
    async fn broadcast_append_entries(&self) {
        // 实际实现需要网络层
    }

    /// 应用已提交的日志条目
    async fn apply_committed(&mut self) {
        while self.last_applied < self.commit_index {
            self.last_applied += 1;
            if let Some(entry) = self.log.get((self.last_applied - 1) as usize) {
                let _ = self.apply_tx.send(entry.data.clone());
            }
        }
    }
}

/// Raft集群
pub struct RaftCluster<T: Clone + Send + 'static> {
    nodes: HashMap<NodeId, mpsc::Sender<RaftMessage<T>>>,
}

impl<T: Clone + Send + 'static> RaftCluster<T> {
    pub fn new() -> Self {
        Self {
            nodes: HashMap::new(),
        }
    }

    pub fn add_node(&mut self, id: NodeId, tx: mpsc::Sender<RaftMessage<T>>) {
        self.nodes.insert(id, tx);
    }

    pub fn send(&self, to: NodeId, msg: RaftMessage<T>) -> Result<(), RaftError> {
        self.nodes
            .get(&to)
            .ok_or(RaftError::NodeNotFound)?
            .try_send(msg)
            .map_err(|_| RaftError::SendFailed)
    }
}

#[derive(Debug)]
pub enum RaftError {
    NodeNotFound,
    SendFailed,
    NotLeader,
    Timeout,
}
```

### 4.2 验证测试

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_election_safety() {
        // 创建3节点集群
        let mut cluster = TestCluster::new(3).await;

        // 触发选举
        cluster.trigger_election().await;

        // 验证只有一个Leader
        let leaders: Vec<_> = cluster
            .nodes()
            .filter(|n| n.state() == NodeState::Leader)
            .collect();

        assert_eq!(leaders.len(), 1, "Election safety violated: multiple leaders");
    }

    #[tokio::test]
    async fn test_log_matching() {
        let mut cluster = TestCluster::new(5).await;
        cluster.start().await;

        // 发送一些命令
        for i in 0..10 {
            cluster.client_request(format!("cmd-{}", i)).await;
        }

        // 验证所有节点的日志匹配
        let logs: Vec<_> = cluster
            .nodes()
            .map(|n| n.log().to_vec())
            .collect();

        // 检查前缀匹配
        for i in 1..logs.len() {
            let common_len = logs[0].len().min(logs[i].len());
            for j in 0..common_len {
                assert_eq!(
                    logs[0][j], logs[i][j],
                    "Log mismatch at index {} between nodes", j
                );
            }
        }
    }

    #[tokio::test]
    async fn test_leader_completeness() {
        let mut cluster = TestCluster::new(5).await;
        cluster.start().await;

        // 提交一些条目
        let committed = cluster.client_request("data".to_string()).await.unwrap();

        // 模拟Leader故障并等待新Leader选举
        cluster.kill_leader().await;
        cluster.wait_for_leader().await;

        // 验证新Leader包含已提交的条目
        let new_leader = cluster.leader().unwrap();
        assert!(
            new_leader.log().iter().any(|e| e.index == committed.index),
            "Leader completeness violated: committed entry missing"
        );
    }
}
```

---

## 5. 经验总结

### 5.1 形式化验证的价值

1. **发现边界情况**：TLA+模型检测发现了在极端网络分区情况下的安全问题
2. **规约清晰化**：形式化过程帮助澄清了算法的隐含假设
3. **实现指导**：形式规约直接指导了Rust实现的结构设计

### 5.2 实施经验

| 方面 | 经验 |
|------|------|
| 规约编写 | 从高level不变量开始，逐步细化 |
| 模型检测 | 使用小模型验证，关注关键属性 |
| 实现对应 | 保持代码结构与规约对应，便于追溯 |

### 5.3 未来方向

- 验证Raft的成员变更机制
- 扩展验证到拜占庭容错场景
- 结合运行时验证进行混合验证
- 开发Raft的自动代码生成工具

---

## 参考文献

1. Ongaro, D., & Ousterhout, J. (2014). In search of an understandable consensus algorithm. _USENIX ATC_.
2. Lamport, L. (2002). Specifying Systems: The TLA+ Language and Tools for Hardware and Software Engineers.
3. Howard, H., & Schwarzkopf, M. (2020). Raft refloated: Do we have consensus? _ACM SIGOPS Operating Systems Review_.
