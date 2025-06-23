# Petri网理论 (Petri Net Theory)

## 1. Petri网基础

### 1.1 Petri网定义

**定义 1.1 (Petri网)**
Petri网是一个四元组 $N = (P, T, F, M_0)$，其中：

- $P$ 是有限的位置集合（places）
- $T$ 是有限的变迁集合（transitions）
- $F \subseteq (P \times T) \cup (T \times P)$ 是流关系（flow relation）
- $M_0 : P \rightarrow \mathbb{N}$ 是初始标识（initial marking）

**定义 1.2 (标识)**
标识 $M : P \rightarrow \mathbb{N}$ 表示每个位置中的托肯（token）数量。

**定义 1.3 (前集和后集)**
对于 $x \in P \cup T$：

- $^\bullet x = \{y \mid (y, x) \in F\}$ 是 $x$ 的前集
- $x^\bullet = \{y \mid (x, y) \in F\}$ 是 $x$ 的后集

### 1.2 变迁规则

**定义 1.4 (变迁使能)**
变迁 $t \in T$ 在标识 $M$ 下使能，记作 $M[t\rangle$，当且仅当：
$$\forall p \in ^\bullet t : M(p) \geq F(p, t)$$

**定义 1.5 (变迁发生)**
如果 $M[t\rangle$，则变迁 $t$ 可以发生，产生新标识 $M'$，记作 $M[t\rangle M'$，其中：
$$M'(p) = M(p) - F(p, t) + F(t, p)$$

**定理 1.1 (变迁发生保持托肯守恒)**
对于任何变迁 $t$ 和标识 $M$，如果 $M[t\rangle M'$，则：
$$\sum_{p \in P} M'(p) = \sum_{p \in P} M(p)$$

**证明：** 通过流关系的定义：
$$\sum_{p \in P} M'(p) = \sum_{p \in P} (M(p) - F(p, t) + F(t, p)) = \sum_{p \in P} M(p)$$

## 2. 可达性分析

### 2.1 可达性关系

**定义 2.1 (可达性)**
标识 $M'$ 从标识 $M$ 可达，记作 $M \rightarrow^* M'$，如果存在变迁序列 $\sigma = t_1 t_2 \cdots t_n$ 使得：
$$M[t_1\rangle M_1[t_2\rangle M_2 \cdots [t_n\rangle M'$$

**定义 2.2 (可达集)**
从标识 $M$ 可达的所有标识集合：
$$R(M) = \{M' \mid M \rightarrow^* M'\}$$

**定理 2.1 (可达性保持)**
如果 $M \rightarrow^* M'$ 且 $M'[t\rangle M''$，则 $M \rightarrow^* M''$。

**证明：** 通过可达性的传递性：

1. $M \rightarrow^* M'$ 存在变迁序列 $\sigma$
2. $M'[t\rangle M''$ 表示 $t$ 在 $M'$ 下使能
3. 因此 $M \rightarrow^* M''$ 通过序列 $\sigma t$

### 2.2 状态空间分析

**定义 2.3 (状态空间)**
Petri网的状态空间是图 $G = (V, E)$，其中：

- $V = R(M_0)$ 是可达标识集合
- $E = \{(M, M') \mid \exists t : M[t\rangle M'\}$ 是变迁关系

-**算法 2.1 (可达性分析)**

```haskell
reachabilityAnalysis :: PetriNet -> [Marking]
reachabilityAnalysis net = 
  let initial = initialMarking net
      reachable = bfs initial [initial]
  in reachable
  where
    bfs :: Marking -> [Marking] -> [Marking]
    bfs current visited = 
      let enabled = enabledTransitions net current
          newMarkings = [fireTransition net current t | t <- enabled]
          unvisited = filter (`notElem` visited) newMarkings
      in if null unvisited 
         then visited
         else bfs (head unvisited) (visited ++ unvisited)
```

## 3. 并发性分析

### 3.1 并发变迁

**定义 3.1 (并发变迁)**
两个变迁 $t_1, t_2 \in T$ 在标识 $M$ 下并发，记作 $M[t_1, t_2\rangle$，当且仅当：

1. $M[t_1\rangle$ 且 $M[t_2\rangle$
2. $^\bullet t_1 \cap ^\bullet t_2 = \emptyset$（无共享输入位置）

**定理 3.1 (并发交换性)**
如果 $M[t_1, t_2\rangle$，则 $M[t_1\rangle M_1[t_2\rangle M'$ 且 $M[t_2\rangle M_2[t_1\rangle M'$，其中 $M_1 \neq M_2$ 但 $M'$ 相同。

**证明：** 通过并发变迁的定义：

1. 无共享输入位置确保独立性
2. 变迁发生顺序不影响最终结果
3. 中间标识可能不同但最终标识相同

### 3.2 冲突分析

**定义 3.2 (冲突)**
两个变迁 $t_1, t_2 \in T$ 在标识 $M$ 下冲突，当且仅当：

1. $M[t_1\rangle$ 且 $M[t_2\rangle$
2. $^\bullet t_1 \cap ^\bullet t_2 \neq \emptyset$（有共享输入位置）

**定理 3.2 (冲突解决)**
如果 $t_1, t_2$ 在 $M$ 下冲突，则最多只能发生其中一个变迁。

**证明：** 通过冲突定义：

1. 共享输入位置限制托肯数量
2. 一个变迁的发生会消耗共享托肯
3. 另一个变迁将不再使能

## 4. 结构性质

### 4.1 有界性

**定义 4.1 (有界性)**
位置 $p \in P$ 是 $k$-有界的，如果对于所有可达标识 $M \in R(M_0)$，都有 $M(p) \leq k$。

**定义 4.2 (安全Petri网)**
Petri网是安全的，如果所有位置都是1-有界的。

**定理 4.1 (有界性判定)**
位置 $p$ 是 $k$-有界的当且仅当在状态空间中 $M(p) \leq k$ 对所有可达标识 $M$ 成立。

### 4.2 活性

**定义 4.3 (活性)**
变迁 $t \in T$ 是活的，如果对于每个可达标识 $M \in R(M_0)$，都存在标识 $M' \in R(M)$ 使得 $M'[t\rangle$。

**定义 4.4 (死锁)**
标识 $M$ 是死锁，如果没有变迁在 $M$ 下使能。

**定理 4.2 (活性保持)**
如果所有变迁都是活的，则Petri网不会出现死锁。

**证明：** 通过活性定义：

1. 每个变迁在任何可达标识后都能再次使能
2. 不存在所有变迁都无法使能的标识
3. 因此不会出现死锁

### 4.3 可逆性

**定义 4.5 (可逆性)**
Petri网是可逆的，如果对于每个可达标识 $M \in R(M_0)$，都有 $M \rightarrow^* M_0$。

**定理 4.3 (可逆性判定)**
Petri网是可逆的当且仅当初始标识 $M_0$ 在状态空间中是强连通的。

## 5. 高级Petri网

### 5.1 时间Petri网

**定义 5.1 (时间Petri网)**
时间Petri网是六元组 $N = (P, T, F, M_0, I, D)$，其中：

- $(P, T, F, M_0)$ 是基础Petri网
- $I : T \rightarrow \mathbb{R}^+ \times \mathbb{R}^+$ 是时间间隔函数
- $D : T \rightarrow \mathbb{R}^+$ 是持续时间函数

**定义 5.2 (时间变迁发生)**
时间变迁 $t$ 在时间 $\tau$ 发生，如果：

1. $M[t\rangle$
2. $\tau \in I(t)$
3. 变迁持续时间为 $D(t)$

### 5.2 着色Petri网

**定义 5.3 (着色Petri网)**
着色Petri网是五元组 $N = (P, T, F, M_0, C)$，其中：

- $(P, T, F, M_0)$ 是基础Petri网
- $C : P \cup T \rightarrow \text{Type}$ 是颜色函数

**定义 5.4 (着色标识)**
着色标识 $M : P \rightarrow \text{Multiset}(C(p))$ 表示每个位置中的有色托肯。

## 6. 实际应用

### 6.1 并发系统建模

-**定义 6.1 (生产者-消费者模型)**

```haskell
data ProducerConsumer = ProducerConsumer
  { buffer :: Place
  , producer :: Transition
  , consumer :: Transition
  , produce :: Arc
  , consume :: Arc
  , capacity :: Int
  }
```

**定理 6.1 (生产者-消费者安全)**
生产者-消费者Petri网是安全的当且仅当缓冲区容量为1。

### 6.2 工作流建模

-**定义 6.2 (工作流Petri网)**

```haskell
data WorkflowNet = WorkflowNet
  { tasks :: [Place]
  , conditions :: [Place]
  , transitions :: [Transition]
  , start :: Place
  , end :: Place
  }
```

**定理 6.2 (工作流正确性)**
工作流Petri网是正确的当且仅当：

1. 从开始位置可达结束位置
2. 结束位置可达开始位置
3. 没有死锁

## 7. 分析算法

### 7.1 不变式分析

**定义 7.1 (S-不变式)**
向量 $x : P \rightarrow \mathbb{Z}$ 是S-不变式，如果对于所有标识 $M \in R(M_0)$：
$$\sum_{p \in P} x(p) \cdot M(p) = \sum_{p \in P} x(p) \cdot M_0(p)$$

**定理 7.1 (S-不变式性质)**
S-不变式提供Petri网的结构性质：

1. 托肯守恒
2. 有界性条件
3. 可达性约束

### 7.2 覆盖性分析

**定义 7.2 (覆盖性)**
标识 $M'$ 覆盖标识 $M$，记作 $M \leq M'$，如果对于所有位置 $p \in P$，都有 $M(p) \leq M'(p)$。

-**算法 7.1 (覆盖性检查)**

```haskell
covers :: Marking -> Marking -> Bool
covers m1 m2 = all (\p -> m1 p <= m2 p) places

findCovering :: PetriNet -> Marking -> [Marking]
findCovering net target = 
  filter (\m -> target `covers` m) (reachabilityAnalysis net)
```

## 8. 结论

Petri网理论为并发系统建模和分析提供了强大的形式化工具：

1. **并发建模**：精确描述并发行为和同步
2. **状态分析**：通过可达性分析验证系统性质
3. **结构分析**：通过不变式分析系统结构
4. **时间建模**：支持实时和定时系统分析

Petri网在软件工程、工作流管理、硬件设计等领域发挥着关键作用。通过形式化的Petri网模型，我们可以：

- 验证并发系统的正确性
- 检测死锁和活锁
- 分析系统性能
- 优化系统设计
