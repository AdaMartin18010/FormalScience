# Petri网理论基础 - 形式化数学体系

## 目录

1. [Petri网基础](#1-petri网基础)
2. [可达性分析](#2-可达性分析)
3. [并发性分析](#3-并发性分析)
4. [结构性质](#4-结构性质)
5. [高级Petri网](#5-高级petri网)
6. [时间Petri网](#6-时间petri网)
7. [着色Petri网](#7-着色petri网)
8. [实际应用](#8-实际应用)

## 1. Petri网基础

### 1.1 Petri网定义

**定义 1.1.1 (Petri网)**
Petri网是一个四元组 $N = (P, T, F, M_0)$，其中：

- $P$ 是有限的位置集合（places）
- $T$ 是有限的变迁集合（transitions）
- $F \subseteq (P \times T) \cup (T \times P)$ 是流关系（flow relation）
- $M_0 : P \rightarrow \mathbb{N}$ 是初始标识（initial marking）

**定义 1.1.2 (标识)**
标识 $M : P \rightarrow \mathbb{N}$ 表示每个位置中的托肯（token）数量。

**定义 1.1.3 (前集和后集)**
对于 $x \in P \cup T$：

- $^\bullet x = \{y \mid (y, x) \in F\}$ 是 $x$ 的前集（preset）
- $x^\bullet = \{y \mid (x, y) \in F\}$ 是 $x$ 的后集（postset）

**定义 1.1.4 (输入和输出函数)**
输入函数 $F^- : P \times T \rightarrow \mathbb{N}$ 和输出函数 $F^+ : T \times P \rightarrow \mathbb{N}$：
$$F^-(p, t) = \begin{cases} 1 & \text{if } (p, t) \in F \\ 0 & \text{otherwise} \end{cases}$$
$$F^+(t, p) = \begin{cases} 1 & \text{if } (t, p) \in F \\ 0 & \text{otherwise} \end{cases}$$

### 1.2 变迁规则

**定义 1.2.1 (变迁使能)**
变迁 $t \in T$ 在标识 $M$ 下使能，记作 $M[t\rangle$，当且仅当：
$$\forall p \in ^\bullet t : M(p) \geq F^-(p, t)$$

**定义 1.2.2 (变迁发生)**
如果 $M[t\rangle$，则变迁 $t$ 可以发生，产生新标识 $M'$，记作 $M[t\rangle M'$，其中：
$$M'(p) = M(p) - F^-(p, t) + F^+(t, p)$$

**定理 1.2.1 (变迁发生保持托肯守恒)**
对于任何变迁 $t$ 和标识 $M$，如果 $M[t\rangle M'$，则：
$$\sum_{p \in P} M'(p) = \sum_{p \in P} M(p)$$

**证明：** 通过流关系的定义：
$$\sum_{p \in P} M'(p) = \sum_{p \in P} (M(p) - F^-(p, t) + F^+(t, p))$$
$$= \sum_{p \in P} M(p) - \sum_{p \in P} F^-(p, t) + \sum_{p \in P} F^+(t, p)$$
$$= \sum_{p \in P} M(p) - |^\bullet t| + |t^\bullet| = \sum_{p \in P} M(p)$$

**算法 1.2.1 (变迁发生)**

```haskell
-- Petri网数据结构
data PetriNet = PetriNet
  { places :: [Place]
  , transitions :: [Transition]
  , flowRelation :: [(Place, Transition)]
  , initialMarking :: Marking
  }

data Marking = Marking
  { tokenCount :: Map Place Int
  }

-- 检查变迁使能
isEnabled :: PetriNet -> Marking -> Transition -> Bool
isEnabled net marking transition = 
  let preset = getPreset net transition
      requiredTokens = map (\p -> getTokenCount marking p) preset
      availableTokens = map (\p -> getTokenCount marking p) preset
  in all (>=) availableTokens requiredTokens

-- 执行变迁
fireTransition :: PetriNet -> Marking -> Transition -> Marking
fireTransition net marking transition = 
  let preset = getPreset net transition
      postset = getPostset net transition
      
      -- 移除输入托肯
      marking1 = foldl removeToken marking preset
      
      -- 添加输出托肯
      marking2 = foldl addToken marking1 postset
  in marking2

-- 移除托肯
removeToken :: Marking -> Place -> Marking
removeToken marking place = 
  let currentCount = getTokenCount marking place
      newCount = max 0 (currentCount - 1)
  in updateTokenCount marking place newCount

-- 添加托肯
addToken :: Marking -> Place -> Marking
addToken marking place = 
  let currentCount = getTokenCount marking place
      newCount = currentCount + 1
  in updateTokenCount marking place newCount
```

### 1.3 Petri网图形表示

**定义 1.3.1 (图形表示)**
Petri网的图形表示：

- 位置用圆圈表示：$\bigcirc$
- 变迁用矩形表示：$\square$
- 托肯用黑点表示：$\bullet$
- 流关系用有向弧表示：$\rightarrow$

**定义 1.3.2 (图形语法)**
Petri网图形的形式化定义：
$$G = (V, E, \mu, \nu)$$

其中：
- $V = P \cup T$ 是顶点集合
- $E = F$ 是边集合
- $\mu : V \rightarrow \{\text{place}, \text{transition}\}$ 是顶点类型函数
- $\nu : V \rightarrow \mathbb{N}$ 是托肯数量函数

## 2. 可达性分析

### 2.1 可达性关系

**定义 2.1.1 (可达性)**
标识 $M'$ 从标识 $M$ 可达，记作 $M \rightarrow^* M'$，如果存在变迁序列 $\sigma = t_1 t_2 \cdots t_n$ 使得：
$$M[t_1\rangle M_1[t_2\rangle M_2 \cdots [t_n\rangle M'$$

**定义 2.1.2 (可达集)**
从标识 $M$ 可达的所有标识集合：
$$R(M) = \{M' \mid M \rightarrow^* M'\}$$

**定义 2.1.3 (可达性图)**
可达性图 $G_R = (V_R, E_R)$，其中：
- $V_R = R(M_0)$ 是可达标识集合
- $E_R = \{(M, M') \mid \exists t : M[t\rangle M'\}$ 是变迁关系

**定理 2.1.1 (可达性保持)**
如果 $M \rightarrow^* M'$ 且 $M'[t\rangle M''$，则 $M \rightarrow^* M''$。

**证明：** 通过可达性的传递性：

1. $M \rightarrow^* M'$ 存在变迁序列 $\sigma$
2. $M'[t\rangle M''$ 表示 $t$ 在 $M'$ 下使能
3. 因此 $M \rightarrow^* M''$ 通过序列 $\sigma t$

**算法 2.1.1 (可达性分析)**

```haskell
-- 可达性分析
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

-- 检查标识可达性
isReachable :: PetriNet -> Marking -> Marking -> Bool
isReachable net from to = 
  let reachableSet = reachabilityAnalysis net
  in to `elem` reachableSet

-- 计算可达性图
reachabilityGraph :: PetriNet -> Graph Marking Transition
reachabilityGraph net = 
  let reachableMarkings = reachabilityAnalysis net
      edges = [(m1, t, m2) | m1 <- reachableMarkings, 
                            t <- enabledTransitions net m1,
                            let m2 = fireTransition net m1 t]
  in buildGraph reachableMarkings edges
```

### 2.2 状态空间分析

**定义 2.2.1 (状态空间)**
Petri网的状态空间是可达性图 $G_R$。

**定义 2.2.2 (状态空间性质)**
状态空间的性质：

- **有限性**：状态空间是有限的
- **连通性**：从初始标识可达所有其他标识
- **无环性**：状态空间可能包含环

**定理 2.2.1 (状态空间有限性)**
如果Petri网是有界的，则其状态空间是有限的。

**证明：** 通过有界性定义：

1. 每个位置 $p$ 的托肯数量有上界 $k_p$
2. 标识空间大小 $\leq \prod_{p \in P} (k_p + 1)$
3. 因此状态空间有限

**算法 2.2.1 (状态空间构建)**

```haskell
-- 构建状态空间
buildStateSpace :: PetriNet -> StateSpace
buildStateSpace net = 
  let initial = initialMarking net
      states = exploreStates net [initial] [initial]
      transitions = buildTransitions net states
  in StateSpace states transitions

-- 探索状态
exploreStates :: PetriNet -> [Marking] -> [Marking] -> [Marking]
exploreStates net [] visited = visited
exploreStates net (current:queue) visited = 
  let enabled = enabledTransitions net current
      newStates = [fireTransition net current t | t <- enabled]
      unvisited = filter (`notElem` visited) newStates
      newQueue = queue ++ unvisited
      newVisited = visited ++ unvisited
  in exploreStates net newQueue newVisited
```

## 3. 并发性分析

### 3.1 并发变迁

**定义 3.1.1 (并发变迁)**
两个变迁 $t_1, t_2 \in T$ 在标识 $M$ 下并发，记作 $M[t_1, t_2\rangle$，当且仅当：

1. $M[t_1\rangle$ 且 $M[t_2\rangle$
2. $^\bullet t_1 \cap ^\bullet t_2 = \emptyset$（无共享输入位置）

**定义 3.1.2 (并发发生)**
如果 $M[t_1, t_2\rangle$，则并发发生产生标识 $M'$，其中：
$$M'(p) = M(p) - F^-(p, t_1) - F^-(p, t_2) + F^+(t_1, p) + F^+(t_2, p)$$

**定理 3.1.1 (并发交换性)**
如果 $M[t_1, t_2\rangle$，则 $M[t_1\rangle M_1[t_2\rangle M'$ 且 $M[t_2\rangle M_2[t_1\rangle M'$，其中 $M_1 \neq M_2$ 但 $M'$ 相同。

**证明：** 通过并发变迁的定义：

1. 无共享输入位置确保独立性
2. 变迁发生顺序不影响最终结果
3. 中间标识可能不同但最终标识相同

**算法 3.1.1 (并发检测)**

```haskell
-- 检测并发变迁
concurrentTransitions :: PetriNet -> Marking -> [Transition]
concurrentTransitions net marking = 
  let enabled = enabledTransitions net marking
      concurrent = filter (\t1 -> 
        any (\t2 -> t1 /= t2 && areConcurrent net t1 t2) enabled) enabled
  in concurrent

-- 检查两个变迁是否并发
areConcurrent :: PetriNet -> Transition -> Transition -> Bool
areConcurrent net t1 t2 = 
  let preset1 = getPreset net t1
      preset2 = getPreset net t2
      shared = intersect preset1 preset2
  in null shared

-- 并发发生
fireConcurrent :: PetriNet -> Marking -> [Transition] -> Marking
fireConcurrent net marking transitions = 
  foldl (fireTransition net) marking transitions
```

### 3.2 冲突分析

**定义 3.2.1 (冲突)**
两个变迁 $t_1, t_2 \in T$ 在标识 $M$ 下冲突，当且仅当：

1. $M[t_1\rangle$ 且 $M[t_2\rangle$
2. $^\bullet t_1 \cap ^\bullet t_2 \neq \emptyset$（有共享输入位置）

**定义 3.2.2 (冲突解决)**
冲突通过非确定性选择解决，只能发生其中一个变迁。

**定理 3.2.1 (冲突不可并发)**
如果 $t_1, t_2$ 在 $M$ 下冲突，则不能并发发生。

**证明：** 通过冲突定义：

1. 共享输入位置限制托肯数量
2. 一个变迁的发生会消耗共享托肯
3. 另一个变迁将不再使能

**算法 3.2.1 (冲突检测)**

```haskell
-- 检测冲突
conflictingTransitions :: PetriNet -> Marking -> [(Transition, Transition)]
conflictingTransitions net marking = 
  let enabled = enabledTransitions net marking
      conflicts = [(t1, t2) | t1 <- enabled, t2 <- enabled, 
                             t1 < t2, areConflicting net t1 t2]
  in conflicts

-- 检查两个变迁是否冲突
areConflicting :: PetriNet -> Transition -> Transition -> Bool
areConflicting net t1 t2 = 
  let preset1 = getPreset net t1
      preset2 = getPreset net t2
      shared = intersect preset1 preset2
  in not (null shared)

-- 冲突解决
resolveConflict :: PetriNet -> Marking -> Transition -> Transition -> Transition
resolveConflict net marking t1 t2 = 
  -- 非确定性选择，这里选择第一个
  t1
```

### 3.3 死锁分析

**定义 3.3.1 (死锁)**
标识 $M$ 是死锁，如果没有变迁在 $M$ 下使能。

**定义 3.3.2 (死锁检测)**
死锁检测是识别所有死锁标识的过程。

**算法 3.3.1 (死锁检测)**

```haskell
-- 死锁检测
deadlockDetection :: PetriNet -> [Marking]
deadlockDetection net = 
  let reachable = reachabilityAnalysis net
      deadlocks = filter (isDeadlock net) reachable
  in deadlocks

-- 检查标识是否为死锁
isDeadlock :: PetriNet -> Marking -> Bool
isDeadlock net marking = 
  let enabled = enabledTransitions net marking
  in null enabled

-- 死锁预防
deadlockPrevention :: PetriNet -> PetriNet
deadlockPrevention net = 
  let deadlocks = deadlockDetection net
      preventionRules = generatePreventionRules deadlocks
  in applyPreventionRules net preventionRules
```

## 4. 结构性质

### 4.1 有界性

**定义 4.1.1 (有界性)**
位置 $p \in P$ 是 $k$-有界的，如果对于所有可达标识 $M \in R(M_0)$，都有 $M(p) \leq k$。

**定义 4.1.2 (安全Petri网)**
Petri网是安全的，如果所有位置都是1-有界的。

**定义 4.1.3 (有界Petri网)**
Petri网是有界的，如果所有位置都是 $k$-有界的（对于某个 $k$）。

**定理 4.1.1 (有界性判定)**
位置 $p$ 是 $k$-有界的当且仅当在状态空间中 $M(p) \leq k$ 对所有可达标识 $M$ 成立。

**证明：** 通过可达性分析：

1. 构建状态空间
2. 检查所有可达标识
3. 验证托肯数量上界

**算法 4.1.1 (有界性分析)**

```haskell
-- 有界性分析
boundednessAnalysis :: PetriNet -> Map Place Int
boundednessAnalysis net = 
  let reachable = reachabilityAnalysis net
      bounds = map (\p -> (p, maxTokenCount net p reachable)) (places net)
  in Map.fromList bounds

-- 计算位置的最大托肯数
maxTokenCount :: PetriNet -> Place -> [Marking] -> Int
maxTokenCount net place markings = 
  maximum [getTokenCount marking place | marking <- markings]

-- 检查安全性
isSafe :: PetriNet -> Bool
isSafe net = 
  let bounds = boundednessAnalysis net
  in all (<= 1) (Map.elems bounds)
```

### 4.2 活性

**定义 4.2.1 (活性)**
变迁 $t \in T$ 是活的，如果对于每个可达标识 $M \in R(M_0)$，都存在标识 $M' \in R(M)$ 使得 $M'[t\rangle$。

**定义 4.2.2 (活性级别)**
活性级别：

- **L0-活**：$t$ 永远不能发生
- **L1-活**：$t$ 至少发生一次
- **L2-活**：$t$ 发生有限次
- **L3-活**：$t$ 发生无限次
- **L4-活**：$t$ 在任何标识后都能再次发生

**定理 4.2.1 (活性保持)**
如果所有变迁都是活的，则Petri网不会出现死锁。

**证明：** 通过活性定义：

1. 每个变迁在任何可达标识后都能再次使能
2. 不存在所有变迁都无法使能的标识
3. 因此不会出现死锁

**算法 4.2.1 (活性分析)**

```haskell
-- 活性分析
livenessAnalysis :: PetriNet -> Map Transition LivenessLevel
livenessAnalysis net = 
  let reachable = reachabilityAnalysis net
      liveness = map (\t -> (t, computeLiveness net t reachable)) (transitions net)
  in Map.fromList liveness

-- 计算变迁活性级别
computeLiveness :: PetriNet -> Transition -> [Marking] -> LivenessLevel
computeLiveness net transition markings = 
  let canFire = [marking | marking <- markings, isEnabled net marking transition]
  in if null canFire
     then L0
     else if length canFire == length markings
          then L4
          else L1

-- 检查死锁自由
isDeadlockFree :: PetriNet -> Bool
isDeadlockFree net = 
  let liveness = livenessAnalysis net
  in all (>= L1) (Map.elems liveness)
```

### 4.3 可逆性

**定义 4.3.1 (可逆性)**
Petri网是可逆的，如果对于每个可达标识 $M \in R(M_0)$，都有 $M \rightarrow^* M_0$。

**定义 4.3.2 (强可逆性)**
Petri网是强可逆的，如果对于每个可达标识 $M \in R(M_0)$，都存在从 $M$ 到 $M_0$ 的路径。

**定理 4.3.1 (可逆性判定)**
Petri网是可逆的当且仅当初始标识 $M_0$ 在状态空间中是强连通的。

**证明：** 通过可达性分析：

1. 构建状态空间
2. 检查强连通性
3. 验证可逆性

**算法 4.3.1 (可逆性分析)**

```haskell
-- 可逆性分析
reversibilityAnalysis :: PetriNet -> Bool
reversibilityAnalysis net = 
  let reachable = reachabilityAnalysis net
      stateSpace = buildStateSpace net
  in isStronglyConnected stateSpace

-- 检查强连通性
isStronglyConnected :: StateSpace -> Bool
isStronglyConnected stateSpace = 
  let nodes = states stateSpace
      edges = transitions stateSpace
      graph = buildGraph nodes edges
  in all (\node -> isReachableFromAll graph node) nodes
```

## 5. 高级Petri网

### 5.1 时间Petri网

**定义 5.1.1 (时间Petri网)**
时间Petri网是六元组 $N = (P, T, F, M_0, I, D)$，其中：

- $(P, T, F, M_0)$ 是基础Petri网
- $I : T \rightarrow \mathbb{R}^+ \times \mathbb{R}^+$ 是时间间隔函数
- $D : T \rightarrow \mathbb{R}^+$ 是持续时间函数

**定义 5.1.2 (时间标识)**
时间标识是二元组 $(M, \tau)$，其中 $M$ 是标识，$\tau$ 是时间。

**定义 5.1.3 (时间变迁发生)**
时间变迁 $t$ 在时间 $\tau$ 发生，如果：

1. $M[t\rangle$
2. $\tau \in I(t)$
3. 变迁持续时间为 $D(t)$

**算法 5.1.1 (时间Petri网模拟)**

```haskell
-- 时间Petri网
data TimedPetriNet = TimedPetriNet
  { baseNet :: PetriNet
  , timeIntervals :: Map Transition (Double, Double)
  , durations :: Map Transition Double
  }

-- 时间标识
data TimedMarking = TimedMarking
  { marking :: Marking
  , time :: Double
  }

-- 时间变迁发生
fireTimedTransition :: TimedPetriNet -> TimedMarking -> Transition -> Double -> TimedMarking
fireTimedTransition net timedMarking transition fireTime = 
  let baseMarking = marking timedMarking
      currentTime = time timedMarking
      interval = timeIntervals net Map.! transition
      duration = durations net Map.! transition
      
      -- 检查时间约束
      (minTime, maxTime) = interval
      validTime = fireTime >= minTime && fireTime <= maxTime
      
      -- 执行变迁
      newMarking = fireTransition (baseNet net) baseMarking transition
      newTime = currentTime + duration
  in if validTime
     then TimedMarking newMarking newTime
     else timedMarking  -- 时间约束不满足
```

### 5.2 着色Petri网

**定义 5.2.1 (着色Petri网)**
着色Petri网是五元组 $N = (P, T, F, M_0, C)$，其中：

- $(P, T, F, M_0)$ 是基础Petri网
- $C : P \cup T \rightarrow \text{Type}$ 是颜色函数

**定义 5.2.2 (着色标识)**
着色标识 $M : P \rightarrow \text{Multiset}(C(p))$ 表示每个位置中的有色托肯。

**定义 5.2.3 (着色变迁)**
着色变迁的使能条件需要考虑颜色匹配。

**算法 5.2.1 (着色Petri网)**

```haskell
-- 着色Petri网
data ColoredPetriNet = ColoredPetriNet
  { baseNet :: PetriNet
  , colorFunction :: Map (Either Place Transition) ColorType
  }

-- 颜色类型
data ColorType = 
  IntColor
  | StringColor
  | ProductColor [ColorType]
  | SumColor [ColorType]

-- 着色标识
data ColoredMarking = ColoredMarking
  { tokenMultiset :: Map Place (Multiset Color)
  }

-- 着色变迁使能
isColoredEnabled :: ColoredPetriNet -> ColoredMarking -> Transition -> Bool
isColoredEnabled net marking transition = 
  let preset = getPreset (baseNet net) transition
      requiredColors = map (\p -> getRequiredColors net p transition) preset
      availableColors = map (\p -> getAvailableColors marking p) preset
  in all (hasMatchingColors) (zip requiredColors availableColors)
```

## 6. 时间Petri网

### 6.1 时间语义

**定义 6.1.1 (时间语义)**
时间Petri网的时间语义定义变迁发生的时机。

**定义 6.1.2 (时间状态)**
时间状态是三元组 $(M, \tau, \text{enabled})$，其中：

- $M$ 是标识
- $\tau$ 是当前时间
- $\text{enabled}$ 是使能变迁集合

**算法 6.1.1 (时间状态转换)**

```haskell
-- 时间状态
data TimedState = TimedState
  { marking :: Marking
  , currentTime :: Double
  , enabledTransitions :: [(Transition, Double, Double)]  -- (transition, minTime, maxTime)
  }

-- 时间状态转换
timedStateTransition :: TimedPetriNet -> TimedState -> Transition -> Double -> TimedState
timedStateTransition net state transition fireTime = 
  let newMarking = fireTransition (baseNet net) (marking state) transition
      newTime = fireTime
      newEnabled = updateEnabledTransitions net newMarking newTime
  in TimedState newMarking newTime newEnabled

-- 更新使能变迁
updateEnabledTransitions :: TimedPetriNet -> Marking -> Double -> [(Transition, Double, Double)]
updateEnabledTransitions net marking time = 
  let enabled = enabledTransitions (baseNet net) marking
      timeInfo = map (\t -> (t, getTimeInterval net t)) enabled
  in timeInfo
```

### 6.2 时间可达性

**定义 6.2.1 (时间可达性)**
时间标识 $(M', \tau')$ 从 $(M, \tau)$ 时间可达，如果存在时间变迁序列。

**算法 6.2.1 (时间可达性分析)**

```haskell
-- 时间可达性分析
timedReachabilityAnalysis :: TimedPetriNet -> [TimedState]
timedReachabilityAnalysis net = 
  let initial = TimedState (initialMarking (baseNet net)) 0 []
      reachable = exploreTimedStates net [initial] [initial]
  in reachable

-- 探索时间状态
exploreTimedStates :: TimedPetriNet -> [TimedState] -> [TimedState] -> [TimedState]
exploreTimedStates net [] visited = visited
exploreTimedStates net (current:queue) visited = 
  let enabled = enabledTransitions current
      newStates = [timedStateTransition net current t time | 
                   (t, minTime, maxTime) <- enabled,
                   time <- [minTime, maxTime]]
      unvisited = filter (`notElem` visited) newStates
      newQueue = queue ++ unvisited
      newVisited = visited ++ unvisited
  in exploreTimedStates net newQueue newVisited
```

## 7. 着色Petri网

### 7.1 颜色语义

**定义 7.1.1 (颜色语义)**
着色Petri网的颜色语义定义托肯的颜色和变迁的颜色匹配。

**定义 7.1.2 (颜色表达式)**
颜色表达式定义变迁的输入输出颜色关系。

**算法 7.1.1 (颜色匹配)**

```haskell
-- 颜色表达式
data ColorExpression = 
  Variable String
  | Constant Color
  | Tuple [ColorExpression]
  | Function String [ColorExpression]

-- 颜色匹配
colorMatching :: ColoredPetriNet -> Transition -> ColorBinding -> Bool
colorMatching net transition binding = 
  let inputArcs = getInputArcs net transition
      outputArcs = getOutputArcs net transition
      
      inputMatch = all (matchInputArc binding) inputArcs
      outputMatch = all (matchOutputArc binding) outputArcs
  in inputMatch && outputMatch

-- 输入弧匹配
matchInputArc :: ColorBinding -> (Place, Transition, ColorExpression) -> Bool
matchInputArc binding (place, transition, expression) = 
  let requiredColor = evaluateExpression expression binding
      availableColors = getAvailableColors place
  in requiredColor `elem` availableColors
```

### 7.2 着色可达性

**定义 7.2.1 (着色可达性)**
着色标识 $M'$ 从 $M$ 着色可达，如果存在颜色匹配的变迁序列。

**算法 7.2.1 (着色可达性分析)**

```haskell
-- 着色可达性分析
coloredReachabilityAnalysis :: ColoredPetriNet -> [ColoredMarking]
coloredReachabilityAnalysis net = 
  let initial = initialColoredMarking net
      reachable = exploreColoredStates net [initial] [initial]
  in reachable

-- 探索着色状态
exploreColoredStates :: ColoredPetriNet -> [ColoredMarking] -> [ColoredMarking] -> [ColoredMarking]
exploreColoredStates net [] visited = visited
exploreColoredStates net (current:queue) visited = 
  let enabled = enabledColoredTransitions net current
      newStates = [fireColoredTransition net current t binding | 
                   (t, binding) <- enabled]
      unvisited = filter (`notElem` visited) newStates
      newQueue = queue ++ unvisited
      newVisited = visited ++ unvisited
  in exploreColoredStates net newQueue newVisited
```

## 8. 实际应用

### 8.1 并发系统建模

**定义 8.1.1 (生产者-消费者模型)**
生产者-消费者系统的Petri网模型。

**算法 8.1.1 (生产者-消费者Petri网)**

```haskell
-- 生产者-消费者Petri网
producerConsumerNet :: PetriNet
producerConsumerNet = PetriNet
  { places = [ProducerReady, Buffer, ConsumerReady, ProducerWorking, ConsumerWorking]
  , transitions = [Produce, Consume, StartProduce, StartConsume]
  , flowRelation = [
      (ProducerReady, StartProduce),
      (StartProduce, ProducerWorking),
      (ProducerWorking, Produce),
      (Produce, Buffer),
      (Produce, ProducerReady),
      (Buffer, StartConsume),
      (StartConsume, ConsumerWorking),
      (ConsumerWorking, Consume),
      (Consume, ConsumerReady),
      (Consume, Buffer)
    ]
  , initialMarking = Marking $ Map.fromList [
      (ProducerReady, 1),
      (Buffer, 0),
      (ConsumerReady, 1),
      (ProducerWorking, 0),
      (ConsumerWorking, 0)
    ]
  }
```

### 8.2 工作流建模

**定义 8.2.1 (工作流Petri网)**
工作流系统的Petri网模型。

**算法 8.2.1 (工作流分析)**

```haskell
-- 工作流分析
workflowAnalysis :: PetriNet -> WorkflowProperties
workflowAnalysis net = 
  let reachable = reachabilityAnalysis net
      bounds = boundednessAnalysis net
      liveness = livenessAnalysis net
      deadlocks = deadlockDetection net
  in WorkflowProperties bounds liveness deadlocks

-- 工作流性质
data WorkflowProperties = WorkflowProperties
  { boundedness :: Map Place Int
  , liveness :: Map Transition LivenessLevel
  , deadlocks :: [Marking]
  }
```

### 8.3 性能分析

**定义 8.3.1 (性能度量)**
Petri网的性能度量：

- **吞吐量**：单位时间内完成的变迁数量
- **响应时间**：从输入到输出的时间
- **资源利用率**：资源的使用效率

**算法 8.3.1 (性能分析)**

```haskell
-- 性能分析
performanceAnalysis :: TimedPetriNet -> PerformanceMetrics
performanceAnalysis net = 
  let timedStates = timedReachabilityAnalysis net
      throughput = computeThroughput net timedStates
      responseTime = computeResponseTime net timedStates
      utilization = computeUtilization net timedStates
  in PerformanceMetrics throughput responseTime utilization

-- 性能度量
data PerformanceMetrics = PerformanceMetrics
  { throughput :: Double
  , responseTime :: Double
  , utilization :: Map Place Double
  }
```

## 结论

Petri网理论为并发系统的建模、分析和验证提供了强大的数学工具，从基础的变迁规则到高级的时间Petri网和着色Petri网，涵盖了：

1. **基础理论**: Petri网定义、变迁规则、可达性分析
2. **并发性**: 并发变迁、冲突分析、死锁检测
3. **结构性质**: 有界性、活性、可逆性
4. **高级模型**: 时间Petri网、着色Petri网
5. **实际应用**: 并发系统建模、工作流分析、性能分析

这些理论为并发系统的设计、验证和优化提供了坚实的理论基础。

## 参考文献

1. Reisig, W. (2013). *Understanding Petri nets: modeling techniques, analysis methods, case studies*. Springer Science & Business Media.
2. Murata, T. (1989). Petri nets: Properties, analysis and applications. *Proceedings of the IEEE*, 77(4), 541-580.
3. Jensen, K., & Kristensen, L. M. (2009). *Coloured Petri nets: modelling and validation of concurrent systems*. Springer Science & Business Media.
4. Berthomieu, B., & Diaz, M. (1991). Modeling and verification of time dependent systems using time Petri nets. *IEEE transactions on software engineering*, 17(3), 259-273.
5. Desel, J., & Esparza, J. (1995). *Free choice Petri nets*. Cambridge University Press.
6. Best, E., Devillers, R., & Hall, J. G. (2001). The box calculus: a new causal algebra with multi-label communication. *Advances in Petri Nets*, 21-69.
7. van der Aalst, W. M. (1998). The application of Petri nets to workflow management. *Journal of Circuits, Systems, and Computers*, 8(01), 21-66.

---

**最后更新**: 2024年12月19日  
**版本**: v1.0  
**状态**: 完成Petri网理论基础重构
