# Petri网理论基础 (Petri Net Theory Foundation)

## 目录

1. [引言](#1-引言)
2. [基本Petri网](#2-基本petri网)
3. [高级Petri网](#3-高级petri网)
4. [并发语义](#4-并发语义)
5. [分析技术](#5-分析技术)
6. [时间Petri网](#6-时间petri网)
7. [着色Petri网](#7-着色petri网)
8. [应用与扩展](#8-应用与扩展)
9. [参考文献](#9-参考文献)

## 1. 引言

### 1.1 Petri网概述

Petri网是并发系统建模和分析的重要形式化工具，由Carl Adam Petri在1962年提出。Petri网通过图形化的方式表示系统的并发行为，为并发系统的设计、分析和验证提供了严格的数学基础。

**定义 1.1.1** (Petri网)
Petri网是一个四元组 $N = (P, T, F, M_0)$，其中：

- $P$ 是有限库所集 (places)
- $T$ 是有限变迁集 (transitions)，满足 $P \cap T = \emptyset$
- $F \subseteq (P \times T) \cup (T \times P)$ 是流关系 (flow relation)
- $M_0: P \rightarrow \mathbb{N}$ 是初始标识 (initial marking)

**定义 1.1.2** (Petri网特性)
Petri网具有以下特性：

1. **并发性**：多个变迁可以同时发生
2. **冲突性**：多个变迁竞争同一资源
3. **同步性**：变迁需要多个条件同时满足
4. **不确定性**：系统行为可能不确定

### 1.2 Petri网分类

Petri网按表达能力分类：

- **基本Petri网**：最简单的Petri网形式
- **时间Petri网**：包含时间约束
- **着色Petri网**：包含数据类型
- **层次Petri网**：支持模块化设计

## 2. 基本Petri网

### 2.1 基本定义

**定义 2.1.1** (标识)
标识是一个函数 $M: P \rightarrow \mathbb{N}$，表示每个库所中的托肯数量。

**定义 2.1.2** (前集和后集)
对于变迁 $t \in T$ 和库所 $p \in P$：

- $\bullet t = \{p \in P \mid (p, t) \in F\}$ (变迁 $t$ 的前集)
- $t \bullet = \{p \in P \mid (t, p) \in F\}$ (变迁 $t$ 的后集)
- $\bullet p = \{t \in T \mid (t, p) \in F\}$ (库所 $p$ 的前集)
- $p \bullet = \{t \in T \mid (p, t) \in F\}$ (库所 $p$ 的后集)

**定义 2.1.3** (变迁使能)
变迁 $t$ 在标识 $M$ 下使能，当且仅当：

$$\forall p \in \bullet t: M(p) \geq 1$$

**定义 2.1.4** (变迁发生)
如果变迁 $t$ 在标识 $M$ 下使能，则 $t$ 可以发生，产生新标识 $M'$：

$$M'(p) = \begin{cases}
M(p) - 1 & \text{if } p \in \bullet t - t \bullet \\
M(p) + 1 & \text{if } p \in t \bullet - \bullet t \\
M(p) & \text{otherwise}
\end{cases}$$

**定理 2.1.1** (标识守恒)
对于任意变迁 $t$ 和标识 $M$，如果 $t$ 在 $M$ 下使能，则：

$$\sum_{p \in P} M'(p) = \sum_{p \in P} M(p)$$

**证明**：通过变迁发生规则：

1. 每个前集库所减少一个托肯
2. 每个后集库所增加一个托肯
3. 其他库所保持不变
4. 因此总托肯数守恒

### 2.2 可达性分析

**定义 2.2.1** (可达性关系)
标识 $M'$ 从标识 $M$ 可达，记作 $M \rightarrow^* M'$，如果存在变迁序列 $\sigma = t_1 t_2 \cdots t_n$ 使得：

$$M \xrightarrow{t_1} M_1 \xrightarrow{t_2} M_2 \rightarrow \cdots \xrightarrow{t_n} M'$$

**定义 2.2.2** (可达集)
可达集定义为：

$$R(N, M_0) = \{M \mid M_0 \rightarrow^* M\}$$

**定理 2.2.1** (可达性判定)
Petri网的可达性问题在一般情况下是不可判定的。

**证明**：通过归约到停机问题：

1. 每个图灵机都可以编码为Petri网
2. 图灵机停机对应Petri网达到特定标识
3. 由于停机问题不可判定，可达性问题也不可判定

**定理 2.2.2** (有界性)
如果Petri网的所有库所在所有可达标识中都有界，则可达集是有限的。

**证明**：通过鸽巢原理：

1. 每个库所的托肯数有上界
2. 所有库所的托肯数组合有上界
3. 因此可达集大小有限

**算法 2.2.1** (可达性分析)

```haskell
data PetriNet = PetriNet {
  places :: Set Place,
  transitions :: Set Transition,
  flowRelation :: Set (Place, Transition, Transition, Place),
  initialMarking :: Map Place Int
}

data Marking = Marking {
  tokens :: Map Place Int
}

data Transition = Transition {
  id :: String,
  prePlaces :: Set Place,
  postPlaces :: Set Place
}

isEnabled :: Transition -> Marking -> Bool
isEnabled transition marking = 
  all (\place -> 
    Map.findWithDefault 0 place marking.tokens >= 1) 
    transition.prePlaces

fireTransition :: Transition -> Marking -> Marking
fireTransition transition marking = 
  let -- 从前集库所移除托肯
      afterPre = foldl (\m place -> 
        Map.insert place (m Map.! place - 1) m) 
        marking.tokens transition.prePlaces
      -- 向后集库所添加托肯
      afterPost = foldl (\m place -> 
        Map.insert place (m Map.! place + 1) m) 
        afterPre transition.postPlaces
  in Marking { tokens = afterPost }

computeReachableSet :: PetriNet -> Set Marking
computeReachableSet net = 
  let initialMarking = Marking { tokens = net.initialMarking }
      -- 广度优先搜索可达标识
      search :: Set Marking -> Set Marking -> Set Marking
      search visited frontier = 
        if Set.null frontier
        then visited
        else 
          let current = Set.findMin frontier
              newVisited = Set.insert current visited
              -- 计算所有可能的后续标识
              successors = Set.fromList [fireTransition t current | 
                t <- Set.toList net.transitions, 
                isEnabled t current]
              newFrontier = Set.union (Set.deleteMin frontier) 
                           (Set.difference successors newVisited)
          in search newVisited newFrontier
  in search Set.empty (Set.singleton initialMarking)
```

### 2.3 不变性分析

**定义 2.3.1** (不变性)
向量 $I: P \rightarrow \mathbb{Z}$ 是Petri网的不变性，如果对于任意标识 $M$ 和变迁 $t$：

$$\text{If } M \xrightarrow{t} M', \text{ then } I \cdot M = I \cdot M'$$

**定理 2.3.1** (不变性保持)
如果 $I$ 是不变性，则对于任意可达标识 $M$：

$$I \cdot M = I \cdot M_0$$

**证明**：通过归纳法：

1. **基础情况**：$M = M_0$ 时显然成立
2. **归纳步骤**：假设 $M \xrightarrow{t} M'$，则 $I \cdot M' = I \cdot M = I \cdot M_0$

**定理 2.3.2** (不变性构造)
每个Petri网都有非平凡的不变性。

**证明**：通过线性代数：

1. 构造关联矩阵 $C$
2. 求解方程 $C^T \cdot I = 0$
3. 非零解即为不变性

**算法 2.3.1** (不变性计算)

```haskell
data Invariant = Invariant {
  coefficients :: Map Place Int
}

computeInvariants :: PetriNet -> [Invariant]
computeInvariants net = 
  let -- 构造关联矩阵
      incidenceMatrix = constructIncidenceMatrix net
      -- 求解齐次线性方程组
      solutions = solveHomogeneousSystem incidenceMatrix
      -- 转换为不变性形式
      invariants = map (\solution -> 
        Invariant { coefficients = solution }) solutions
  in invariants

constructIncidenceMatrix :: PetriNet -> Matrix Int
constructIncidenceMatrix net = 
  let places = Set.toList net.places
      transitions = Set.toList net.transitions
      -- 构造矩阵
      matrix = matrix (length places) (length transitions) (\(i, j) -> 
        let place = places !! i
            transition = transitions !! j
            preWeight = getFlowWeight net place transition
            postWeight = getFlowWeight net transition place
        in postWeight - preWeight)
  in matrix

solveHomogeneousSystem :: Matrix Int -> [Map Place Int]
solveHomogeneousSystem matrix = 
  let -- 使用高斯消元法求解
      reduced = gaussianElimination matrix
      -- 提取基础解系
      basis = extractBasis reduced
      -- 转换为不变性形式
      invariants = map vectorToMap basis
  in invariants

gaussianElimination :: Matrix Int -> Matrix Int
gaussianElimination matrix = 
  let (rows, cols) = matrixSize matrix
      -- 高斯消元过程
      eliminate row col matrix = 
        if row >= rows || col >= cols
        then matrix
        else 
          let pivot = matrix ! (row, col)
          in if pivot == 0
             then eliminate row (col + 1) matrix
             else 
               let -- 消元
                   newMatrix = eliminateColumn row col matrix
               in eliminate (row + 1) (col + 1) newMatrix
  in eliminate 0 0 matrix
```

## 3. 高级Petri网

### 3.1 时间Petri网

**定义 3.1.1** (时间Petri网)
时间Petri网是一个六元组 $N = (P, T, F, M_0, I, D)$，其中：

- $(P, T, F, M_0)$ 是基本Petri网
- $I: T \rightarrow \mathbb{R}^+ \times (\mathbb{R}^+ \cup \{\infty\})$ 是时间间隔函数
- $D: T \rightarrow \mathbb{R}^+$ 是延迟函数

**定义 3.1.2** (时间状态)
时间状态是一个对 $(M, \tau)$，其中：

- $M$ 是标识
- $\tau: T \rightarrow \mathbb{R}^+$ 是时钟函数

**定义 3.1.3** (时间变迁发生)
变迁 $t$ 在时间状态 $(M, \tau)$ 下可以发生，如果：

1. $t$ 在 $M$ 下使能
2. $\tau(t) \in I(t)$

**定理 3.1.1** (时间可达性)
时间Petri网的可达性问题比基本Petri网更复杂。

**证明**：通过时间约束：

1. 时间约束增加了状态空间维度
2. 时间约束可能导致无限状态空间
3. 时间约束使得分析算法更复杂

**算法 3.1.1** (时间Petri网分析)

```haskell
data TimedPetriNet = TimedPetriNet {
  basicNet :: PetriNet,
  timeIntervals :: Map Transition (Double, Double),
  delays :: Map Transition Double
}

data TimedState = TimedState {
  marking :: Marking,
  clocks :: Map Transition Double
}

data TimeInterval = TimeInterval {
  lower :: Double,
  upper :: Double
}

isTimedEnabled :: Transition -> TimedState -> Bool
isTimedEnabled transition state = 
  let basicEnabled = isEnabled transition state.marking
      timeEnabled = case Map.lookup transition.id state.clocks of
        Just clock -> 
          let interval = state.timeIntervals Map.! transition.id
          in clock >= interval.lower && clock <= interval.upper
        Nothing -> False
  in basicEnabled && timeEnabled

fireTimedTransition :: Transition -> TimedState -> TimedState
fireTimedTransition transition state = 
  let -- 基本变迁发生
      newMarking = fireTransition transition state.marking
      -- 重置时钟
      newClocks = Map.insert transition.id 0.0 state.clocks
  in TimedState {
    marking = newMarking,
    clocks = newClocks
  }

advanceTime :: Double -> TimedState -> TimedState
advanceTime delta state = 
  let -- 所有时钟增加时间
      newClocks = Map.map (\clock -> clock + delta) state.clocks
  in TimedState {
    marking = state.marking,
    clocks = newClocks
  }

computeTimedReachableSet :: TimedPetriNet -> Set TimedState
computeTimedReachableSet net = 
  let initialState = TimedState {
    marking = Marking { tokens = net.basicNet.initialMarking },
    clocks = Map.fromList [(t.id, 0.0) | t <- Set.toList net.basicNet.transitions]
  }
      -- 时间抽象可达性分析
      abstractStates = computeTimeAbstractStates net initialState
  in abstractStates

computeTimeAbstractStates :: TimedPetriNet -> TimedState -> Set TimedState
computeTimeAbstractStates net initialState = 
  let -- 计算时间区域
      regions = computeTimeRegions net
      -- 构造区域图
      regionGraph = constructRegionGraph net regions
      -- 计算可达区域
      reachableRegions = computeReachableRegions regionGraph initialState
  in reachableRegions
```

### 3.2 着色Petri网

**定义 3.2.1** (着色Petri网)
着色Petri网是一个六元组 $N = (P, T, F, M_0, C, G)$，其中：

- $(P, T, F, M_0)$ 是基本Petri网
- $C: P \cup T \rightarrow \Sigma$ 是颜色函数
- $G: T \rightarrow \text{Bool}$ 是守卫函数

**定义 3.2.2** (颜色标识)
颜色标识是一个函数 $M: P \rightarrow \text{Bag}(C(p))$，其中 $\text{Bag}(A)$ 表示集合 $A$ 的多重集。

**定义 3.2.3** (着色变迁发生)
变迁 $t$ 在标识 $M$ 下可以发生，如果：

1. 存在绑定 $\beta$ 使得 $G[t](\beta) = \text{true}$
2. 对于每个 $p \in \bullet t$，$M(p)$ 包含足够的颜色托肯

**定理 3.2.1** (着色表达能力)
着色Petri网比基本Petri网具有更强的表达能力。

**证明**：通过编码：

1. 每个着色Petri网都可以展开为基本Petri网
2. 展开后的网可能指数级增长
3. 着色网可以更紧凑地表示复杂系统

**算法 3.2.1** (着色Petri网展开)

```haskell
data ColoredPetriNet = ColoredPetriNet {
  basicNet :: PetriNet,
  colorFunctions :: Map (Place, Transition) ColorFunction,
  guardFunctions :: Map Transition GuardFunction
}

data ColorFunction = ColorFunction {
  inputColors :: Map Place [Color],
  outputColors :: Map Place [Color]
}

data GuardFunction = GuardFunction {
  condition :: Color -> Bool
}

data Color = Color {
  value :: String,
  type :: ColorType
}

data ColorType = IntType | StringType | ProductType [ColorType]

unfoldColoredNet :: ColoredPetriNet -> PetriNet
unfoldColoredNet coloredNet = 
  let -- 展开库所
      unfoldedPlaces = unfoldPlaces coloredNet
      -- 展开变迁
      unfoldedTransitions = unfoldTransitions coloredNet
      -- 展开流关系
      unfoldedFlow = unfoldFlowRelation coloredNet
      -- 展开初始标识
      unfoldedMarking = unfoldInitialMarking coloredNet
  in PetriNet {
    places = unfoldedPlaces,
    transitions = unfoldedTransitions,
    flowRelation = unfoldedFlow,
    initialMarking = unfoldedMarking
  }

unfoldPlaces :: ColoredPetriNet -> Set Place
unfoldPlaces coloredNet = 
  let -- 为每个库所和颜色组合创建新库所
      unfolded = concatMap (\place -> 
        let colors = getPlaceColors coloredNet place
        in [Place { id = place.id ++ "_" ++ show color, 
                   originalPlace = place.id,
                   color = color } | color <- colors]) 
        (Set.toList coloredNet.basicNet.places)
  in Set.fromList unfolded

unfoldTransitions :: ColoredPetriNet -> Set Transition
unfoldTransitions coloredNet = 
  let -- 为每个变迁和绑定组合创建新变迁
      unfolded = concatMap (\transition -> 
        let bindings = getValidBindings coloredNet transition
        in [Transition { id = transition.id ++ "_" ++ show binding,
                        originalTransition = transition.id,
                        binding = binding } | binding <- bindings])
        (Set.toList coloredNet.basicNet.transitions)
  in Set.fromList unfolded

getValidBindings :: ColoredPetriNet -> Transition -> [Binding]
getValidBindings net transition = 
  let -- 获取所有可能的颜色绑定
      allBindings = generateAllBindings net transition
      -- 过滤满足守卫条件的绑定
      validBindings = filter (\binding -> 
        evaluateGuard net transition binding) allBindings
  in validBindings

evaluateGuard :: ColoredPetriNet -> Transition -> Binding -> Bool
evaluateGuard net transition binding = 
  let guardFunction = net.guardFunctions Map.! transition.id
  in guardFunction.condition binding
```

## 4. 并发语义

### 4.1 步语义

**定义 4.1.1** (步)
步是一个多重集 $S: T \rightarrow \mathbb{N}$，表示同时发生的变迁。

**定义 4.1.2** (步使能)
步 $S$ 在标识 $M$ 下使能，如果：

$$\forall p \in P: M(p) \geq \sum_{t \in T} S(t) \cdot F(p,t)$$

**定义 4.1.3** (步发生)
步 $S$ 的发生产生新标识 $M'$：

$$M'(p) = M(p) + \sum_{t \in T} S(t) \cdot (F(t,p) - F(p,t))$$

**定理 4.1.1** (步语义等价性)
步语义与交错语义在可达性方面等价。

**证明**：通过交错展开：

1. 每个步都可以分解为交错序列
2. 每个交错序列都可以组合为步
3. 两种语义产生相同的可达集

**算法 4.1.1** (步语义分析)

```haskell
data Step = Step {
  transitions :: Map Transition Int
}

isStepEnabled :: Step -> Marking -> Bool
isStepEnabled step marking = 
  let -- 检查每个库所的托肯是否足够
      sufficientTokens = all (\place -> 
        let required = sum [step.transitions Map.! t * getFlowWeight place t | 
                           t <- Map.keys step.transitions]
            available = marking.tokens Map.! place
        in available >= required) 
        (Set.toList marking.tokens)
  in sufficientTokens

fireStep :: Step -> Marking -> Marking
fireStep step marking = 
  let -- 计算每个库所的托肯变化
      newTokens = Map.mapWithKey (\place currentTokens -> 
        let inputTokens = sum [step.transitions Map.! t * getFlowWeight place t | 
                              t <- Map.keys step.transitions]
            outputTokens = sum [step.transitions Map.! t * getFlowWeight t place | 
                               t <- Map.keys step.transitions]
        in currentTokens - inputTokens + outputTokens) 
        marking.tokens
  in Marking { tokens = newTokens }

computeMaximalSteps :: PetriNet -> Marking -> [Step]
computeMaximalSteps net marking = 
  let -- 计算所有可能的步
      allSteps = generateAllSteps net marking
      -- 过滤最大步
      maximalSteps = filter (\step -> 
        not (any (\largerStep -> 
          isSubstep step largerStep && step /= largerStep) allSteps)) 
        allSteps
  in maximalSteps

generateAllSteps :: PetriNet -> Marking -> [Step]
generateAllSteps net marking = 
  let enabledTransitions = filter (\t -> isEnabled t marking) 
                                 (Set.toList net.transitions)
      -- 生成所有可能的步组合
      stepCombinations = generateStepCombinations enabledTransitions
      -- 过滤有效的步
      validSteps = filter (\step -> isStepEnabled step marking) stepCombinations
  in validSteps
```

### 4.2 部分序语义

**定义 4.2.1** (部分序)
部分序是变迁发生之间的因果关系，表示为有向无环图。

**定义 4.2.2** (进程)
进程是部分序语义下的执行序列，表示变迁发生的因果关系。

**定义 4.2.3** (展开)
展开是Petri网的部分序语义表示，包含所有可能的执行序列。

**定理 4.2.1** (展开完备性)
展开包含Petri网的所有可能行为。

**证明**：通过构造性证明：

1. 每个执行序列对应展开中的一条路径
2. 展开包含所有可能的执行序列
3. 因此展开是完备的

**算法 4.2.1** (部分序分析)

```haskell
data PartialOrder = PartialOrder {
  events :: Set Event,
  causality :: Set (Event, Event),
  conflicts :: Set (Event, Event)
}

data Event = Event {
  id :: String,
  transition :: Transition,
  occurrence :: Int
}

data Process = Process {
  partialOrder :: PartialOrder,
  mapping :: Map Event (Place, Transition)
}

computeUnfolding :: PetriNet -> Process
computeUnfolding net = 
  let -- 初始化展开
      initialProcess = initializeProcess net
      -- 逐步展开
      unfoldedProcess = unfoldProcess net initialProcess
  in unfoldedProcess

unfoldProcess :: PetriNet -> Process -> Process
unfoldProcess net process = 
  let -- 找到可扩展的事件
      extensibleEvents = findExtensibleEvents net process
      -- 扩展每个可扩展事件
      newProcess = foldl (\p event -> 
        extendProcess net p event) process extensibleEvents
  in if extensibleEvents == []
     then process
     else unfoldProcess net newProcess

findExtensibleEvents :: PetriNet -> Process -> [Event]
findExtensibleEvents net process = 
  let -- 找到所有可能的扩展点
      cut = computeCut process
      -- 检查哪些变迁可以在当前切面上发生
      enabledTransitions = filter (\t -> 
        canOccurAtCut t cut) (Set.toList net.transitions)
      -- 创建新事件
      newEvents = map (\t -> 
        Event { id = generateEventId t,
                transition = t,
                occurrence = getNextOccurrence t }) 
        enabledTransitions
  in newEvents

extendProcess :: PetriNet -> Process -> Event -> Process
extendProcess net process event = 
  let -- 添加新事件
      newEvents = Set.insert event process.partialOrder.events
      -- 更新因果关系
      newCausality = updateCausality process event
      -- 更新冲突关系
      newConflicts = updateConflicts process event
      -- 更新映射
      newMapping = Map.insert event (getEventMapping event) process.mapping
  in Process {
    partialOrder = PartialOrder {
      events = newEvents,
      causality = newCausality,
      conflicts = newConflicts
    },
    mapping = newMapping
  }
```

## 5. 分析技术

### 5.1 结构分析

**定义 5.1.1** (关联矩阵)
关联矩阵 $C$ 定义为：

$$C(p,t) = F(t,p) - F(p,t)$$

**定义 5.1.2** (结构性质)
Petri网的结构性质：

1. **有界性**：所有库所有界
2. **活性**：所有变迁都可以无限次发生
3. **可逆性**：可以从任意可达标识回到初始标识
4. **持久性**：使能的变迁不会因为其他变迁发生而失去使能

**定理 5.1.1** (结构有界性)
Petri网结构有界当且仅当存在正不变性。

**证明**：通过不变性理论：

1. 如果存在正不变性，则所有库所有界
2. 如果网有界，则存在正不变性
3. 因此结构有界性等价于正不变性存在

**算法 5.1.1** (结构分析)

```haskell
data StructuralAnalysis = StructuralAnalysis {
  bounded :: Bool,
  live :: Bool,
  reversible :: Bool,
  persistent :: Bool
}

analyzeStructure :: PetriNet -> StructuralAnalysis
analyzeStructure net = 
  let -- 分析有界性
      bounded = checkBoundedness net
      -- 分析活性
      live = checkLiveness net
      -- 分析可逆性
      reversible = checkReversibility net
      -- 分析持久性
      persistent = checkPersistence net
  in StructuralAnalysis {
    bounded = bounded,
    live = live,
    reversible = reversible,
    persistent = persistent
  }

checkBoundedness :: PetriNet -> Bool
checkBoundedness net = 
  let -- 计算不变性
      invariants = computeInvariants net
      -- 检查是否存在正不变性
      positiveInvariant = any (\inv -> 
        all (\coeff -> coeff > 0) (Map.elems inv.coefficients)) invariants
  in positiveInvariant

checkLiveness :: PetriNet -> Bool
checkLiveness net = 
  let -- 计算可达集
      reachableSet = computeReachableSet net
      -- 检查每个变迁在每个可达标识下是否最终可发生
      allLive = all (\transition -> 
        all (\marking -> 
          canEventuallyFire transition marking reachableSet) 
        reachableSet) 
        (Set.toList net.transitions)
  in allLive

canEventuallyFire :: Transition -> Marking -> Set Marking -> Bool
canEventuallyFire transition marking reachableSet = 
  let -- 检查是否存在从当前标识到使能该变迁标识的路径
      canReachEnabled = any (\targetMarking -> 
        isEnabled transition targetMarking && 
        isReachable marking targetMarking reachableSet) 
        reachableSet
  in canReachEnabled
```

### 5.2 性能分析

**定义 5.2.1** (性能度量)
Petri网的性能度量：

1. **吞吐量**：单位时间内完成的变迁数量
2. **响应时间**：从输入到输出的时间
3. **利用率**：资源的使用效率
4. **瓶颈**：限制系统性能的组件

**定义 5.2.2** (随机Petri网)
随机Petri网为每个变迁分配指数分布的延迟时间。

**算法 5.2.1** (性能分析)

```haskell
data StochasticPetriNet = StochasticPetriNet {
  basicNet :: PetriNet,
  firingRates :: Map Transition Double
}

data PerformanceMetrics = PerformanceMetrics {
  throughput :: Map Transition Double,
  responseTime :: Double,
  utilization :: Map Place Double,
  bottlenecks :: [Transition]
}

analyzePerformance :: StochasticPetriNet -> PerformanceMetrics
analyzePerformance spn = 
  let -- 计算稳态概率
      steadyState = computeSteadyState spn
      -- 计算吞吐量
      throughput = computeThroughput spn steadyState
      -- 计算响应时间
      responseTime = computeResponseTime spn steadyState
      -- 计算利用率
      utilization = computeUtilization spn steadyState
      -- 识别瓶颈
      bottlenecks = identifyBottlenecks spn throughput
  in PerformanceMetrics {
    throughput = throughput,
    responseTime = responseTime,
    utilization = utilization,
    bottlenecks = bottlenecks
  }

computeSteadyState :: StochasticPetriNet -> Map Marking Double
computeSteadyState spn = 
  let -- 构造马尔可夫链
      markovChain = constructMarkovChain spn
      -- 求解稳态方程
      steadyState = solveSteadyStateEquations markovChain
  in steadyState

constructMarkovChain :: StochasticPetriNet -> Matrix Double
constructMarkovChain spn = 
  let -- 获取所有可达标识
      reachableMarkings = computeReachableSet spn.basicNet
      -- 构造转移率矩阵
      transitionMatrix = matrix (length reachableMarkings) 
                               (length reachableMarkings) (\(i, j) -> 
        let markingI = Set.elemAt i reachableMarkings
            markingJ = Set.elemAt j reachableMarkings
        in computeTransitionRate spn markingI markingJ)
  in transitionMatrix

solveSteadyStateEquations :: Matrix Double -> Map Marking Double
solveSteadyStateEquations matrix = 
  let -- 添加概率和为1的约束
      augmentedMatrix = addProbabilityConstraint matrix
      -- 求解线性方程组
      solution = solveLinearSystem augmentedMatrix
      -- 转换为概率分布
      steadyState = vectorToProbabilityMap solution
  in steadyState
```

## 6. 时间Petri网

### 6.1 时间语义

**定义 6.1.1** (时间Petri网语义)
时间Petri网的时间语义包括：

1. **最早发生时间**：变迁可以发生的最早时间
2. **最晚发生时间**：变迁必须发生的最晚时间
3. **时间间隔**：变迁发生的时间窗口

**定义 6.1.2** (时间状态)
时间状态包含：

1. **离散状态**：标识
2. **连续状态**：时钟值
3. **时间约束**：时钟约束

**算法 6.1.1** (时间分析)

```haskell
data TimedAnalysis = TimedAnalysis {
  earliestTimes :: Map Transition Double,
  latestTimes :: Map Transition Double,
  timeIntervals :: Map Transition (Double, Double)
}

analyzeTiming :: TimedPetriNet -> TimedAnalysis
analyzeTiming net = 
  let -- 计算最早发生时间
      earliest = computeEarliestTimes net
      -- 计算最晚发生时间
      latest = computeLatestTimes net
      -- 计算时间间隔
      intervals = Map.mapWithKey (\t (e, l) -> (e, l)) 
                 (Map.intersectionWith (,) earliest latest)
  in TimedAnalysis {
    earliestTimes = earliest,
    latestTimes = latest,
    timeIntervals = intervals
  }

computeEarliestTimes :: TimedPetriNet -> Map Transition Double
computeEarliestTimes net = 
  let -- 使用动态规划计算最早时间
      earliestTimes = foldl (\times transition -> 
        let predecessors = getPredecessors net transition
            maxPredecessorTime = maximum [times Map.! t | t <- predecessors]
            delay = net.delays Map.! transition.id
        in Map.insert transition.id (maxPredecessorTime + delay) times)
        Map.empty (topologicalSort net)
  in earliestTimes

computeLatestTimes :: TimedPetriNet -> Map Transition Double
computeLatestTimes net = 
  let -- 使用反向动态规划计算最晚时间
      latestTimes = foldl (\times transition -> 
        let successors = getSuccessors net transition
            minSuccessorTime = minimum [times Map.! t | t <- successors]
            delay = net.delays Map.! transition.id
        in Map.insert transition.id (minSuccessorTime - delay) times)
        Map.empty (reverseTopologicalSort net)
  in latestTimes
```

## 7. 着色Petri网

### 7.1 颜色语义

**定义 7.1.1** (颜色语义)
着色Petri网的颜色语义包括：

1. **颜色类型**：数据类型定义
2. **颜色函数**：输入输出颜色映射
3. **守卫条件**：变迁发生的条件

**定义 7.1.2** (绑定)
绑定是变量到颜色的映射，满足守卫条件。

**算法 7.1.1** (颜色分析)

```haskell
data ColorAnalysis = ColorAnalysis {
  colorTypes :: Map Place ColorType,
  colorFunctions :: Map Transition ColorFunction,
  validBindings :: Map Transition [Binding]
}

analyzeColors :: ColoredPetriNet -> ColorAnalysis
analyzeColors net = 
  let -- 分析颜色类型
      types = analyzeColorTypes net
      -- 分析颜色函数
      functions = analyzeColorFunctions net
      -- 计算有效绑定
      bindings = computeValidBindings net
  in ColorAnalysis {
    colorTypes = types,
    colorFunctions = functions,
    validBindings = bindings
  }

analyzeColorTypes :: ColoredPetriNet -> Map Place ColorType
analyzeColorTypes net = 
  let -- 推断每个库所的颜色类型
      types = Map.mapWithKey (\place _ -> 
        inferColorType net place) net.basicNet.places
  in types

inferColorType :: ColoredPetriNet -> Place -> ColorType
inferColorType net place = 
  let -- 分析输入变迁的颜色函数
      inputTransitions = getInputTransitions net place
      inputTypes = map (\t -> 
        getOutputColorType net t place) inputTransitions
      -- 分析输出变迁的颜色函数
      outputTransitions = getOutputTransitions net place
      outputTypes = map (\t -> 
        getInputColorType net t place) outputTransitions
      -- 统一颜色类型
      unifiedType = unifyColorTypes (inputTypes ++ outputTypes)
  in unifiedType

unifyColorTypes :: [ColorType] -> ColorType
unifyColorTypes types = 
  case types of
    [] -> IntType  -- 默认类型
    [t] -> t
    (t1:t2:rest) -> 
      let unified = unifyTwoTypes t1 t2
      in unifyColorTypes (unified:rest)

unifyTwoTypes :: ColorType -> ColorType -> ColorType
unifyTwoTypes t1 t2 = 
  case (t1, t2) of
    (IntType, IntType) -> IntType
    (StringType, StringType) -> StringType
    (ProductType ts1, ProductType ts2) -> 
      if length ts1 == length ts2
      then ProductType (zipWith unifyTwoTypes ts1 ts2)
      else error "Incompatible product types"
    _ -> error "Incompatible color types"
```

## 8. 应用与扩展

### 8.1 工作流建模

**定义 8.1.1** (工作流Petri网)
工作流Petri网用于建模业务流程：

1. **任务**：表示为变迁
2. **条件**：表示为库所
3. **控制流**：表示为流关系

**定义 8.1.2** (工作流性质)
工作流的重要性质：

1. **合理性**：每个任务都可以执行
2. **安全性**：不会出现死锁
3. **完整性**：所有任务都能完成

### 8.2 制造系统建模

**定义 8.2.1** (制造Petri网)
制造Petri网用于建模制造系统：

1. **机器**：表示为库所
2. **操作**：表示为变迁
3. **物料流**：表示为托肯

**定义 8.2.2** (制造性质)
制造系统的重要性质：

1. **无死锁**：系统不会进入死锁状态
2. **最大并发**：最大化系统并发度
3. **资源效率**：最大化资源利用率

## 9. 参考文献

1. **Petri, C. A.** (1962). Kommunikation mit Automaten. *Schriften des Instituts für Instrumentelle Mathematik*, 3.

2. **Reisig, W.** (2013). *Understanding Petri Nets: Modeling Techniques, Analysis Methods, Case Studies*. Springer.

3. **Murata, T.** (1989). Petri nets: Properties, analysis and applications. *Proceedings of the IEEE*, 77(4), 541-580.

4. **Jensen, K., & Kristensen, L. M.** (2009). *Coloured Petri Nets: Modelling and Validation of Concurrent Systems*. Springer.

5. **Berthomieu, B., & Diaz, M.** (1991). Modeling and verification of time dependent systems using time Petri nets. *IEEE Transactions on Software Engineering*, 17(3), 259-273.

6. **Esparza, J.** (1998). Decidability and complexity of Petri net problems—an introduction. *Lectures on Petri Nets I: Basic Models*, 1491, 374-428.

7. **Desel, J., & Reisig, W.** (1998). Place/transition Petri nets. *Lectures on Petri Nets I: Basic Models*, 1491, 122-173.

8. **Aalst, W. M. P. van der** (1998). The application of Petri nets to workflow management. *Journal of Circuits, Systems, and Computers*, 8(1), 21-66.

---

**文档版本**：1.0  
**最后更新**：2024-12-19  
**作者**：形式科学理论体系重构项目  
**状态**：已完成Petri网理论基础重构
