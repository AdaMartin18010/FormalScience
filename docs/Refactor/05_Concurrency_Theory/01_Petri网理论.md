# Petri网理论 (Petri Net Theory)

## 目录

1. [基本Petri网](#1-基本petri网)
2. [高级Petri网](#2-高级petri网)
3. [并发语义](#3-并发语义)
4. [分析技术](#4-分析技术)
5. [结构性质](#5-结构性质)
6. [性能分析](#6-性能分析)
7. [参考文献](#7-参考文献)

---

## 1. 基本Petri网

### 1.1 基本定义

**定义 1.1 (基本Petri网)**
基本Petri网是一个四元组 $N = (P, T, F, M_0)$，其中：

- $P$ 是有限库所集 (places)
- $T$ 是有限变迁集 (transitions)，满足 $P \cap T = \emptyset$
- $F \subseteq (P \times T) \cup (T \times P)$ 是流关系 (flow relation)
- $M_0: P \rightarrow \mathbb{N}$ 是初始标识 (initial marking)

**定义 1.2 (标识)**
标识 $M: P \rightarrow \mathbb{N}$ 是一个函数，表示每个库所中的托肯数量。

**定义 1.3 (前集和后集)**
对于任意 $x \in P \cup T$，定义：

- $\bullet x = \{y \in P \cup T \mid (y, x) \in F\}$ (前集)
- $x \bullet = \{y \in P \cup T \mid (x, y) \in F\}$ (后集)

**定义 1.4 (变迁使能)**
变迁 $t \in T$ 在标识 $M$ 下使能，记作 $M[t\rangle$，当且仅当：
$$\forall p \in \bullet t: M(p) \geq F(p, t)$$

其中 $F(p, t)$ 表示从库所 $p$ 到变迁 $t$ 的弧权重。

**定义 1.5 (变迁发生)**
如果变迁 $t$ 在标识 $M$ 下使能，则 $t$ 可以发生，产生新标识 $M'$，记作 $M[t\rangle M'$：
$$M'(p) = M(p) - F(p, t) + F(t, p)$$

### 1.2 可达性分析

**定义 1.6 (可达性关系)**
标识 $M'$ 从标识 $M$ 可达，记作 $M \rightarrow^* M'$，如果存在变迁序列 $\sigma = t_1 t_2 \cdots t_n$ 使得：
$$M[t_1\rangle M_1[t_2\rangle M_2 \cdots [t_n\rangle M'$$

**定义 1.7 (可达集)**
Petri网 $N$ 的可达集定义为：
$$R(N, M_0) = \{M \mid M_0 \rightarrow^* M\}$$

**定理 1.1 (标识守恒)**
对于任意变迁 $t$ 和标识 $M$，如果 $M[t\rangle M'$，则：
$$\sum_{p \in P} M'(p) = \sum_{p \in P} M(p)$$

**证明：** 通过变迁发生规则：

1. **托肯消耗**：每个前集库所 $p \in \bullet t$ 消耗 $F(p, t)$ 个托肯
2. **托肯产生**：每个后集库所 $p \in t \bullet$ 产生 $F(t, p)$ 个托肯
3. **守恒性**：由于 $\sum_{p \in \bullet t} F(p, t) = \sum_{p \in t \bullet} F(t, p)$，总托肯数守恒

**定理 1.2 (可达性判定)**
Petri网的可达性问题在一般情况下是不可判定的。

**证明：** 通过归约到停机问题：

1. **编码构造**：每个图灵机都可以编码为Petri网
2. **停机对应**：图灵机停机对应Petri网达到特定标识
3. **不可判定性**：由于停机问题不可判定，可达性问题也不可判定

**定理 1.3 (有界性)**
如果Petri网的所有库所在所有可达标识中都有界，则可达集是有限的。

**证明：** 通过鸽巢原理：

1. **有界性**：每个库所 $p$ 的托肯数有上界 $B_p$
2. **状态空间**：所有可能的标识组合数为 $\prod_{p \in P} (B_p + 1)$
3. **有限性**：由于每个 $B_p$ 有限，可达集大小有限

### 1.3 不变性分析

**定义 1.8 (不变性)**
向量 $I: P \rightarrow \mathbb{Z}$ 是Petri网的不变性，如果对于任意标识 $M$ 和变迁 $t$：
$$M[t\rangle M' \Rightarrow I \cdot M = I \cdot M'$$

其中 $I \cdot M = \sum_{p \in P} I(p) \cdot M(p)$。

**定理 1.4 (不变性保持)**
如果 $I$ 是不变性，则对于任意可达标识 $M$：
$$I \cdot M = I \cdot M_0$$

**证明：** 通过归纳法：

1. **基础情况**：$M = M_0$ 时显然成立
2. **归纳步骤**：假设 $M[t\rangle M'$，则 $I \cdot M' = I \cdot M = I \cdot M_0$

**定理 1.5 (不变性构造)**
每个Petri网都有非平凡的不变性。

**证明：** 通过线性代数：

1. **关联矩阵**：构造关联矩阵 $C$，其中 $C(p, t) = F(t, p) - F(p, t)$
2. **线性方程**：求解方程 $C^T \cdot I = 0$
3. **非零解**：由于 $C$ 的秩小于 $|P|$，存在非零解 $I$
4. **不变性**：非零解 $I$ 即为不变性

---

## 2. 高级Petri网

### 2.1 时间Petri网

**定义 2.1 (时间Petri网)**
时间Petri网是一个六元组 $N = (P, T, F, M_0, I, D)$，其中：

- $(P, T, F, M_0)$ 是基本Petri网
- $I: T \rightarrow \mathbb{R}^+ \times (\mathbb{R}^+ \cup \{\infty\})$ 是时间间隔函数
- $D: T \rightarrow \mathbb{R}^+$ 是延迟函数

**定义 2.2 (时间状态)**
时间状态是一个对 $(M, \tau)$，其中：

- $M$ 是标识
- $\tau: T \rightarrow \mathbb{R}^+$ 是时钟函数

**定义 2.3 (时间变迁发生)**
变迁 $t$ 在时间状态 $(M, \tau)$ 下可以发生，如果：

1. $t$ 在 $M$ 下使能
2. $\tau(t) \in I(t)$

**定理 2.1 (时间可达性)**
时间Petri网的可达性问题比基本Petri网更复杂。

**证明：** 通过时间约束：

1. **状态空间扩展**：时间约束增加了状态空间维度
2. **无限状态**：时间约束可能导致无限状态空间
3. **算法复杂度**：时间约束使得分析算法更复杂

### 2.2 着色Petri网

**定义 2.4 (着色Petri网)**
着色Petri网是一个六元组 $N = (P, T, F, M_0, C, G)$，其中：

- $(P, T, F, M_0)$ 是基本Petri网
- $C: P \cup T \rightarrow \Sigma$ 是颜色函数
- $G: T \rightarrow \text{Bool}$ 是守卫函数

**定义 2.5 (颜色标识)**
颜色标识是一个函数 $M: P \rightarrow \text{Bag}(C(p))$，其中 $\text{Bag}(A)$ 表示集合 $A$ 的多重集。

**定义 2.6 (着色变迁发生)**
变迁 $t$ 在标识 $M$ 下可以发生，如果：

1. 存在绑定 $\beta$ 使得 $G[t](\beta) = \text{true}$
2. 对于每个 $p \in \bullet t$，$M(p)$ 包含足够的颜色托肯

**定理 2.2 (着色表达能力)**
着色Petri网比基本Petri网具有更强的表达能力。

**证明：** 通过编码：

1. **展开构造**：每个着色Petri网都可以展开为基本Petri网
2. **指数增长**：展开后的网可能指数级增长
3. **紧凑表示**：着色网可以更紧凑地表示复杂系统

### 2.3 层次Petri网

**定义 2.7 (层次Petri网)**
层次Petri网是一个递归结构，其中：

- 每个子网都是一个Petri网
- 子网之间通过接口连接
- 支持抽象和细化

**定理 2.3 (层次分析)**
层次Petri网的分析可以通过组合方法进行。

**证明：** 通过模块化：

1. **独立分析**：每个子网可以独立分析
2. **接口抽象**：接口行为可以抽象
3. **组合行为**：整体行为通过组合得到

---

## 3. 并发语义

### 3.1 步语义

**定义 3.1 (步)**
步是一个多重集 $S: T \rightarrow \mathbb{N}$，表示同时发生的变迁。

**定义 3.2 (步使能)**
步 $S$ 在标识 $M$ 下使能，记作 $M[S\rangle$，如果：
$$\forall p \in P: M(p) \geq \sum_{t \in T} S(t) \cdot F(p, t)$$

**定义 3.3 (步发生)**
步 $S$ 的发生产生新标识 $M'$，记作 $M[S\rangle M'$：
$$M'(p) = M(p) + \sum_{t \in T} S(t) \cdot (F(t, p) - F(p, t))$$

**定理 3.1 (步语义等价性)**
步语义与交错语义在可达性方面等价。

**证明：** 通过交错展开：

1. **步分解**：每个步都可以分解为交错序列
2. **序列组合**：每个交错序列都可以组合为步
3. **等价性**：两种语义产生相同的可达集

### 3.2 部分序语义

**定义 3.4 (过程)**
过程是一个偏序集 $(E, \leq)$，其中：

- $E$ 是事件集
- $\leq$ 是因果序关系

**定义 3.5 (展开)**
Petri网的展开是一个过程，其中：

- 事件对应变迁发生
- 因果序对应依赖关系

**定理 3.2 (展开唯一性)**
每个Petri网都有唯一的展开。

**证明：** 通过构造：

1. **初始构造**：从初始标识开始
2. **逐步扩展**：逐步添加使能的变迁
3. **依赖建立**：建立因果依赖关系

---

## 4. 分析技术

### 4.1 状态空间分析

**定义 4.1 (状态图)**
状态图是一个有向图 $G = (V, E)$，其中：

- $V = R(N, M_0)$ 是可达标识集
- $E = \{(M, M') \mid \exists t \in T: M[t\rangle M'\}$ 是变迁关系

**定理 4.1 (状态图性质)**
状态图反映了Petri网的所有行为。

**证明：** 通过可达性：

1. **节点对应**：每个可达标识都是状态图的节点
2. **边对应**：每个变迁发生都是状态图的边
3. **行为完整**：状态图包含所有执行路径

-**算法 4.1 (状态空间构造)**

```haskell
constructStateSpace :: PetriNet -> Marking -> StateGraph
constructStateSpace net initialMarking = 
  let initialState = initialMarking
      states = [initialState]
      edges = []
  in buildStateSpace net states edges

buildStateSpace :: PetriNet -> [Marking] -> [Edge] -> StateGraph
buildStateSpace net states edges = 
  let newStates = findNewStates net states
      newEdges = findNewEdges net states newStates
      updatedStates = states ++ newStates
      updatedEdges = edges ++ newEdges
  in if null newStates 
     then StateGraph states edges
     else buildStateSpace net updatedStates updatedEdges
```

### 4.2 结构分析

**定义 4.2 (结构性质)**
结构性质是不依赖于初始标识的性质。

**定义 4.3 (结构有界性)**
Petri网结构有界，如果对于任意初始标识，网都是有界的。

**定理 4.2 (结构有界性)**
Petri网结构有界当且仅当存在正不变性。

**证明：** 通过线性规划：

1. **等价性**：结构有界性等价于线性约束系统有解
2. **约束系统**：$C^T \cdot I = 0$ 且 $I > 0$
3. **解对应**：线性约束系统的解对应不变性
4. **正不变性**：正不变性保证有界性

-**算法 4.2 (结构有界性检查)**

```haskell
checkStructuralBoundedness :: PetriNet -> Bool
checkStructuralBoundedness net = 
  let incidenceMatrix = buildIncidenceMatrix net
      constraints = buildConstraints incidenceMatrix
      solution = solveLinearProgram constraints
  in isFeasible solution

buildConstraints :: Matrix -> [Constraint]
buildConstraints matrix = 
  let rows = rowCount matrix
      constraints = [Constraint (matrix !! i) 0 | i <- [0..rows-1]]
      positivityConstraints = [Constraint (unitVector i) 0 | i <- [0..cols-1]]
  in constraints ++ positivityConstraints
```

### 4.3 不变性分析

**定义 4.4 (P-不变性)**
P-不变性是库所不变性，满足 $I \cdot M = I \cdot M_0$。

**定义 4.5 (T-不变性)**
T-不变性是变迁不变性，满足 $C \cdot \sigma = 0$。

**定理 4.3 (不变性构造)**
P-不变性可以通过求解 $C^T \cdot I = 0$ 得到。

**证明：** 通过线性代数：

1. **关联矩阵**：$C(p, t) = F(t, p) - F(p, t)$
2. **不变性条件**：$I \cdot M' = I \cdot M$ 对于任意 $M[t\rangle M'$
3. **线性方程**：$C^T \cdot I = 0$
4. **解空间**：所有解都是P-不变性

---

## 5. 结构性质

### 5.1 活性

**定义 5.1 (活性)**
变迁 $t$ 是活的，如果对于任意可达标识 $M$，存在从 $M$ 可达的标识 $M'$ 使得 $t$ 在 $M'$ 下使能。

**定义 5.2 (死锁)**
标识 $M$ 是死锁，如果没有变迁在 $M$ 下使能。

**定理 5.1 (活性判定)**
Petri网的活性判定是PSPACE完全的。

**证明：** 通过复杂度分析：

1. **可达性归约**：活性问题可以归约为可达性问题
2. **PSPACE下界**：可达性是PSPACE完全的
3. **PSPACE上界**：活性问题可以在PSPACE中解决

### 5.2 公平性

**定义 5.3 (公平性)**
Petri网满足公平性，如果对于任意无限执行序列，每个变迁都无限次使能。

**定理 5.2 (公平性判定)**
公平性判定可以通过状态空间分析进行。

**证明：** 通过强连通分量：

1. **强连通分量**：分析状态图的强连通分量
2. **公平性条件**：每个强连通分量中所有变迁都可达
3. **判定算法**：通过深度优先搜索检查

---

## 6. 性能分析

### 6.1 性能指标

**定义 6.1 (吞吐量)**
吞吐量是单位时间内完成的变迁数量。

**定义 6.2 (响应时间)**
响应时间是从输入到输出的时间延迟。

**定义 6.3 (利用率)**
利用率是资源的使用效率。

**定理 6.1 (性能界限)**
性能指标可以通过结构分析得到界限。

**证明：** 通过瓶颈分析：

1. **瓶颈库所**：瓶颈库所限制系统性能
2. **不变性上界**：不变性提供性能上界
3. **结构分析**：结构分析确定瓶颈位置

### 6.2 随机Petri网

**定义 6.4 (随机Petri网)**
随机Petri网在基本Petri网基础上添加指数分布的时间延迟。

**定理 6.2 (随机分析)**
随机Petri网可以分析系统的性能特性。

**证明：** 通过马尔可夫链：

1. **状态空间**：随机Petri网的状态空间是马尔可夫链
2. **稳态分析**：可以计算稳态概率分布
3. **性能计算**：基于稳态分布计算性能指标

---

## 7. 参考文献

1. **Petri, C. A.** (1962). Kommunikation mit Automaten. PhD thesis, Universität Hamburg.

2. **Reisig, W.** (2013). *Understanding Petri nets: Modeling techniques, analysis methods, case studies*. Springer.

3. **Murata, T.** (1989). Petri nets: Properties, analysis and applications. *Proceedings of the IEEE*, 77(4), 541-580.

4. **Jensen, K., & Kristensen, L. M.** (2009). *Colored Petri nets: Modeling and validation of concurrent systems*. Springer.

5. **Berthomieu, B., & Diaz, M.** (1991). Modeling and verification of time dependent systems using time Petri nets. *IEEE transactions on software engineering*, 17(3), 259-273.

6. **Desel, J., & Esparza, J.** (1995). *Free choice Petri nets*. Cambridge University Press.

7. **Silva, M.** (1993). *Las redes de Petri en la ingeniería de sistemas*. Universidad de Zaragoza.

---

**文档版本**: 1.0  
**最后更新**: 2024-12-19  
**作者**: 形式科学理论体系重构项目  
**许可证**: 学术开放许可
