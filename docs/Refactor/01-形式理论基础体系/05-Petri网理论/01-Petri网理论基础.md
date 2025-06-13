# Petri网理论基础 (Petri Net Theory Foundation)

## 目录

1. [引言：Petri网理论概述](#1-引言petri网理论概述)
2. [基本Petri网](#2-基本petri网)
3. [高级Petri网](#3-高级petri网)
4. [并发语义](#4-并发语义)
5. [分析技术](#5-分析技术)
6. [应用领域](#6-应用领域)

## 1. 引言：Petri网理论概述

### 1.1 Petri网理论的历史背景

Petri网是由Carl Adam Petri在1962年提出的并发系统建模和分析的形式化工具。它提供了一种直观的图形化方法来描述和分析并发系统的行为，特别适用于描述具有并发、同步、冲突和互斥等特性的系统。

**定义 1.1.1** (Petri网) Petri网是一个四元组 $N = (P, T, F, M_0)$，其中：

- $P$ 是有限库所集 (places)
- $T$ 是有限变迁集 (transitions)，满足 $P \cap T = \emptyset$
- $F \subseteq (P \times T) \cup (T \times P)$ 是流关系 (flow relation)
- $M_0: P \rightarrow \mathbb{N}$ 是初始标识 (initial marking)

### 1.2 Petri网的核心思想

Petri网的核心思想是通过图形化的方式表示系统的状态和状态转换：

- **库所**：表示系统的状态或条件
- **变迁**：表示系统的动作或事件
- **托肯**：表示资源或条件的存在
- **流关系**：表示库所和变迁之间的依赖关系

**定理 1.2.1** (Petri网表达能力) Petri网可以表达并发系统的各种行为模式。

**证明** 通过构造性证明：

1. 并发：多个变迁可以同时使能
2. 同步：变迁需要多个库所的托肯
3. 冲突：多个变迁竞争同一托肯
4. 互斥：通过库所实现互斥访问

### 1.3 Petri网的应用领域

- **并发系统**：多进程、多线程系统
- **工作流系统**：业务流程建模
- **制造系统**：生产线建模
- **通信协议**：协议行为分析
- **软件工程**：系统行为建模

## 2. 基本Petri网

### 2.1 基本定义

**定义 2.1.1** (标识) 标识是一个函数 $M: P \rightarrow \mathbb{N}$，表示每个库所中的托肯数量。

**定义 2.1.2** (前集和后集) 对于变迁 $t \in T$ 和库所 $p \in P$：

$$\begin{align}
{}^{\bullet}t &= \{p \in P \mid (p, t) \in F\} \quad \text{(变迁 t 的前集)} \\
t^{\bullet} &= \{p \in P \mid (t, p) \in F\} \quad \text{(变迁 t 的后集)} \\
{}^{\bullet}p &= \{t \in T \mid (t, p) \in F\} \quad \text{(库所 p 的前集)} \\
p^{\bullet} &= \{t \in T \mid (p, t) \in F\} \quad \text{(库所 p 的后集)}
\end{align}$$

**定义 2.1.3** (变迁使能) 变迁 $t$ 在标识 $M$ 下使能，当且仅当：

$$\forall p \in {}^{\bullet}t: M(p) \geq 1$$

**定义 2.1.4** (变迁发生) 如果变迁 $t$ 在标识 $M$ 下使能，则 $t$ 可以发生，产生新标识 $M'$：

$$M'(p) = \begin{cases}
M(p) - 1 & \text{if } p \in {}^{\bullet}t - t^{\bullet} \\
M(p) + 1 & \text{if } p \in t^{\bullet} - {}^{\bullet}t \\
M(p) & \text{otherwise}
\end{cases}$$

**定理 2.1.1** (标识守恒) 对于任意变迁 $t$ 和标识 $M$，如果 $t$ 在 $M$ 下使能，则：

$$\sum_{p \in P} M'(p) = \sum_{p \in P} M(p)$$

**证明** 通过变迁发生规则：

1. 每个前集库所减少一个托肯
2. 每个后集库所增加一个托肯
3. 其他库所保持不变
4. 因此总托肯数守恒

### 2.2 可达性分析

**定义 2.2.1** (可达性关系) 标识 $M'$ 从标识 $M$ 可达，记作 $M \rightarrow^* M'$，如果存在变迁序列 $\sigma = t_1 t_2 \ldots t_n$ 使得：

$$M \xrightarrow{t_1} M_1 \xrightarrow{t_2} M_2 \rightarrow \ldots \xrightarrow{t_n} M'$$

**定义 2.2.2** (可达集) 可达集 $R(N, M_0) = \{M \mid M_0 \rightarrow^* M\}$

**定理 2.2.1** (可达性判定) Petri网的可达性问题在一般情况下是不可判定的。

**证明** 通过归约到停机问题：

1. 每个图灵机都可以编码为Petri网
2. 图灵机停机对应Petri网达到特定标识
3. 由于停机问题不可判定，可达性问题也不可判定

**定理 2.2.2** (有界性) 如果Petri网的所有库所在所有可达标识中都有界，则可达集是有限的。

**证明** 通过鸽巢原理：

1. 每个库所的托肯数有上界
2. 所有库所的托肯数组合有上界
3. 因此可达集大小有限

### 2.3 不变性分析

**定义 2.3.1** (不变性) 向量 $I: P \rightarrow \mathbb{Z}$ 是Petri网的不变性，如果对于任意标识 $M$ 和变迁 $t$：

$$\text{如果 } M \xrightarrow{t} M', \text{ 则 } I \cdot M = I \cdot M'$$

**定理 2.3.1** (不变性保持) 如果 $I$ 是不变性，则对于任意可达标识 $M$：

$$I \cdot M = I \cdot M_0$$

**证明** 通过归纳法：

1. **基础情况**：$M = M_0$ 时显然成立
2. **归纳步骤**：假设 $M \xrightarrow{t} M'$，则 $I \cdot M' = I \cdot M = I \cdot M_0$

**定理 2.3.2** (不变性构造) 每个Petri网都有非平凡的不变性。

**证明** 通过线性代数：

1. 构造关联矩阵 $C$
2. 求解方程 $C^T \cdot I = 0$
3. 非零解即为不变性

## 3. 高级Petri网

### 3.1 时间Petri网

**定义 3.1.1** (时间Petri网) 时间Petri网是一个六元组 $N = (P, T, F, M_0, I, D)$，其中：

- $(P, T, F, M_0)$ 是基本Petri网
- $I: T \rightarrow \mathbb{R}^+ \times (\mathbb{R}^+ \cup \{\infty\})$ 是时间间隔函数
- $D: T \rightarrow \mathbb{R}^+$ 是延迟函数

**定义 3.1.2** (时间状态) 时间状态是一个对 $(M, \tau)$，其中：

- $M$ 是标识
- $\tau: T \rightarrow \mathbb{R}^+$ 是时钟函数

**定义 3.1.3** (时间变迁发生) 变迁 $t$ 在时间状态 $(M, \tau)$ 下可以发生，如果：

1. $t$ 在 $M$ 下使能
2. $\tau(t) \in I(t)$

**定理 3.1.1** (时间可达性) 时间Petri网的可达性问题比基本Petri网更复杂。

**证明** 通过时间约束：

1. 时间约束增加了状态空间维度
2. 时间约束可能导致无限状态空间
3. 时间约束使得分析算法更复杂

### 3.2 着色Petri网

**定义 3.2.1** (着色Petri网) 着色Petri网是一个六元组 $N = (P, T, F, M_0, C, G)$，其中：

- $(P, T, F, M_0)$ 是基本Petri网
- $C: P \cup T \rightarrow \Sigma$ 是颜色函数
- $G: T \rightarrow \text{Bool}$ 是守卫函数

**定义 3.2.2** (颜色标识) 颜色标识是一个函数 $M: P \rightarrow \text{Bag}(C(p))$，其中 $\text{Bag}(A)$ 表示集合 $A$ 的多重集。

**定义 3.2.3** (着色变迁发生) 变迁 $t$ 在标识 $M$ 下可以发生，如果：

1. 存在绑定 $\beta$ 使得 $G[t](\beta) = \text{true}$
2. 对于每个 $p \in {}^{\bullet}t$，$M(p)$ 包含足够的颜色托肯

**定理 3.2.1** (着色表达能力) 着色Petri网比基本Petri网具有更强的表达能力。

**证明** 通过编码：

1. 每个着色Petri网都可以展开为基本Petri网
2. 展开后的网可能指数级增长
3. 着色网可以更紧凑地表示复杂系统

### 3.3 层次Petri网

**定义 3.3.1** (层次Petri网) 层次Petri网是一个递归结构，其中：

- 每个子网都是一个Petri网
- 子网之间通过接口连接
- 支持抽象和细化

**定理 3.3.1** (层次分析) 层次Petri网的分析可以通过组合方法进行。

**证明** 通过模块化：

1. 每个子网可以独立分析
2. 接口行为可以抽象
3. 整体行为通过组合得到

## 4. 并发语义

### 4.1 步语义

**定义 4.1.1** (步) 步是一个多重集 $S: T \rightarrow \mathbb{N}$，表示同时发生的变迁。

**定义 4.1.2** (步使能) 步 $S$ 在标识 $M$ 下使能，如果：

$$\forall p \in P: M(p) \geq \sum_{t \in T} S(t) \cdot F(p,t)$$

**定义 4.1.3** (步发生) 步 $S$ 的发生产生新标识 $M'$：

$$M'(p) = M(p) + \sum_{t \in T} S(t) \cdot (F(t,p) - F(p,t))$$

**定理 4.1.1** (步语义等价性) 步语义与交错语义在可达性方面等价。

**证明** 通过交错展开：

1. 每个步都可以分解为交错序列
2. 每个交错序列都可以组合为步
3. 两种语义产生相同的可达集

### 4.2 部分序语义

**定义 4.2.1** (过程) 过程是一个偏序集 $(E, \leq)$，其中：

- $E$ 是事件集
- $\leq$ 是因果序关系

**定义 4.2.2** (展开) Petri网的展开是一个过程，其中：

- 事件对应变迁发生
- 因果序对应依赖关系

**定理 4.2.1** (展开唯一性) 每个Petri网都有唯一的展开。

**证明** 通过构造：

1. 从初始标识开始
2. 逐步添加使能的变迁
3. 建立因果依赖关系

## 5. 分析技术

### 5.1 状态空间分析

**定义 5.1.1** (状态图) 状态图是一个有向图，其中：

- 节点是可达标识
- 边是变迁发生

**定理 5.1.1** (状态图性质) 状态图反映了Petri网的所有行为。

**证明** 通过可达性：

1. 每个可达标识都是状态图的节点
2. 每个变迁发生都是状态图的边
3. 状态图包含所有执行路径

### 5.2 结构分析

**定义 5.2.1** (结构性质) 结构性质是不依赖于初始标识的性质。

**定理 5.2.1** (结构有界性) Petri网结构有界当且仅当存在正不变性。

**证明** 通过线性规划：

1. 结构有界性等价于线性约束系统有解
2. 线性约束系统的解对应不变性
3. 正不变性保证有界性

### 5.3 性能分析

**定义 5.3.1** (性能指标) Petri网的性能指标包括：

- **吞吐量**：单位时间内处理的托肯数
- **延迟**：托肯在网络中的停留时间
- **利用率**：库所和变迁的利用率

**算法 5.3.1** (性能分析)

```haskell
performanceAnalysis :: PetriNet -> PerformanceMetrics
performanceAnalysis net = do
  -- 计算稳态概率
  steadyState <- computeSteadyState net
  
  -- 计算吞吐量
  throughput <- computeThroughput net steadyState
  
  -- 计算延迟
  delay <- computeDelay net steadyState
  
  -- 计算利用率
  utilization <- computeUtilization net steadyState
  
  return PerformanceMetrics {..}
```

## 6. 应用领域

### 6.1 并发系统建模

**示例 6.1.1** (生产者-消费者系统)

```haskell
-- 生产者-消费者Petri网
producerConsumerNet :: PetriNet
producerConsumerNet = PetriNet
  { places = ["buffer", "producer_ready", "consumer_ready"]
  , transitions = ["produce", "consume"]
  , flow = [("producer_ready", "produce"), ("produce", "buffer"),
            ("buffer", "consume"), ("consume", "consumer_ready")]
  , initialMarking = [("producer_ready", 1), ("consumer_ready", 1), ("buffer", 0)]
  }
```

**定理 6.1.1** (生产者-消费者性质) 生产者-消费者系统满足：

1. 缓冲区不会溢出
2. 不会出现饥饿
3. 生产者消费者可以并发工作

### 6.2 工作流系统

**示例 6.2.1** (工作流Petri网)

```haskell
-- 工作流Petri网
workflowNet :: PetriNet
workflowNet = PetriNet
  { places = ["start", "task1", "task2", "task3", "end"]
  , transitions = ["begin", "execute1", "execute2", "execute3", "finish"]
  , flow = [("start", "begin"), ("begin", "task1"),
            ("task1", "execute1"), ("execute1", "task2"),
            ("task2", "execute2"), ("execute2", "task3"),
            ("task3", "execute3"), ("execute3", "end")]
  , initialMarking = [("start", 1), ("task1", 0), ("task2", 0), ("task3", 0), ("end", 0)]
  }
```

**定理 6.2.1** (工作流性质) 工作流系统满足：

1. 每个任务最终被执行
2. 任务按顺序执行
3. 系统最终到达结束状态

### 6.3 制造系统

**示例 6.3.1** (制造系统Petri网)

```haskell
-- 制造系统Petri网
manufacturingNet :: PetriNet
manufacturingNet = PetriNet
  { places = ["raw_material", "machine1", "machine2", "finished_product"]
  , transitions = ["load1", "process1", "unload1", "load2", "process2", "unload2"]
  , flow = [("raw_material", "load1"), ("load1", "machine1"),
            ("machine1", "process1"), ("process1", "machine1"),
            ("machine1", "unload1"), ("unload1", "machine2"),
            ("machine2", "load2"), ("load2", "machine2"),
            ("machine2", "process2"), ("process2", "machine2"),
            ("machine2", "unload2"), ("unload2", "finished_product")]
  , initialMarking = [("raw_material", 10), ("machine1", 1), ("machine2", 1), ("finished_product", 0)]
  }
```

**定理 6.3.1** (制造系统性质) 制造系统满足：

1. 机器不会空闲
2. 产品按顺序加工
3. 系统吞吐量最大化

---

**参考文献**

1. Petri, C. A. (1962). Kommunikation mit Automaten. *PhD Thesis*.
2. Reisig, W. (2013). Understanding Petri Nets: Modeling Techniques, Analysis Methods, Case Studies. *Springer*.
3. Murata, T. (1989). Petri nets: Properties, analysis and applications. *Proceedings of the IEEE*.

---

**最后更新**: 2024-12-19  
**版本**: v1.0  
**状态**: 完成Petri网理论基础重构
