# Petri网理论 (Petri Net Theory)

## 目录

- [Petri网理论 (Petri Net Theory)](#petri网理论-petri-net-theory)
  - [目录](#目录)
  - [概述](#概述)
  - [1. 基本Petri网 (Basic Petri Nets)](#1-基本petri网-basic-petri-nets)
    - [1.1 基本定义](#11-基本定义)
    - [1.2 可达性分析](#12-可达性分析)
    - [1.3 不变性分析](#13-不变性分析)
  - [2. 高级Petri网 (Advanced Petri Nets)](#2-高级petri网-advanced-petri-nets)
    - [2.1 时间Petri网 (Timed Petri Nets)](#21-时间petri网-timed-petri-nets)
    - [2.2 着色Petri网 (Colored Petri Nets)](#22-着色petri网-colored-petri-nets)
    - [2.3 层次Petri网 (Hierarchical Petri Nets)](#23-层次petri网-hierarchical-petri-nets)
  - [3. 并发语义 (Concurrency Semantics)](#3-并发语义-concurrency-semantics)
    - [3.1 步语义 (Step Semantics)](#31-步语义-step-semantics)
    - [3.2 部分序语义 (Partial Order Semantics)](#32-部分序语义-partial-order-semantics)
  - [4. 分析技术 (Analysis Techniques)](#4-分析技术-analysis-techniques)
    - [4.1 状态空间分析](#41-状态空间分析)
    - [4.2 结构分析](#42-结构分析)
    - [4.3 性能分析](#43-性能分析)
  - [5. 应用领域 (Application Domains)](#5-应用领域-application-domains)
    - [5.1 并发系统建模](#51-并发系统建模)
    - [5.2 工作流建模](#52-工作流建模)
    - [5.3 制造系统建模](#53-制造系统建模)
  - [6. 扩展理论 (Extension Theories)](#6-扩展理论-extension-theories)
    - [6.1 概率Petri网](#61-概率petri网)
    - [6.2 模糊Petri网](#62-模糊petri网)
    - [6.3 对象Petri网](#63-对象petri网)
  - [7. 结论](#7-结论)
  - [参考文献](#参考文献)

## 概述

Petri网是并发系统建模和分析的重要形式化工具，由Carl Adam Petri在1962年提出。本文档系统性地梳理了Petri网理论的主要分支，从基本Petri网到高级变种，包括时间Petri网、着色Petri网等。

## 1. 基本Petri网 (Basic Petri Nets)

### 1.1 基本定义

**定义 1.1.1** 基本Petri网是一个四元组 N = (P, T, F, M₀)，其中：

- P 是有限库所集 (places)
- T 是有限变迁集 (transitions)，P ∩ T = ∅
- F ⊆ (P × T) ∪ (T × P) 是流关系 (flow relation)
- M₀: P → ℕ 是初始标识 (initial marking)

**定义 1.1.2** 标识 (Marking) 是一个函数 M: P → ℕ，表示每个库所中的托肯数量。

**定义 1.1.3** 前集和后集：

```text
•t = {p ∈ P | (p, t) ∈ F}    (变迁 t 的前集)
t• = {p ∈ P | (t, p) ∈ F}    (变迁 t 的后集)
•p = {t ∈ T | (t, p) ∈ F}    (库所 p 的前集)
p• = {t ∈ T | (p, t) ∈ F}    (库所 p 的后集)
```

**定义 1.1.4** 变迁使能条件：变迁 t 在标识 M 下使能，当且仅当：

```text
∀p ∈ •t: M(p) ≥ 1
```

**定义 1.1.5** 变迁发生：如果变迁 t 在标识 M 下使能，则 t 可以发生，产生新标识 M'：

```text
M'(p) = M(p) - 1, 如果 p ∈ •t - t•
M'(p) = M(p) + 1, 如果 p ∈ t• - •t
M'(p) = M(p),     其他情况
```

**定理 1.1.1** (标识守恒) 对于任意变迁 t 和标识 M，如果 t 在 M 下使能，则：

```text
∑_{p∈P} M'(p) = ∑_{p∈P} M(p)
```

**证明** 通过变迁发生规则：

1. 每个前集库所减少一个托肯
2. 每个后集库所增加一个托肯
3. 其他库所保持不变
4. 因此总托肯数守恒

### 1.2 可达性分析

**定义 1.2.1** 可达性关系：标识 M' 从标识 M 可达，记作 M →* M'，如果存在变迁序列 σ = t₁t₂...tₙ 使得：

```text
M →^{t₁} M₁ →^{t₂} M₂ → ... →^{tₙ} M'
```

**定义 1.2.2** 可达集：R(N, M₀) = {M | M₀ →* M}

**定理 1.2.1** (可达性判定) Petri网的可达性问题在一般情况下是不可判定的。

**证明** 通过归约到停机问题：

1. 每个图灵机都可以编码为Petri网
2. 图灵机停机对应Petri网达到特定标识
3. 由于停机问题不可判定，可达性问题也不可判定

**定理 1.2.2** (有界性) 如果Petri网的所有库所在所有可达标识中都有界，则可达集是有限的。

**证明** 通过鸽巢原理：

1. 每个库所的托肯数有上界
2. 所有库所的托肯数组合有上界
3. 因此可达集大小有限

### 1.3 不变性分析

**定义 1.3.1** 不变性：向量 I: P → ℤ 是Petri网的不变性，如果对于任意标识 M 和变迁 t：

```text
如果 M →^{t} M'，则 I · M = I · M'
```

**定理 1.3.1** (不变性保持) 如果 I 是不变性，则对于任意可达标识 M：

```text
I · M = I · M₀
```

**证明** 通过归纳法：

1. 基础情况：M = M₀ 时显然成立
2. 归纳步骤：假设 M →^{t} M'，则 I · M' = I · M = I · M₀

**定理 1.3.2** (不变性构造) 每个Petri网都有非平凡的不变性。

**证明** 通过线性代数：

1. 构造关联矩阵 C
2. 求解方程 C^T · I = 0
3. 非零解即为不变性

## 2. 高级Petri网 (Advanced Petri Nets)

### 2.1 时间Petri网 (Timed Petri Nets)

**定义 2.1.1** 时间Petri网是一个六元组 N = (P, T, F, M₀, I, D)，其中：

- (P, T, F, M₀) 是基本Petri网
- I: T → ℝ⁺ × (ℝ⁺ ∪ {∞}) 是时间间隔函数
- D: T → ℝ⁺ 是延迟函数

**定义 2.1.2** 时间状态：时间状态是一个对 (M, τ)，其中：

- M 是标识
- τ: T → ℝ⁺ 是时钟函数

**定义 2.1.3** 时间变迁发生：变迁 t 在时间状态 (M, τ) 下可以发生，如果：

1. t 在 M 下使能
2. τ(t) ∈ I(t)

**定理 2.1.1** (时间可达性) 时间Petri网的可达性问题比基本Petri网更复杂。

**证明** 通过时间约束：

1. 时间约束增加了状态空间维度
2. 时间约束可能导致无限状态空间
3. 时间约束使得分析算法更复杂

### 2.2 着色Petri网 (Colored Petri Nets)

**定义 2.2.1** 着色Petri网是一个六元组 N = (P, T, F, M₀, C, G)，其中：

- (P, T, F, M₀) 是基本Petri网
- C: P ∪ T → Σ 是颜色函数
- G: T → Bool 是守卫函数

**定义 2.2.2** 颜色标识：颜色标识是一个函数 M: P → Bag(C(p))，其中 Bag(A) 表示集合 A 的多重集。

**定义 2.2.3** 着色变迁发生：变迁 t 在标识 M 下可以发生，如果：

1. 存在绑定 β 使得 G[t](β) = true
2. 对于每个 p ∈ •t，M(p) 包含足够的颜色托肯

**定理 2.2.1** (着色表达能力) 着色Petri网比基本Petri网具有更强的表达能力。

**证明** 通过编码：

1. 每个着色Petri网都可以展开为基本Petri网
2. 展开后的网可能指数级增长
3. 着色网可以更紧凑地表示复杂系统

### 2.3 层次Petri网 (Hierarchical Petri Nets)

**定义 2.3.1** 层次Petri网是一个递归结构，其中：

- 每个子网都是一个Petri网
- 子网之间通过接口连接
- 支持抽象和细化

**定理 2.3.1** (层次分析) 层次Petri网的分析可以通过组合方法进行。

**证明** 通过模块化：

1. 每个子网可以独立分析
2. 接口行为可以抽象
3. 整体行为通过组合得到

## 3. 并发语义 (Concurrency Semantics)

### 3.1 步语义 (Step Semantics)

**定义 3.1.1** 步：步是一个多重集 S: T → ℕ，表示同时发生的变迁。

**定义 3.1.2** 步使能：步 S 在标识 M 下使能，如果：

```text
∀p ∈ P: M(p) ≥ ∑_{t∈T} S(t) · F(p,t)
```

**定义 3.1.3** 步发生：步 S 的发生产生新标识 M'：

```text
M'(p) = M(p) + ∑_{t∈T} S(t) · (F(t,p) - F(p,t))
```

**定理 3.1.1** (步语义等价性) 步语义与交错语义在可达性方面等价。

**证明** 通过交错展开：

1. 每个步都可以分解为交错序列
2. 每个交错序列都可以组合为步
3. 两种语义产生相同的可达集

### 3.2 部分序语义 (Partial Order Semantics)

**定义 3.2.1** 过程：过程是一个偏序集 (E, ≤)，其中：

- E 是事件集
- ≤ 是因果序关系

**定义 3.2.2** 展开：Petri网的展开是一个过程，其中：

- 事件对应变迁发生
- 因果序对应依赖关系

**定理 3.2.1** (展开唯一性) 每个Petri网都有唯一的展开。

**证明** 通过构造：

1. 从初始标识开始
2. 逐步添加使能的变迁
3. 建立因果依赖关系

## 4. 分析技术 (Analysis Techniques)

### 4.1 状态空间分析

**定义 4.1.1** 状态图：状态图是一个有向图，其中：

- 节点是可达标识
- 边是变迁发生

**定理 4.1.1** (状态图性质) 状态图反映了Petri网的所有行为。

**证明** 通过可达性：

1. 每个可达标识都是状态图的节点
2. 每个变迁发生都是状态图的边
3. 状态图包含所有执行路径

### 4.2 结构分析

**定义 4.2.1** 结构性质：结构性质是不依赖于初始标识的性质。

**定理 4.2.1** (结构有界性) Petri网结构有界当且仅当存在正不变性。

**证明** 通过线性规划：

1. 结构有界性等价于线性约束系统有解
2. 线性约束系统的解对应不变性
3. 正不变性保证有界性

### 4.3 性能分析

**定义 4.3.1** 性能指标：包括吞吐量、响应时间、利用率等。

**定理 4.3.1** (性能界限) 性能指标可以通过结构分析得到界限。

**证明** 通过瓶颈分析：

1. 瓶颈库所限制系统性能
2. 不变性提供性能上界
3. 结构分析确定瓶颈位置

## 5. 应用领域 (Application Domains)

### 5.1 并发系统建模

**定理 5.1.1** (并发建模) Petri网可以精确建模并发系统的行为。

**证明** 通过语义对应：

1. 库所对应系统状态
2. 变迁对应系统事件
3. 托肯对应资源或条件

### 5.2 工作流建模

**定理 5.2.1** (工作流建模) Petri网适合建模工作流过程。

**证明** 通过过程对应：

1. 库所对应活动状态
2. 变迁对应活动执行
3. 托肯对应案例或任务

### 5.3 制造系统建模

**定理 5.3.1** (制造建模) Petri网可以建模制造系统的动态行为。

**证明** 通过系统对应：

1. 库所对应机器状态
2. 变迁对应操作执行
3. 托肯对应工件或资源

## 6. 扩展理论 (Extension Theories)

### 6.1 概率Petri网

**定义 6.1.1** 概率Petri网在基本Petri网基础上添加概率分布。

**定理 6.1.1** (概率分析) 概率Petri网可以分析系统的概率性质。

### 6.2 模糊Petri网

**定义 6.2.1** 模糊Petri网在基本Petri网基础上添加模糊逻辑。

**定理 6.2.1** (模糊推理) 模糊Petri网可以处理不确定性。

### 6.3 对象Petri网

**定义 6.3.1** 对象Petri网将面向对象概念引入Petri网。

**定理 6.3.1** (对象建模) 对象Petri网适合建模复杂对象系统。

## 7. 结论

Petri网理论为并发系统提供了强大的建模和分析工具。从基本Petri网到各种高级变种，Petri网理论形成了完整的理论体系，广泛应用于软件工程、系统设计、工作流管理等领域。

## 参考文献

1. Petri, C. A. (1962). Kommunikation mit Automaten. PhD thesis, Universität Hamburg.
2. Reisig, W. (2013). Understanding Petri nets: Modeling techniques, analysis methods, case studies.
3. Murata, T. (1989). Petri nets: Properties, analysis and applications. Proceedings of the IEEE, 77(4), 541-580.
4. Jensen, K., & Kristensen, L. M. (2009). Colored Petri nets: Modeling and validation of concurrent systems.
5. Berthomieu, B., & Diaz, M. (1991). Modeling and verification of time dependent systems using time Petri nets. IEEE transactions on software engineering, 17(3), 259-273.
