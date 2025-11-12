# 形式科学理论体系 - 术语表

> **文档版本**: v1.0.0
> **最后更新**: 2025-10-25
> **术语总数**: 120+
> **覆盖范围**: 七大视角核心术语

---


---

## 📋 目录

- [形式科学理论体系 - 术语表](#形式科学理论体系---术语表)
  - [1 📋 快速导航](#1-快速导航)
  - [2 按字母索引](#2-按字母索引)
  - [按字母索引](#按字母索引)
    - [2.1 A](#21-a)
      - [2.1.1 AGI (Artificial General Intelligence)](#211-agi-artificial-general-intelligence)
      - [2.1.2 Ashby必要多样性定律 (Ashby's Law of Requisite Variety)](#212-ashby必要多样性定律-ashbys-law-of-requisite-variety)
    - [2.2 B](#22-b)
      - [2.2.1 BFT (Byzantine Fault Tolerance)](#221-bft-byzantine-fault-tolerance)
      - [2.2.2 BQP (Bounded-Error Quantum Polynomial Time)](#222-bqp-bounded-error-quantum-polynomial-time)
    - [2.3 C](#23-c)
      - [2.3.1 CAP定理 (CAP Theorem)](#231-cap定理-cap-theorem)
      - [2.3.2 Chomsky层级 (Chomsky Hierarchy)](#232-chomsky层级-chomsky-hierarchy)
    - [2.4 D](#24-d)
      - [2.4.1 Data Rate定理 (Data Rate Theorem)](#241-data-rate定理-data-rate-theorem)
      - [2.4.2 DIKWP模型](#242-dikwp模型)
    - [2.5 E](#25-e)
      - [2.5.1 Entropy (熵)](#251-entropy-熵)
    - [2.6 F](#26-f)
      - [2.6.1 FLP不可能定理 (FLP Impossibility Theorem)](#261-flp不可能定理-flp-impossibility-theorem)
      - [2.6.2 反身性 (Reflexivity)](#262-反身性-reflexivity)
    - [2.7 G](#27-g)
      - [2.7.1 Gödel不完备定理 (Gödel's Incompleteness Theorems)](#271-gödel不完备定理-gödels-incompleteness-theorems)
      - [2.7.2 Gold可学习性 (Gold Learnability Theory)](#272-gold可学习性-gold-learnability-theory)
    - [2.8 H](#28-h)
      - [2.8.1 停机问题 (Halting Problem)](#281-停机问题-halting-problem)
    - [2.9 I](#29-i)
      - [2.9.1 隔离 (Isolation)](#291-隔离-isolation)
      - [2.9.2 互信息 (Mutual Information)](#292-互信息-mutual-information)
    - [2.10 K](#210-k)
      - [2.10.1 Kolmogorov复杂度 (Kolmogorov Complexity)](#2101-kolmogorov复杂度-kolmogorov-complexity)
    - [2.11 L](#211-l)
      - [2.11.1 Landauer极限 (Landauer Limit)](#2111-landauer极限-landauer-limit)
    - [2.12 M](#212-m)
      - [2.12.1 Meta-learning (元学习)](#2121-meta-learning-元学习)
      - [2.12.2 冯·诺依曼瓶颈 (Von Neumann Bottleneck)](#2122-冯诺依曼瓶颈-von-neumann-bottleneck)
    - [2.13 P](#213-p)
      - [2.13.1 PAC学习 (Probably Approximately Correct Learning)](#2131-pac学习-probably-approximately-correct-learning)
      - [2.13.2 P vs NP问题](#2132-p-vs-np问题)
      - [2.13.3 Popek-Goldberg定理](#2133-popek-goldberg定理)
    - [2.14 R](#214-r)
      - [2.14.1 Rice定理 (Rice's Theorem)](#2141-rice定理-rices-theorem)
    - [2.15 S](#215-s)
      - [2.15.1 三票理论 (Three Tickets Theory)](#2151-三票理论-three-tickets-theory)
      - [2.15.2 Shannon熵 (Shannon Entropy)](#2152-shannon熵-shannon-entropy)
      - [2.15.3 主权矩阵 (Sovereignty Matrix)](#2153-主权矩阵-sovereignty-matrix)
    - [2.16 T](#216-t)
      - [2.16.1 图灵完备性 (Turing Completeness)](#2161-图灵完备性-turing-completeness)
      - [2.16.2 三元视角 (Triadic Perspective)](#2162-三元视角-triadic-perspective)
    - [2.17 U](#217-u)
      - [2.17.1 UH-Cost 统一元模型](#2171-uh-cost-统一元模型)
    - [2.18 V](#218-v)
      - [2.18.1 VC维 (Vapnik-Chervonenkis Dimension)](#2181-vc维-vapnik-chervonenkis-dimension)
      - [2.18.2 虚拟化 (Virtualization)](#2182-虚拟化-virtualization)
    - [2.19 X](#219-x)
      - [2.19.1 形式语言 (Formal Language)](#2191-形式语言-formal-language)
  - [3 按视角分类](#3-按视角分类)
    - [3.1 形式语言视角](#31-形式语言视角)
    - [3.2 AI模型视角](#32-ai模型视角)
    - [3.3 信息论视角](#33-信息论视角)
    - [3.4 图灵可计算视角](#34-图灵可计算视角)
    - [3.5 控制论视角](#35-控制论视角)
    - [3.6 冯·诺依曼架构视角](#36-冯诺依曼架构视角)
    - [3.7 分布式系统视角](#37-分布式系统视角)
    - [3.8 编程算法设计视角 ✨](#38-编程算法设计视角-)
  - [4 核心术语 (Top 50)](#4-核心术语-top-50)
  - [5 缩写表](#5-缩写表)
  - [6 补充说明](#6-补充说明)
    - [6.1 如何使用本术语表](#61-如何使用本术语表)
    - [6.2 术语说明规范](#62-术语说明规范)
    - [6.3 持续更新](#63-持续更新)
  - [7 相关资源](#7-相关资源)

---

## 1 📋 快速导航

- [按字母索引](#按字母索引)
- [按视角分类](#按视角分类)
- [核心术语](#核心术语-top-50)
- [缩写表](#缩写表)

---

## 2 按字母索引

### 2.1 A

#### 2.1.1 AGI (Artificial General Intelligence)

- 中文：通用人工智能
- 定义：能够在任何智力任务上达到或超过人类水平的AI系统
- 视角：AI模型、形式语言、控制论
- 相关：AI对齐问题, [图灵完备性](#图灵完备性-turing-completeness)

#### 2.1.2 Ashby必要多样性定律 (Ashby's Law of Requisite Variety)

- 定义：V_controller ≥ V_system（控制器复杂度必须≥被控系统）
- 视角：控制论（核心）
- 详见：[CONCEPT_CROSS_INDEX.md](CONCEPT_CROSS_INDEX.md#ashby必要多样性定律-ashbys-law-of-requisite-variety-七视角)

### 2.2 B

#### 2.2.1 BFT (Byzantine Fault Tolerance)

- 中文：拜占庭容错
- 定义：系统能容忍拜占庭错误（恶意节点）的能力
- 公式：n ≥ 3f + 1（n个节点容忍f个恶意节点）
- 视角：分布式系统（核心）
- 相关：[FLP不可能定理](#flp不可能定理-flp-impossibility-theorem), 共识算法（Paxos, Raft, PBFT）

#### 2.2.2 BQP (Bounded-Error Quantum Polynomial Time)

- 中文：有界误差量子多项式时间
- 定义：量子计算机在多项式时间内可解的问题类
- 视角：计算理论、量子计算
- 相关：[P vs NP](#p-vs-np问题), 量子计算

### 2.3 C

#### 2.3.1 CAP定理 (CAP Theorem)

- 定义：C(一致性) ∧ A(可用性) ∧ P(分区容错)不可兼得
- 视角：分布式系统（核心）、信息论
- 详见：[CONCEPT_CROSS_INDEX.md](CONCEPT_CROSS_INDEX.md#cap定理-cap-theorem-七视角)

#### 2.3.2 Chomsky层级 (Chomsky Hierarchy)

- 定义：形式语言的四层分类（TYPE-0到TYPE-3）
- 映射：RE ⊃ CSL ⊃ CFL ⊃ REG
- 视角：形式语言（核心）、AI模型
- 详见：[CONCEPT_CROSS_INDEX.md](CONCEPT_CROSS_INDEX.md#chomsky层级-chomsky-hierarchy-七视角)

### 2.4 D

#### 2.4.1 Data Rate定理 (Data Rate Theorem)

- 定义：R ≥ Σlog₂λᵢ（信息速率下界）
- 视角：控制论（核心）、信息论
- 详见：[CONCEPT_CROSS_INDEX.md](CONCEPT_CROSS_INDEX.md#data-rate定理-data-rate-theorem-七视角)

#### 2.4.2 DIKWP模型

- 定义：数据(D)→信息(I)→知识(K)→智慧(W)→目的(P)
- 视角：信息论、AI模型、形式语言
- 详见：[CONCEPT_CROSS_INDEX.md](CONCEPT_CROSS_INDEX.md#dikwp模型-七视角)

### 2.5 E

#### 2.5.1 Entropy (熵)

- 定义：H(X) = -Σ p(x)log p(x)（不确定性度量）
- 视角：信息论（核心）、控制论、分布式
- 详见：[CONCEPT_CROSS_INDEX.md](CONCEPT_CROSS_INDEX.md#熵-entropy-七视角)

### 2.6 F

#### 2.6.1 FLP不可能定理 (FLP Impossibility Theorem)

- 定义：异步网络中不存在同时满足一致性、终止性、容错性的共识协议
- 视角：分布式系统（核心）
- 详见：[CONCEPT_CROSS_INDEX.md](CONCEPT_CROSS_INDEX.md#flp不可能定理-flp-impossibility-theorem-七视角)

#### 2.6.2 反身性 (Reflexivity)

- 定义：系统重写自身规则的能力
- 形式化：公理A5: ⟦φ⟧ ∈ 𝒮 → ∃ψ. ⟦ψ⟧ = ⟦φ⟧
- 视角：七视角通用核心概念
- 详见：[CONCEPT_CROSS_INDEX.md](CONCEPT_CROSS_INDEX.md#反身性-reflexivity-七视角)

### 2.7 G

#### 2.7.1 Gödel不完备定理 (Gödel's Incompleteness Theorems)

- 第一定理：任何一致的、足够强的形式系统都包含不可证命题
- 第二定理：系统无法证明自身一致性
- 视角：形式语言（核心）、AI模型、图灵可计算
- 详见：[CONCEPT_CROSS_INDEX.md](CONCEPT_CROSS_INDEX.md#gödel不完备定理-gödels-incompleteness-theorems-七视角)

#### 2.7.2 Gold可学习性 (Gold Learnability Theory)

- 定义：从正例（或完全文本）在极限意义下学习语言类的理论
- 核心结果：超限类不可从正例学习
- 视角：AI模型（核心）、形式语言
- 详见：[CONCEPT_CROSS_INDEX.md](CONCEPT_CROSS_INDEX.md#gold可学习性-gold-learnability-theory-七视角)

### 2.8 H

#### 2.8.1 停机问题 (Halting Problem)

- 定义：判定任意程序是否停机是不可判定的
- 证明：对角线论证（Cantor, Gödel, Turing）
- 视角：图灵可计算（核心）、形式语言
- 详见：[CONCEPT_CROSS_INDEX.md](CONCEPT_CROSS_INDEX.md#停机问题-halting-problem-七视角)

### 2.9 I

#### 2.9.1 隔离 (Isolation)

- 定义：系统间信息流受控的性质
- 度量：隔离熵 H_isolation = H(S₁|S₂)
- 视角：图灵可计算（核心）、信息论、控制论
- 详见：[CONCEPT_CROSS_INDEX.md](CONCEPT_CROSS_INDEX.md#隔离-isolation-七视角)

#### 2.9.2 互信息 (Mutual Information)

- 定义：I(X;Y) = H(X) + H(Y) - H(X,Y)
- 直观：X和Y共享的信息量
- 视角：信息论（核心）、AI模型、控制论
- 详见：[CONCEPT_CROSS_INDEX.md](CONCEPT_CROSS_INDEX.md#互信息-mutual-information-七视角)

### 2.10 K

#### 2.10.1 Kolmogorov复杂度 (Kolmogorov Complexity)

- 定义：K(x) = min{|p| : U(p) = x}（最短程序长度）
- 性质：不可计算
- 视角：信息论（核心）、图灵可计算、形式语言
- 详见：[CONCEPT_CROSS_INDEX.md](CONCEPT_CROSS_INDEX.md#kolmogorov复杂度-kolmogorov-complexity-七视角)

### 2.11 L

#### 2.11.1 Landauer极限 (Landauer Limit)

- 定义：E_min = kT ln2（擦除1比特信息的最小能耗）
- 意义：信息擦除的物理代价
- 视角：信息论（核心）、图灵可计算、控制论
- 详见：[CONCEPT_CROSS_INDEX.md](CONCEPT_CROSS_INDEX.md#landauer极限-landauer-limit-七视角)

### 2.12 M

#### 2.12.1 Meta-learning (元学习)

- 定义：学习如何学习
- 等价性：≡ 2阶反身性 ≡ 2阶反馈控制
- 视角：AI模型（核心）、形式语言、控制论
- 详见：[CONCEPT_CROSS_INDEX.md](CONCEPT_CROSS_INDEX.md#meta-learning-七视角)

#### 2.12.2 冯·诺依曼瓶颈 (Von Neumann Bottleneck)

- 定义：CPU与内存间的速度差距（数千倍）
- 根源：指令与数据共享总线
- 视角：冯·诺依曼架构（核心）
- 相关：三大祸根（冯·诺依曼架构的三个根本缺陷）, 内存墙

### 2.13 P

#### 2.13.1 PAC学习 (Probably Approximately Correct Learning)

- 定义：以高概率学习近似正确假设的框架
- 关键参数：ε（误差）、δ（置信度）
- 视角：AI模型（核心）
- 相关：[VC维](#vc维-vapnik-chervonenkis-dimension), 样本复杂度（m = O((1/ε) log(1/δ))）

#### 2.13.2 P vs NP问题

- 问题：P = NP?（P是否等于NP）
- 意义：高效算法是否总能找到
- 视角：计算理论（核心）、AI模型
- 详见：[CONCEPT_CROSS_INDEX.md](CONCEPT_CROSS_INDEX.md#p-vs-np问题-p-versus-np-problem-七视角)

#### 2.13.3 Popek-Goldberg定理

- 定义：虚拟化的充要条件（敏感指令⊆特权指令）
- 反例：x86未满足（后续通过硬件辅助解决）
- 视角：图灵可计算（核心）、冯·诺依曼架构
- 详见：[CONCEPT_CROSS_INDEX.md](CONCEPT_CROSS_INDEX.md#popek-goldberg定理-popek-goldberg-virtualization-theorem-七视角)

### 2.14 R

#### 2.14.1 Rice定理 (Rice's Theorem)

- 定义：所有非平凡的语义性质都是不可判定的
- 证明：归约到停机问题
- 视角：图灵可计算（核心）、形式语言
- 详见：[CONCEPT_CROSS_INDEX.md](CONCEPT_CROSS_INDEX.md#rice定理-rices-theorem-七视角)

### 2.15 S

#### 2.15.1 三票理论 (Three Tickets Theory)

- 定义：文明三要素 = 能量盈余 + 信息外化 + 冗余容错
- 2025状态：三票齐备，文明加速
- 视角：信息论、图灵可计算、分布式
- 详见：[CONCEPT_CROSS_INDEX.md](CONCEPT_CROSS_INDEX.md#三票理论-three-tickets-theory-七视角)

#### 2.15.2 Shannon熵 (Shannon Entropy)

- 同：[熵 (Entropy)](#entropy-熵)

#### 2.15.3 主权矩阵 (Sovereignty Matrix)

- 定义：九维系统控制能力度量
- 维度：指令拦截、地址重映射、系统调用、内核模块、硬件直通、网络协议、文件系统、内存限制、生命周期
- 视角：图灵可计算（核心）、控制论、分布式
- 详见：[CONCEPT_CROSS_INDEX.md](CONCEPT_CROSS_INDEX.md#主权矩阵-sovereignty-matrix-七视角)

### 2.16 T

#### 2.16.1 图灵完备性 (Turing Completeness)

- 定义：计算能力等价于图灵机（可模拟任何算法）
- 条件：无限内存 + 条件分支 + 循环
- 视角：图灵可计算（核心）、形式语言、AI模型
- 详见：[CONCEPT_CROSS_INDEX.md](CONCEPT_CROSS_INDEX.md#图灵完备性-turing-completeness-七视角)

#### 2.16.2 三元视角 (Triadic Perspective)

- 中文：控制·执行·数据
- 定义：将系统分解为控制层(Control)、执行层(Execution)、数据层(Data)
- 形式化：Sys = ⟨C, E, D⟩
- 视角：编程算法设计（核心）
- 应用：形式语义建模、架构分析、性能优化
- 详见：[Program_Algorithm_Perspective](Program_Algorithm_Perspective/README.md)

### 2.17 U

#### 2.17.1 UH-Cost 统一元模型

- 英文：Unified Hypergraph-Cost Model
- 定义：用于建模编程语言语义、算法复杂度、设计模式和系统架构的统一形式化框架
- 形式化：UH-Cost = ⟨Σ, ⟶, κ, Φ⟩
  - Σ：系统状态空间 (State Space)
  - ⟶：转换关系 (Transition Relation)
  - κ：代价函数 (Cost Function)
  - Φ：属性规范 (Property Specifications)
- 视角：编程算法设计（核心）、形式语言、信息论
- 特点：支持20维复杂度分析、跨层架构验证
- 工具链：Coq/Lean4/K-Framework/mCRL2/UPPAAL
- 详见：[Program_Algorithm_Perspective](Program_Algorithm_Perspective/README.md) | [CONCEPT_CROSS_INDEX.md](CONCEPT_CROSS_INDEX.md#uh-cost-统一元模型-unified-hypergraph-cost-model-新增编程算法视角)

### 2.18 V

#### 2.18.1 VC维 (Vapnik-Chervonenkis Dimension)

- 定义：假设空间能打散的最大点数
- 意义：模型容量的度量
- 关键定理：PAC可学习 ⟺ 有限VC维
- 视角：AI模型（核心）
- 详见：[CONCEPT_CROSS_INDEX.md](CONCEPT_CROSS_INDEX.md#vc维-vapnik-chervonenkis-dimension-七视角)

#### 2.18.2 虚拟化 (Virtualization)

- 定义：通过软件抽象层将物理资源映射为虚拟资源
- 类型：全虚拟化、半虚拟化、硬件辅助
- 视角：图灵可计算（核心）、冯·诺依曼架构
- 详见：[CONCEPT_CROSS_INDEX.md](CONCEPT_CROSS_INDEX.md#虚拟化-virtualization-七视角)

### 2.19 X

#### 2.19.1 形式语言 (Formal Language)

- 定义：L ⊆ Σ*（字母表上的字符串集合）
- 分类：[Chomsky层级](#chomsky层级-chomsky-hierarchy)
- 视角：形式语言（核心）
- 相关：语法（Syntax, 符号规则）, 语义（Semantics, 符号意义）

---

## 3 按视角分类

### 3.1 形式语言视角

- [Chomsky层级](#chomsky层级-chomsky-hierarchy)
- [反身性](#反身性-reflexivity)
- [Gödel不完备定理](#gödel不完备定理-gödels-incompleteness-theorems)
- [形式语言](#形式语言-formal-language)
- 语法 (Syntax) - 符号规则
- 语义 (Semantics) - 符号意义
- 语义域 (Semantic Domain) - 意义空间
- 类型系统 (Type System) - 类型约束

### 3.2 AI模型视角

- [Gold可学习性](#gold可学习性-gold-learnability-theory)
- [VC维](#vc维-vapnik-chervonenkis-dimension)
- [PAC学习](#pac学习-probably-approximately-correct-learning)
- [Meta-learning](#meta-learning-元学习)
- [AGI](#agi-artificial-general-intelligence)
- 神经网络 (Neural Network) - AI基础架构
- Transformer - 现代大模型核心架构
- 注意力机制 (Attention Mechanism) - Self-Attention, Cross-Attention

### 3.3 信息论视角

- [熵 (Entropy)](#entropy-熵)
- [互信息](#互信息-mutual-information)
- [Kolmogorov复杂度](#kolmogorov复杂度-kolmogorov-complexity)
- [Landauer极限](#landauer极限-landauer-limit)
- Shannon定理 - 信道容量界 C = max I(X;Y)
- 信道容量 (Channel Capacity) - C bits/symbol
- 率失真理论 (Rate-Distortion) - 压缩与失真权衡 R(D)
- 信息瓶颈 (Information Bottleneck) - 最小化I(X;T) + βI(T;Y)

### 3.4 图灵可计算视角

- [图灵完备性](#图灵完备性-turing-completeness)
- [停机问题](#停机问题-halting-problem)
- [Rice定理](#rice定理-rices-theorem)
- [虚拟化](#虚拟化-virtualization)
- [Popek-Goldberg定理](#popek-goldberg定理)
- 容器化 (Containerization) - Docker, Kubernetes
- 沙盒化 (Sandboxing) - WASM, Seccomp, eBPF
- [主权矩阵](#主权矩阵-sovereignty-matrix)
- [隔离](#隔离-isolation)
- [三票理论](#三票理论-three-tickets-theory)

### 3.5 控制论视角

- [Ashby必要多样性定律](#ashby必要多样性定律-ashbys-law-of-requisite-variety)
- [Data Rate定理](#data-rate定理-data-rate-theorem)
- 反馈控制 (Feedback Control) - 输出反馈u=f(y)
- 前馈控制 (Feedforward Control) - 基于模型预测
- Lyapunov稳定性 - V̇(x) < 0 保证稳定
- MPC (Model Predictive Control) - 滚动优化控制
- PID控制 - u = Kp·e + Ki∫e + Kd·de/dt

### 3.6 冯·诺依曼架构视角

- [冯·诺依曼瓶颈](#冯诺依曼瓶颈-von-neumann-bottleneck)
- 三大祸根 (Three Curses) - 瓶颈、串行、脆弱
- 指令集架构 (ISA) - x86, ARM, RISC-V
- 内存层次 (Memory Hierarchy) - Register, Cache, RAM, Disk
- Cache (缓存) - L1/L2/L3，局部性原理
- DMA (Direct Memory Access) - 直接内存访问，无需CPU
- IOMMU - IO内存管理单元，虚拟化支持

### 3.7 分布式系统视角

- [CAP定理](#cap定理-cap-theorem)
- [FLP不可能定理](#flp不可能定理-flp-impossibility-theorem)
- [BFT (拜占庭容错)](#bft-byzantine-fault-tolerance)
- 共识算法 (Consensus Algorithm) - 分布式一致性协议
- Paxos - 经典共识算法，两阶段提交
- Raft - 易理解的共识算法，Leader选举
- PBFT (Practical BFT) - 实用拜占庭容错，3f+1节点
- 最终一致性 (Eventual Consistency) - BASE模型，弱一致性

### 3.8 编程算法设计视角 ✨

- [UH-Cost 统一元模型](#uh-cost-统一元模型)
- [三元视角](#三元视角-triadic-perspective)
- 操作语义 (Operational Semantics) - 程序执行的小步/大步语义
- 指称语义 (Denotational Semantics) - 程序的数学语义
- 公理语义 (Axiomatic Semantics) - Hoare逻辑
- 设计模式形式化 (Formal Design Patterns) - GoF 23模式的UH-Cost建模
- 多维复杂度 (Multidimensional Complexity) - 20维资源向量分析
- 跨层验证 (Cross-Layer Verification) - 商业→企业→软件→硬件→信息
- K-Framework - 可执行形式语义框架
- mCRL2 - 模型检查工具
- UPPAAL - 时间自动机验证工具

**完整术语表**: [Program_Algorithm_Perspective/GLOSSARY.md](Program_Algorithm_Perspective/GLOSSARY.md) (100+ 术语)

---

## 4 核心术语 (Top 50)

以下是最常用、最核心的50个术语，按使用频率和重要性排序：

1. **反身性** - 七视角通用核心
2. **Chomsky层级** - 语言能力分类
3. **图灵完备性** - 计算能力定义
4. **熵** - 信息度量基础
5. **互信息** - 信息共享度量
6. **虚拟化** - 资源抽象核心
7. **CAP定理** - 分布式系统限制
8. **Ashby定律** - 控制复杂度下界
9. **VC维** - 模型容量度量
10. **Gold可学习性** - 学习理论基础
11. **停机问题** - 可计算性边界
12. **Gödel不完备定理** - 形式系统限制
13. **Kolmogorov复杂度** - 最短描述长度
14. **隔离** - 系统安全基础
15. **FLP不可能定理** - 异步共识限制
16. **Data Rate定理** - 信息速率下界
17. **Meta-learning** - 学习如何学习
18. **P vs NP** - 计算复杂性核心问题
19. **Rice定理** - 语义性质不可判定
20. **Landauer极限** - 信息擦除能耗下界
21. **三票理论** - 文明演化框架
22. **主权矩阵** - 系统控制能力
23. **Popek-Goldberg定理** - 虚拟化条件
24. **BFT** - 拜占庭容错
25. **PAC学习** - 概率近似正确学习
26. **DIKWP模型** - 数据到目的升华
27. **冯·诺依曼瓶颈** - CPU-内存速度差距
28. **Shannon定理** - 信道容量界
29. **形式语言** - 符号串集合
30. **语法与语义** - 符号与意义
31. **AGI** - 通用人工智能
32. **神经网络** - AI基础架构
33. **Transformer** - 现代AI核心架构
34. **反馈控制** - 系统调节机制
35. **Lyapunov稳定性** - 系统稳定性判据
36. **MPC** - 模型预测控制
37. **共识算法** - 分布式一致性
38. **容器化** - 轻量级虚拟化
39. **沙盒化** - 隔离执行环境
40. **指令集架构** - 硬件软件接口
41. **Cache** - 高速缓存
42. **信道容量** - 通信上界
43. **率失真** - 压缩与失真权衡
44. **信息瓶颈** - 信息压缩原则
45. **类型系统** - 程序正确性保障
46. **Paxos/Raft** - 经典共识算法
47. **最终一致性** - 分布式弱一致性
48. **IOMMU** - IO内存管理单元
49. **三大祸根** - 冯·诺依曼架构缺陷
50. **注意力机制** - Transformer核心

---

## 5 缩写表

| 缩写 | 全称 | 中文 | 类别 |
|-----|------|------|------|
| AI | Artificial Intelligence | 人工智能 | 通用 |
| AGI | Artificial General Intelligence | 通用人工智能 | AI |
| BFT | Byzantine Fault Tolerance | 拜占庭容错 | 分布式 |
| BQP | Bounded-Error Quantum Polynomial Time | 有界误差量子多项式时间 | 复杂性 |
| CAP | Consistency, Availability, Partition-tolerance | 一致性、可用性、分区容错 | 分布式 |
| CFL | Context-Free Language | 上下文无关语言 | 形式语言 |
| CSL | Context-Sensitive Language | 上下文相关语言 | 形式语言 |
| DMA | Direct Memory Access | 直接内存访问 | 硬件 |
| FLP | Fischer-Lynch-Paterson | Fischer-Lynch-Paterson | 分布式 |
| ISA | Instruction Set Architecture | 指令集架构 | 硬件 |
| MPC | Model Predictive Control | 模型预测控制 | 控制论 |
| NP | Nondeterministic Polynomial Time | 非确定性多项式时间 | 复杂性 |
| PAC | Probably Approximately Correct | 概率近似正确 | 学习理论 |
| PBFT | Practical Byzantine Fault Tolerance | 实用拜占庭容错 | 分布式 |
| PID | Proportional-Integral-Derivative | 比例-积分-微分 | 控制论 |
| RE | Recursively Enumerable | 递归可枚举 | 形式语言 |
| REG | Regular Language | 正则语言 | 形式语言 |
| VC | Vapnik-Chervonenkis | Vapnik-Chervonenkis | 学习理论 |

---

## 6 补充说明

### 6.1 如何使用本术语表

1. **快速查词**: 按字母索引或视角分类查找
2. **深入学习**: 点击"详见"链接查看完整分析
3. **跨视角理解**: 关注"视角"标签，理解概念的多维视角
4. **建立联系**: 通过"相关"链接建立概念网络

### 6.2 术语说明规范

每个术语包含：

- **定义**: 简明扼要的定义
- **形式化**: 数学公式（如适用）
- **视角**: 该术语所属的主要视角
- **相关**: 关联的其他术语
- **详见**: 更详细文档的链接

### 6.3 持续更新

本术语表随项目发展持续更新：

- ✅ v1.0.0: 初始版本，120+核心术语
- 🔜 v1.1.0: 补充剩余概念，扩展到150+术语
- 🔜 v2.0.0: 增加多语言支持

---

## 7 相关资源

- [完整概念分析](CONCEPT_CROSS_INDEX.md) - 30个核心概念的七视角详解
- [快速参考](QUICK_REFERENCE.md) - 核心公式和定理速查
- [FAQ](FAQ.md) - 常见问题解答
- [学习路径](LEARNING_PATHS.md) - 系统学习指南
- [统一框架](UNIFIED_FRAMEWORK.md) - 七视角理论框架
- [导航地图](NAVIGATION_INDEX.md) - 全局导航系统

---

**文档版本**: v1.2.0
**最后更新**: 2025-10-25
**维护状态**: ✅ 活跃维护
**术语总数**: 120+
**链接修复**: ✅ 已全部完成
**格式优化**: ✅ 已完成

> 💡 遇到生词就查本术语表！💡
