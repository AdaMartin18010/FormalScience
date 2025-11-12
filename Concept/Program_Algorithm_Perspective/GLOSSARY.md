# 术语表 (Glossary)

> **程序-算法-设计视角的核心术语定义**

---

## 📋 目录

- [术语表 (Glossary)](#术语表-glossary)
  - [📋 目录](#-目录)
  - [1 📋 索引](#1--索引)
  - [2 A](#2-a)
    - [2.1 Abstract Factory (抽象工厂模式)](#21-abstract-factory-抽象工厂模式)
    - [2.2 Adaptivity (自适应性)](#22-adaptivity-自适应性)
    - [2.3 Axiomatic Semantics (公理语义)](#23-axiomatic-semantics-公理语义)
  - [3 B](#3-b)
    - [3.1 Big-step Semantics (大步语义)](#31-big-step-semantics-大步语义)
    - [3.2 Builder Pattern (建造者模式)](#32-builder-pattern-建造者模式)
  - [4 C](#4-c)
    - [4.1 Cache Complexity (缓存复杂度)](#41-cache-complexity-缓存复杂度)
    - [4.2 Cache-oblivious Algorithm (缓存无关算法)](#42-cache-oblivious-algorithm-缓存无关算法)
    - [4.3 Communication Complexity (通讯复杂度)](#43-communication-complexity-通讯复杂度)
    - [4.4 Composite Pattern (组合模式)](#44-composite-pattern-组合模式)
    - [4.5 Cost Semantics (成本语义)](#45-cost-semantics-成本语义)
    - [4.6 CQRS (Command Query Responsibility Segregation)](#46-cqrs-command-query-responsibility-segregation)
  - [5 D](#5-d)
    - [5.1 Decorator Pattern (装饰器模式)](#51-decorator-pattern-装饰器模式)
    - [5.2 Denotational Semantics (指称语义)](#52-denotational-semantics-指称语义)
    - [5.3 Differential Privacy (差分隐私)](#53-differential-privacy-差分隐私)
  - [6 E](#6-e)
    - [6.1 Energy Complexity (能量复杂度)](#61-energy-complexity-能量复杂度)
    - [6.2 Event Sourcing (事件溯源)](#62-event-sourcing-事件溯源)
  - [7 F](#7-f)
    - [7.1 Factory Method (工厂方法模式)](#71-factory-method-工厂方法模式)
    - [7.2 Formal Semantics (形式语义)](#72-formal-semantics-形式语义)
  - [8 G](#8-g)
    - [8.1 GoF (Gang of Four)](#81-gof-gang-of-four)
  - [9 H](#9-h)
    - [9.1 Hoare Triple (Hoare 三元组)](#91-hoare-triple-hoare-三元组)
  - [10 I](#10-i)
    - [10.1 I/O Complexity (I/O 复杂度)](#101-io-complexity-io-复杂度)
    - [10.2 Ideal-Cache Model (理想缓存模型)](#102-ideal-cache-model-理想缓存模型)
  - [11 K](#11-k)
    - [11.1 K-Framework](#111-k-framework)
    - [11.2 Kolmogorov Complexity (柯尔莫哥洛夫复杂度)](#112-kolmogorov-complexity-柯尔莫哥洛夫复杂度)
  - [12 L](#12-l)
    - [12.1 Lambda Calculus (λ-演算)](#121-lambda-calculus-λ-演算)
    - [12.2 Landauer's Principle (Landauer 原理)](#122-landauers-principle-landauer-原理)
  - [13 M](#13-m)
    - [13.1 Model Checking (模型检测)](#131-model-checking-模型检测)
  - [14 N](#14-n)
    - [14.1 Natural Semantics (自然语义)](#141-natural-semantics-自然语义)
  - [15 O](#15-o)
    - [15.1 Observer Pattern (观察者模式)](#151-observer-pattern-观察者模式)
    - [15.2 Operational Semantics (操作语义)](#152-operational-semantics-操作语义)
  - [16 P](#16-p)
    - [16.1 Petri Net (Petri 网)](#161-petri-net-petri-网)
    - [16.2 π-Calculus (π-演算)](#162-π-calculus-π-演算)
    - [16.3 Privacy Budget (隐私预算)](#163-privacy-budget-隐私预算)
    - [16.4 Proxy Pattern (代理模式)](#164-proxy-pattern-代理模式)
  - [17 Q](#17-q)
    - [17.1 QHL (Quantitative Hoare Logic)](#171-qhl-quantitative-hoare-logic)
  - [18 R](#18-r)
    - [18.1 Rewriting Logic (重写逻辑)](#181-rewriting-logic-重写逻辑)
  - [19 S](#19-s)
    - [19.1 Saga Pattern (Saga 模式)](#191-saga-pattern-saga-模式)
    - [19.2 Sample Complexity (样本复杂度)](#192-sample-complexity-样本复杂度)
    - [19.3 Singleton Pattern (单例模式)](#193-singleton-pattern-单例模式)
    - [19.4 Small-step Semantics (小步语义)](#194-small-step-semantics-小步语义)
    - [19.5 Span (跨度)](#195-span-跨度)
    - [19.6 Strategy Pattern (策略模式)](#196-strategy-pattern-策略模式)
  - [20 T](#20-t)
    - [20.1 Theorem Prover (定理证明器)](#201-theorem-prover-定理证明器)
    - [20.2 Time Complexity (时间复杂度)](#202-time-complexity-时间复杂度)
    - [20.3 Type System (类型系统)](#203-type-system-类型系统)
  - [21 U](#21-u)
    - [21.1 UH-Cost (Unified Hypergraph-Cost Model)](#211-uh-cost-unified-hypergraph-cost-model)
  - [22 V](#22-v)
    - [22.1 Verifiability (可验证性)](#221-verifiability-可验证性)
  - [23 W](#23-w)
    - [23.1 Work (工作量)](#231-work-工作量)
    - [23.2 Workflow Pattern (工作流模式)](#232-workflow-pattern-工作流模式)
  - [24 Z](#24-z)
    - [24.1 Z3](#241-z3)
  - [25 缩写表](#25-缩写表)
  - [26 符号表](#26-符号表)
  - [27 扩展阅读](#27-扩展阅读)

---

## 1 📋 索引

[A](#a) | [B](#b) | [C](#c) | [D](#d) | [E](#e) | [F](#f) | [G](#g) | [H](#h) | [I](#i) | [K](#k) | [L](#l) | [M](#m) | [N](#n) | [O](#o) | [P](#p) | [Q](#q) | [R](#r) | [S](#s) | [T](#t) | [U](#u) | [V](#v) | [W](#w) | [Z](#z)

---

## 2 A

### 2.1 Abstract Factory (抽象工厂模式)

**定义**: 提供一个创建一系列相关或相互依赖对象的接口，而无需指定它们具体的类。

**形式化**:

```coq
Record AbstractFactory : Type := {
  create : Product -> object
}.
```

**相关**: [02.1_GoF_Formal_Analysis.md](02_Design_Patterns/02.1_GoF_Formal_Analysis.md)

---

### 2.2 Adaptivity (自适应性)

**定义**: 算法根据中间结果动态调整后续查询或决策的能力。

**度量**: 轮次数（自适应轮）vs 总查询数

**示例**: 随机梯度下降（自适应学习率）

**相关**: [03.1_Multidimensional_Complexity.md](03_Algorithm_Complexity/03.1_Multidimensional_Complexity.md#adaptivity)

---

### 2.3 Axiomatic Semantics (公理语义)

**定义**: 通过逻辑公式（前置条件、后置条件）描述程序性质的语义方法。

**形式**: Hoare 三元组 `{P} c {Q}`

**工具**: Dafny, Why3, Frama-C

**相关**: [01.3_Axiomatic_Semantics.md](01_Formal_Semantics/01.3_Axiomatic_Semantics.md)

---

## 3 B

### 3.1 Big-step Semantics (大步语义)

**定义**: 直接求值到最终结果的操作语义，也称自然语义 (Natural Semantics)。

**判断形式**: `e ⇓ v`

**对比**: Small-step Semantics (小步语义)

**相关**: [01.1_Operational_Semantics.md](01_Formal_Semantics/01.1_Operational_Semantics.md#big-step)

---

### 3.2 Builder Pattern (建造者模式)

**定义**: 将一个复杂对象的构建与它的表示分离，使得同样的构建过程可以创建不同的表示。

**特点**: 链式调用、分步构造

**相关**: [02.1_GoF_Formal_Analysis.md](02_Design_Patterns/02.1_GoF_Formal_Analysis.md#builder)

---

## 4 C

### 4.1 Cache Complexity (缓存复杂度)

**定义**: 缓存未命中 (cache miss) 的次数。

**模型**: Ideal-Cache 模型（全相联、LRU、参数 Z 和 L）

**典型下界**: 矩阵乘法 Ω(n³/√Z)

**相关**: [03.1_Multidimensional_Complexity.md](03_Algorithm_Complexity/03.1_Multidimensional_Complexity.md#cache)

---

### 4.2 Cache-oblivious Algorithm (缓存无关算法)

**定义**: 无需知道缓存参数 Z 和 L 就能达到渐近最优缓存性能的算法。

**典型例子**: 递归矩阵乘法、Funnelsort

**优势**: 可移植性、自适应多级缓存

**参考**: [Wikipedia](https://en.wikipedia.org/wiki/Cache-oblivious_algorithm)

---

### 4.3 Communication Complexity (通讯复杂度)

**定义**: 分布式算法中传输的总比特数。

**模型**:

- 2-party (Alice & Bob)
- multi-party (n 个参与方)

**经典问题**: DISJ (不相交集判定) 下界 Ω(n)

**相关**: [03.1_Multidimensional_Complexity.md](03_Algorithm_Complexity/03.1_Multidimensional_Complexity.md#communication)

---

### 4.4 Composite Pattern (组合模式)

**定义**: 将对象组合成树形结构以表示"部分-整体"的层次结构，使得用户对单个对象和组合对象的使用具有一致性。

**形式化**: 代数数据类型 `data Component = Leaf a | Node [Component a]`

**相关**: [02.1_GoF_Formal_Analysis.md](02_Design_Patterns/02.1_GoF_Formal_Analysis.md#composite)

---

### 4.5 Cost Semantics (成本语义)

**定义**: 在操作语义上附加资源计数器，精确追踪资源消耗。

**形式**: `⟨e, σ, κ⟩ → ⟨e', σ', κ'⟩` 其中 κ ∈ ℕ^d 是 d 维资源向量

**应用**: 验证时间/空间/能量界

**相关**: [01.1_Operational_Semantics.md](01_Formal_Semantics/01.1_Operational_Semantics.md#cost-semantics)

---

### 4.6 CQRS (Command Query Responsibility Segregation)

**定义**: 命令查询职责分离，读写操作使用不同的模型。

**形式化**: `Command → Event*; Query → View`

**优势**: 读写独立扩展、事件溯源

**相关**: [02.2_Distributed_Patterns.md](02_Design_Patterns/02.2_Distributed_Patterns.md)

---

## 5 D

### 5.1 Decorator Pattern (装饰器模式)

**定义**: 动态地给一个对象添加一些额外的职责，就增加功能来说，Decorator 模式相比生成子类更为灵活。

**形式化**: 函数组合 `Decorator : Component -> Component`

**性质**: 结合律 `(D₁ ∘ D₂) ∘ D₃ ≡ D₁ ∘ (D₂ ∘ D₃)`

**相关**: [02.1_GoF_Formal_Analysis.md](02_Design_Patterns/02.1_GoF_Formal_Analysis.md#decorator)

---

### 5.2 Denotational Semantics (指称语义)

**定义**: 将程序映射到数学对象（通常是函数或域）的语义方法。

**核心**: 语义函数 `⟦·⟧ : Expr → Domain`

**优势**: 组合性强、易于数学推理

**相关**: [01.2_Denotational_Semantics.md](01_Formal_Semantics/01.2_Denotational_Semantics.md)

---

### 5.3 Differential Privacy (差分隐私)

**定义**: 保证单条记录的添加或删除对算法输出分布的影响有界。

**形式**: `Pr[A(D) ∈ S] ≤ e^ε · Pr[A(D') ∈ S] + δ`

**参数**: ε (隐私预算), δ (失败概率)

**相关**: [03.1_Multidimensional_Complexity.md](03_Algorithm_Complexity/03.1_Multidimensional_Complexity.md#privacy)

---

## 6 E

### 6.1 Energy Complexity (能量复杂度)

**定义**: 算法执行的比特翻转次数，衡量能量消耗。

**物理基础**: Landauer 极限 (kT ln 2)

**典型下界**: n-bit 乘法 Ω(n²)

**相关**: [03.1_Multidimensional_Complexity.md](03_Algorithm_Complexity/03.1_Multidimensional_Complexity.md#energy)

---

### 6.2 Event Sourcing (事件溯源)

**定义**: 将所有状态变更存储为事件序列，当前状态通过重放事件计算得到。

**形式化**: `State = fold Event* σ₀`

**优势**: 完整审计日志、时间旅行查询

**相关**: [02.2_Distributed_Patterns.md](02_Design_Patterns/02.2_Distributed_Patterns.md)

---

## 7 F

### 7.1 Factory Method (工厂方法模式)

**定义**: 定义一个创建对象的接口，让子类决定实例化哪一个类。

**形式化**: `create : Type -> object` (子类重写)

**参考**: [Wikipedia](https://en.wikipedia.org/wiki/Factory_method_pattern)

**相关**: [02.1_GoF_Formal_Analysis.md](02_Design_Patterns/02.1_GoF_Formal_Analysis.md)

---

### 7.2 Formal Semantics (形式语义)

**定义**: 用数学方法精确定义程序行为的语义学。

**三大类**:

1. 操作语义 (Operational)
2. 指称语义 (Denotational)
3. 公理语义 (Axiomatic)

**参考**: [Wikipedia](https://en.wikipedia.org/wiki/Formal_semantics_of_programming_languages)

**相关**: [01_Formal_Semantics/](01_Formal_Semantics/)

---

## 8 G

### 8.1 GoF (Gang of Four)

**定义**: Gamma, Helm, Johnson, Vlissides 四位作者，1994 年出版《Design Patterns》。

**贡献**: 定义了 23 个经典设计模式

**分类**: 创建型、结构型、行为型

**参考**: [Wikipedia](https://en.wikipedia.org/wiki/Design_Patterns)

---

## 9 H

### 9.1 Hoare Triple (Hoare 三元组)

**定义**: 公理语义的核心判断形式 `{P} c {Q}`

**含义**:

- P: 前置条件 (precondition)
- c: 程序/命令 (command)
- Q: 后置条件 (postcondition)

**语义**: 若 P 成立且 c 终止，则 Q 成立

**相关**: [01.3_Axiomatic_Semantics.md](01_Formal_Semantics/01.3_Axiomatic_Semantics.md)

---

## 10 I

### 10.1 I/O Complexity (I/O 复杂度)

**定义**: 读写外部存储的块数。

**模型**: Aggarwal-Vitter 模型 (参数 M, B, N)

**排序下界**: Θ((N/B) log_{M/B} (N/B))

**相关**: [03.1_Multidimensional_Complexity.md](03_Algorithm_Complexity/03.1_Multidimensional_Complexity.md#io), [03.5_External_Memory_Algorithms.md](03_Algorithm_Complexity/03.5_External_Memory_Algorithms.md)

---

### 10.2 Ideal-Cache Model (理想缓存模型)

**定义**: 假设全相联、LRU 替换、离线最优的缓存模型。

**参数**:

- Z: 缓存大小
- L: 缓存行大小

**用途**: 分析缓存复杂度的理论模型

**相关**: [03.1_Multidimensional_Complexity.md](03_Algorithm_Complexity/03.1_Multidimensional_Complexity.md#cache)

---

## 11 K

### 11.1 K-Framework

**定义**: 基于重写逻辑的编程语言语义框架。

**特点**:

- 可执行语义（定义即解释器）
- 自动生成符号执行器
- 支持模型检测

**官网**: <https://kframework.org/>

**相关**: [05.3_K_Framework.md](05_Formal_Verification/05.3_K_Framework.md)

---

### 11.2 Kolmogorov Complexity (柯尔莫哥洛夫复杂度)

**定义**: 生成字符串 x 的最短程序长度 K(x)。

**性质**:

- 不可计算
- H(X) ≈ E[K(X)] (期望近似)

**应用**: 信息论下界、随机性度量

**相关**: [../../Information_Theory_Perspective/](../../Information_Theory_Perspective/)

---

## 12 L

### 12.1 Lambda Calculus (λ-演算)

**定义**: 形式化函数定义、应用和递归的计算模型。

**语法**: `e ::= x | λx.e | e e`

**性质**: 图灵完备

**应用**: 函数式编程语言的理论基础

**参考**: [Wikipedia](https://en.wikipedia.org/wiki/Lambda_calculus)

---

### 12.2 Landauer's Principle (Landauer 原理)

**定义**: 擦除 1 比特信息至少需要 kT ln 2 的能量。

**意义**: 计算的热力学极限

**温度**: 室温下 ≈ 3×10⁻²¹ J

**相关**: [03.1_Multidimensional_Complexity.md](03_Algorithm_Complexity/03.1_Multidimensional_Complexity.md#energy)

---

## 13 M

### 13.1 Model Checking (模型检测)

**定义**: 自动验证有限状态系统是否满足时序逻辑性质的技术。

**逻辑**: CTL, LTL, μ-演算

**工具**: mCRL2, UPPAAL, SPIN, TLA+

**应用**: 并发系统、分布式协议验证

**相关**: [05.2_Model_Checking_Tools.md](05_Formal_Verification/05.2_Model_Checking_Tools.md)

---

## 14 N

### 14.1 Natural Semantics (自然语义)

**定义**: Big-step Semantics 的别名，见 [Big-step Semantics](#big-step-semantics-大步语义)。

---

## 15 O

### 15.1 Observer Pattern (观察者模式)

**定义**: 定义对象间的一对多依赖关系，当一个对象状态改变时，所有依赖于它的对象都得到通知并自动更新。

**形式化**: π-演算 `Subject | Observer₁ | ... | ObserverN`

**性质**:

- 无死锁 (AG ¬deadlock)
- 通讯线性 (Comm = N·|state|)

**相关**: [02.1_GoF_Formal_Analysis.md](02_Design_Patterns/02.1_GoF_Formal_Analysis.md#observer)

---

### 15.2 Operational Semantics (操作语义)

**定义**: 通过定义程序如何逐步执行来给出程序意义的语义方法。

**两种形式**:

1. Small-step (小步语义)
2. Big-step (大步语义)

**参考**: [Wikipedia](https://en.wikipedia.org/wiki/Operational_semantics)

**相关**: [01.1_Operational_Semantics.md](01_Formal_Semantics/01.1_Operational_Semantics.md)

---

## 16 P

### 16.1 Petri Net (Petri 网)

**定义**: 用于并发系统建模的数学工具。

**组成**:

- Place (库所)
- Transition (变迁)
- Token (托肯)
- Arc (弧)

**应用**: 工作流、并发系统验证

**相关**: [02.3_Workflow_Patterns.md](02_Design_Patterns/02.3_Workflow_Patterns.md)

---

### 16.2 π-Calculus (π-演算)

**定义**: 描述并发计算的进程代数，支持通道传递。

**语法**: `P ::= 0 | a(x).P | ā⟨M⟩.P | P|Q | νa.P | !P`

**特点**: 移动性（通道可作为消息传递）

**应用**: 并发模式形式化

**参考**: [Wikipedia](https://en.wikipedia.org/wiki/Pi-calculus)

---

### 16.3 Privacy Budget (隐私预算)

**定义**: 差分隐私中的 ε 参数，越小越隐私。

**性质**: 可组合性（ε₁ + ε₂）

**典型值**: ε ∈ [0.1, 10]

**相关**: [03.1_Multidimensional_Complexity.md](03_Algorithm_Complexity/03.1_Multidimensional_Complexity.md#privacy)

---

### 16.4 Proxy Pattern (代理模式)

**定义**: 为其他对象提供一种代理以控制对这个对象的访问。

**类型**: 虚拟代理、保护代理、远程代理、缓存代理

**形式化**: π-演算 `Proxy | Subject` 行为等价

**相关**: [02.1_GoF_Formal_Analysis.md](02_Design_Patterns/02.1_GoF_Formal_Analysis.md#proxy)

---

## 17 Q

### 17.1 QHL (Quantitative Hoare Logic)

**定义**: 定量霍尔逻辑，扩展 Hoare Logic 支持资源界。

**形式**: `{P ∧ κ=K} c {Q ∧ κ≤K+Δ}`

**应用**: 验证时间/空间/能量界

---

## 18 R

### 18.1 Rewriting Logic (重写逻辑)

**定义**: 基于项重写的逻辑系统。

**语法**: `L ⟹ R`

**工具**: Maude, K-Framework

**应用**: 语言语义定义、并发系统建模

**相关**: [05.3_K_Framework.md](05_Formal_Verification/05.3_K_Framework.md)

---

## 19 S

### 19.1 Saga Pattern (Saga 模式)

**定义**: 分布式长事务模式，通过补偿操作保证最终一致性。

**形式化**: `comp₁;...;compₙ; compensateᵢ`

**性质**: `fold compensate σᵢ = σ₀` (可补偿性)

**相关**: [02.2_Distributed_Patterns.md](02_Design_Patterns/02.2_Distributed_Patterns.md)

---

### 19.2 Sample Complexity (样本复杂度)

**定义**: 学习算法达到目标精度所需的样本数。

**VC 维下界**: Ω(d/ε)

**应用**: 机器学习理论

**相关**: [03.1_Multidimensional_Complexity.md](03_Algorithm_Complexity/03.1_Multidimensional_Complexity.md#sample)

---

### 19.3 Singleton Pattern (单例模式)

**定义**: 保证一个类仅有一个实例，并提供一个全局访问点。

**形式化**: 线性类型 `⊢ ∀ r1 r2 : &mut Singleton, r1 ≡ r2`

**实现**: 懒汉式、饿汉式、双重检查锁定

**相关**: [02.1_GoF_Formal_Analysis.md](02_Design_Patterns/02.1_GoF_Formal_Analysis.md#singleton)

---

### 19.4 Small-step Semantics (小步语义)

**定义**: 每次执行一个原子操作的操作语义。

**判断形式**: `⟨e, σ⟩ → ⟨e', σ'⟩`

**优势**: 可建模中间状态、并发、非终止

**相关**: [01.1_Operational_Semantics.md](01_Formal_Semantics/01.1_Operational_Semantics.md#small-step)

---

### 19.5 Span (跨度)

**定义**: 并行算法的关键路径长度（最长依赖链）。

**Work-Span 模型**:

- Work = 总操作数
- Span = 关键路径长度
- 并行度 = Work / Span

**相关**: [03.4_Parallel_Algorithms.md](03_Algorithm_Complexity/03.4_Parallel_Algorithms.md)

---

### 19.6 Strategy Pattern (策略模式)

**定义**: 定义一系列算法，把它们一个个封装起来，并且使它们可以互相替换。

**形式化**: `Context : ∀α. Strategy α -> α`

**性质**: 可替换性 `ctx s1 ≡ ctx s2`

**相关**: [02.1_GoF_Formal_Analysis.md](02_Design_Patterns/02.1_GoF_Formal_Analysis.md#strategy)

---

## 20 T

### 20.1 Theorem Prover (定理证明器)

**定义**: 交互式或自动化证明数学定理的软件工具。

**主流工具**:

- Coq (依赖类型)
- Lean4 (数学库丰富)
- Isabelle/HOL (高阶逻辑)

**应用**: 程序验证、数学定理证明

**相关**: [05.1_Coq_Introduction.md](05_Formal_Verification/05.1_Coq_Introduction.md)

---

### 20.2 Time Complexity (时间复杂度)

**定义**: 算法执行的指令数或基本操作数。

**表示法**: O, Ω, Θ

**经典下界**: 排序 Ω(n log n)

**相关**: [03.1_Multidimensional_Complexity.md](03_Algorithm_Complexity/03.1_Multidimensional_Complexity.md#time)

---

### 20.3 Type System (类型系统)

**定义**: 用类型约束程序行为的形式化系统。

**类型**:

- 简单类型 (Simple Types)
- 依赖类型 (Dependent Types)
- 线性类型 (Linear Types)
- 定量类型 (Quantitative Types)

**性质**: Type Safety (Progress + Preservation)

**相关**: [01.4_Type_Systems.md](01_Formal_Semantics/01.4_Type_Systems.md)

---

## 21 U

### 21.1 UH-Cost (Unified Hypergraph-Cost Model)

**定义**: 统一超图成本模型，本项目提出的形式化框架。

**形式**: `UH-Cost = ⟨Σ, ⟶, κ, Φ⟩`

**应用**: 统一设计模式、算法、架构的形式化

**相关**: [README.md](README.md#uh-cost)

---

## 22 V

### 22.1 Verifiability (可验证性)

**定义**: 生成和验证计算正确性证明的资源消耗。

**维度**:

- 证明长度
- 验证时间

**技术**: PCP, SNARK, STARK

**相关**: [03.1_Multidimensional_Complexity.md](03_Algorithm_Complexity/03.1_Multidimensional_Complexity.md#verifiability)

---

## 23 W

### 23.1 Work (工作量)

**定义**: 并行算法的总操作数（时间 × 处理器数）。

**关系**: `T_parallel · P ≥ Work`

**相关**: [Span](#span-跨度), [03.4_Parallel_Algorithms.md](03_Algorithm_Complexity/03.4_Parallel_Algorithms.md)

---

### 23.2 Workflow Pattern (工作流模式)

**定义**: 业务流程建模中的可复用控制流模式。

**基础模式**: Sequence, XOR-Split, AND-Split, XOR-Join, AND-Join

**形式化**: Petri 网、BPMN

**相关**: [02.3_Workflow_Patterns.md](02_Design_Patterns/02.3_Workflow_Patterns.md)

---

## 24 Z

### 24.1 Z3

**定义**: Microsoft Research 开发的 SMT (Satisfiability Modulo Theories) 求解器。

**应用**: 符号执行、程序综合、约束求解

**官网**: <https://github.com/Z3Prover/z3>

**相关**: [05.4_Symbolic_Execution.md](05_Formal_Verification/05.4_Symbolic_Execution.md)

---

## 25 缩写表

| 缩写 | 全称 | 中文 |
|------|------|------|
| AST | Abstract Syntax Tree | 抽象语法树 |
| BPMN | Business Process Model and Notation | 业务流程建模符号 |
| CC | Communication Complexity | 通讯复杂度 |
| CEK | Control-Environment-Kontinuation | 控制-环境-继续 |
| CFG | Context-Free Grammar | 上下文无关文法 |
| CLRS | Cormen, Leiserson, Rivest, Stein | 《算法导论》作者 |
| CQRS | Command Query Responsibility Segregation | 命令查询职责分离 |
| CSP | Communicating Sequential Processes | 通讯顺序进程 |
| CTL | Computation Tree Logic | 计算树逻辑 |
| DP | Differential Privacy | 差分隐私 |
| ES | Event Sourcing | 事件溯源 |
| GoF | Gang of Four | 四人组 |
| HJB | Hamilton-Jacobi-Bellman | 哈密尔顿-雅可比-贝尔曼方程 |
| HOL | Higher-Order Logic | 高阶逻辑 |
| I/O | Input/Output | 输入/输出 |
| LRU | Least Recently Used | 最近最少使用 |
| LTL | Linear Temporal Logic | 线性时序逻辑 |
| LTS | Labeled Transition System | 标签转移系统 |
| MIR | Mid-level Intermediate Representation | 中级中间表示 (Rust) |
| NoC | Network-on-Chip | 片上网络 |
| PCP | Probabilistically Checkable Proof | 概率可检查证明 |
| POSA | Pattern-Oriented Software Architecture | 面向模式的软件架构 |
| QHL | Quantitative Hoare Logic | 定量霍尔逻辑 |
| RAM | Random Access Machine | 随机访问机 |
| SECD | Stack-Environment-Control-Dump | 栈-环境-控制-转储 |
| SMT | Satisfiability Modulo Theories | 可满足性模理论 |
| SNARK | Succinct Non-interactive Argument of Knowledge | 简洁非交互知识论证 |
| SOS | Structural Operational Semantics | 结构化操作语义 |
| SPARK | Semantic and Pragmatic Analyzer for Reproducible Code | SPARK 验证工具集 |
| TAPL | Types and Programming Languages | 《类型与编程语言》 |
| TLA+ | Temporal Logic of Actions | 行为时序逻辑 |
| VC | Verification Condition | 验证条件 (VC 维 = Vapnik-Chervonenkis 维) |

---

## 26 符号表

| 符号 | 含义 | 示例 |
|------|------|------|
| `⟨·⟩` | 配置/元组 | `⟨e, σ, κ⟩` |
| `→` | 转移/推导 | `e → e'` |
| `⇒` | 重写/蕴含 | `L ⇒ R` |
| `⇓` | 大步求值 | `e ⇓ v` |
| `⟦·⟧` | 语义函数 | `⟦e⟧σ` |
| `{P} c {Q}` | Hoare 三元组 | `{x>0} x:=x+1 {x>1}` |
| `≡` | 等价 | `e1 ≡ e2` |
| `⊢` | 证明/推导 | `Γ ⊢ e : τ` |
| `⊨` | 满足/语义蕴含 | `M ⊨ φ` |
| `∘` | 函数组合 | `f ∘ g` |
| `\|` | 并行组合 | `P \| Q` |
| `ν` | 新名字/限制 | `νx.P` |
| `!` | 复制 | `!P` |
| `Ω` | 下界 | `Ω(n log n)` |
| `O` | 上界 | `O(n²)` |
| `Θ` | 紧界 | `Θ(n)` |
| `⊥` | 底元素/未定义 | `⟦diverge⟧ = ⊥` |
| `⊤` | 顶元素/真 | `true = ⊤` |
| `∀` | 全称量词 | `∀x. P(x)` |
| `∃` | 存在量词 | `∃x. P(x)` |
| `λ` | Lambda 抽象 | `λx.e` |
| `μ` | 不动点 | `μX.F(X)` |
| `κ` | 成本向量 | `κ = (t, s, c, e, ...)` |
| `σ` | 状态/环境 | `σ : Var → Val` |
| `Φ` | 正确性谓词 | `Φ(M)` |
| `Σ` | 签名/和类型 | `Σ = (P, T, F)` |
| `∏` | 积类型/并行组合 | `∏ᵢ Pᵢ` |

---

## 27 扩展阅读

- [00_Master_Index.md](00_Master_Index.md) - 主索引
- [README.md](README.md) - 总体概述
- [REFERENCES.md](REFERENCES.md) - 参考文献
- [LEARNING_PATHS.md](LEARNING_PATHS.md) - 学习路径

---

**最后更新**: 2025-10-29
**维护者**: FormalScience Team
**许可**: MIT License
