- --
topic: "术语表 (Glossary)"
dependencies: []
status: "review"
author: "FormalScience Project"
date: "2026-04-12"
version: "1.0.0"
tags: ["递归", "类型", "形式化", "证明", "定理"]
category: "reference"
priority: "medium"
- --

# 术语表 (Glossary)

> **程序-算法-设计视角的核心术语定义**

- --

## 1. 📋 目录 {#-目录}

- [术语表 (Glossary)](#术语表-glossary)
  - [1. 📋 目录 {#-目录}](#1--目录--目录)
  - [1. 📋 索引 {#-索引}](#1--索引--索引)
  - [2. A {#a}](#2-a-a)
    - [2 1 Abstract Factory (抽象工厂模式) {#1-abstract-factory-抽象工厂模式}](#2-1-abstract-factory-抽象工厂模式-1-abstract-factory-抽象工厂模式)
    - [2 2 Adaptivity (自适应性) {#2-adaptivity-自适应性}](#2-2-adaptivity-自适应性-2-adaptivity-自适应性)
    - [2 3 Axiomatic Semantics (公理语义) {#3-axiomatic-semantics-公理语义}](#2-3-axiomatic-semantics-公理语义-3-axiomatic-semantics-公理语义)
  - [3. B {#b}](#3-b-b)
    - [3 1 Big-step Semantics (大步语义) {#1-big-step-semantics-大步语义}](#3-1-big-step-semantics-大步语义-1-big-step-semantics-大步语义)
    - [3 2 Builder Pattern (建造者模式) {#2-builder-pattern-建造者模式}](#3-2-builder-pattern-建造者模式-2-builder-pattern-建造者模式)
  - [4. C {#c}](#4-c-c)
    - [4 1 Cache Complexity (缓存复杂度) {#1-cache-complexity-缓存复杂度}](#4-1-cache-complexity-缓存复杂度-1-cache-complexity-缓存复杂度)
    - [4 2 Cache-oblivious Algorithm (缓存无关算法) {#2-cache-oblivious-algorithm-缓存}](#4-2-cache-oblivious-algorithm-缓存无关算法-2-cache-oblivious-algorithm-缓存)
    - [4 3 Communication Complexity (通讯复杂度) {#3-communication-complexity-通讯复}](#4-3-communication-complexity-通讯复杂度-3-communication-complexity-通讯复)
    - [4 4 Composite Pattern (组合模式) {#4-composite-pattern-组合模式}](#4-4-composite-pattern-组合模式-4-composite-pattern-组合模式)
    - [4 5 Cost Semantics (成本语义) {#5-cost-semantics-成本语义}](#4-5-cost-semantics-成本语义-5-cost-semantics-成本语义)
    - [4 6 CQRS (Command Query Responsibility Segregation) {#6-cqrs-command-query-responsib}](#4-6-cqrs-command-query-responsibility-segregation-6-cqrs-command-query-responsib)
  - [5. D {#d}](#5-d-d)
    - [5 1 Decorator Pattern (装饰器模式) {#1-decorator-pattern-装饰器模式}](#5-1-decorator-pattern-装饰器模式-1-decorator-pattern-装饰器模式)
    - [5 2 Denotational Semantics (指称语义) {#2-denotational-semantics-指称语义}](#5-2-denotational-semantics-指称语义-2-denotational-semantics-指称语义)
    - [5 3 Differential Privacy (差分隐私) {#3-differential-privacy-差分隐私}](#5-3-differential-privacy-差分隐私-3-differential-privacy-差分隐私)
  - [6. E {#e}](#6-e-e)
    - [6 1 Energy Complexity (能量复杂度) {#1-energy-complexity-能量复杂度}](#6-1-energy-complexity-能量复杂度-1-energy-complexity-能量复杂度)
    - [6 2 Event Sourcing (事件溯源) {#2-event-sourcing-事件溯源}](#6-2-event-sourcing-事件溯源-2-event-sourcing-事件溯源)
  - [7. F {#f}](#7-f-f)
    - [7 1 Factory Method (工厂方法模式) {#1-factory-method-工厂方法模式}](#7-1-factory-method-工厂方法模式-1-factory-method-工厂方法模式)
    - [7 2 Formal Semantics (形式语义) {#2-formal-semantics-形式语义}](#7-2-formal-semantics-形式语义-2-formal-semantics-形式语义)
  - [8. G {#g}](#8-g-g)
    - [8 1 GoF (Gang of Four) {#1-gof-gang-of-four}](#8-1-gof-gang-of-four-1-gof-gang-of-four)
  - [9. H {#h}](#9-h-h)
    - [9 1 Hoare Triple (Hoare 三元组) {#1-hoare-triple-hoare-三元组}](#9-1-hoare-triple-hoare-三元组-1-hoare-triple-hoare-三元组)
  - [10. I {#i}](#10-i-i)
    - [10 1 I/O Complexity (I/O 复杂度) {#1-io-complexity-io-复杂度}](#10-1-io-complexity-io-复杂度-1-io-complexity-io-复杂度)
    - [10 2 Ideal-Cache Model (理想缓存模型) {#2-ideal-cache-model-理想缓存模型}](#10-2-ideal-cache-model-理想缓存模型-2-ideal-cache-model-理想缓存模型)
  - [11. K {#k}](#11-k-k)
    - [11 1 K-Framework {#1-k-framework}](#11-1-k-framework-1-k-framework)
    - [11 2 Kolmogorov Complexity (柯尔莫哥洛夫复杂度) {#2-kolmogorov-complexity-柯尔莫哥洛夫}](#11-2-kolmogorov-complexity-柯尔莫哥洛夫复杂度-2-kolmogorov-complexity-柯尔莫哥洛夫)
  - [12. L {#l}](#12-l-l)
    - [12 1 Lambda Calculus (λ-演算) {#1-lambda-calculus-λ-演算}](#12-1-lambda-calculus-λ-演算-1-lambda-calculus-λ-演算)
    - [12 2 Landauer's Principle (Landauer 原理) {#2-landauers-principle-landauer}](#12-2-landauers-principle-landauer-原理-2-landauers-principle-landauer)
  - [13. M {#m}](#13-m-m)
    - [13 1 Model Checking (模型检测) {#1-model-checking-模型检测}](#13-1-model-checking-模型检测-1-model-checking-模型检测)
  - [14. N {#n}](#14-n-n)
    - [14 1 Natural Semantics (自然语义) {#1-natural-semantics-自然语义}](#14-1-natural-semantics-自然语义-1-natural-semantics-自然语义)
  - [15. O {#o}](#15-o-o)
    - [15 1 Observer Pattern (观察者模式) {#1-observer-pattern-观察者模式}](#15-1-observer-pattern-观察者模式-1-observer-pattern-观察者模式)
    - [15 2 Operational Semantics (操作语义) {#2-operational-semantics-操作语义}](#15-2-operational-semantics-操作语义-2-operational-semantics-操作语义)
  - [16. P {#p}](#16-p-p)
    - [16 1 Petri Net (Petri 网) {#1-petri-net-petri-网}](#16-1-petri-net-petri-网-1-petri-net-petri-网)
    - [16 2 π-Calculus (π-演算) {#2-π-calculus-π-演算}](#16-2-π-calculus-π-演算-2-π-calculus-π-演算)
    - [16 3 Privacy Budget (隐私预算) {#3-privacy-budget-隐私预算}](#16-3-privacy-budget-隐私预算-3-privacy-budget-隐私预算)
    - [16 4 Proxy Pattern (代理模式) {#4-proxy-pattern-代理模式}](#16-4-proxy-pattern-代理模式-4-proxy-pattern-代理模式)
  - [17. Q {#q}](#17-q-q)
    - [17 1 QHL (Quantitative Hoare Logic) {#1-qhl-quantitative-hoare-logic}](#17-1-qhl-quantitative-hoare-logic-1-qhl-quantitative-hoare-logic)
  - [18. R {#r}](#18-r-r)
    - [18 1 Rewriting Logic (重写逻辑) {#1-rewriting-logic-重写逻辑}](#18-1-rewriting-logic-重写逻辑-1-rewriting-logic-重写逻辑)
  - [19. S {#s}](#19-s-s)
    - [19 1 Saga Pattern (Saga 模式) {#1-saga-pattern-saga-模式}](#19-1-saga-pattern-saga-模式-1-saga-pattern-saga-模式)
    - [19 2 Sample Complexity (样本复杂度) {#2-sample-complexity-样本复杂度}](#19-2-sample-complexity-样本复杂度-2-sample-complexity-样本复杂度)
    - [19 3 Singleton Pattern (单例模式) {#3-singleton-pattern-单例模式}](#19-3-singleton-pattern-单例模式-3-singleton-pattern-单例模式)
    - [19 4 Small-step Semantics (小步语义) {#4-small-step-semantics-小步语义}](#19-4-small-step-semantics-小步语义-4-small-step-semantics-小步语义)
    - [19 5 Span (跨度) {#5-span-跨度}](#19-5-span-跨度-5-span-跨度)
    - [19 6 Strategy Pattern (策略模式) {#6-strategy-pattern-策略模式}](#19-6-strategy-pattern-策略模式-6-strategy-pattern-策略模式)
  - [20. T {#t}](#20-t-t)
    - [20 1 Theorem Prover (定理证明器) {#1-theorem-prover-定理证明器}](#20-1-theorem-prover-定理证明器-1-theorem-prover-定理证明器)
    - [20 2 Time Complexity (时间复杂度) {#2-time-complexity-时间复杂度}](#20-2-time-complexity-时间复杂度-2-time-complexity-时间复杂度)
    - [20 3 Type System (类型系统) {#3-type-system-类型系统}](#20-3-type-system-类型系统-3-type-system-类型系统)
  - [21. U {#u}](#21-u-u)
    - [21 1 UH-Cost (Unified Hypergraph-Cost Model) {#1-uh-cost-unified-hypergraph-c}](#21-1-uh-cost-unified-hypergraph-cost-model-1-uh-cost-unified-hypergraph-c)
  - [22. V {#v}](#22-v-v)
    - [22 1 Verifiability (可验证性) {#1-verifiability-可验证性}](#22-1-verifiability-可验证性-1-verifiability-可验证性)
  - [23. W {#w}](#23-w-w)
    - [23 1 Work (工作量) {#1-work-工作量}](#23-1-work-工作量-1-work-工作量)
    - [23 2 Workflow Pattern (工作流模式) {#2-workflow-pattern-工作流模式}](#23-2-workflow-pattern-工作流模式-2-workflow-pattern-工作流模式)
  - [24. Z {#z}](#24-z-z)
    - [24 1 Z3 {#1-z3}](#24-1-z3-1-z3)
  - [25. 缩写表 {#缩写表}](#25-缩写表-缩写表)
  - [26. 符号表 {#符号表}](#26-符号表-符号表)
  - [27. 扩展阅读 {#扩展阅读}](#27-扩展阅读-扩展阅读)
  - [关联网络](#关联网络)
    - [前向引用](#前向引用)
    - [后向引用](#后向引用)
    - [交叉链接](#交叉链接)

- --

## 1. 📋 索引 {#-索引}

[A](#a) | [B](#b) | [C](#c) | [D](#d) | [E](#e) | [F](#f) | [G](#g) | [H](#h) | [I](#i) | [K](#k) | [L](#l) | [M](#m) | [N](#n) | [O](#o) | [P](#p) | [Q](#q) | [R](#r) | [S](#s) | [T](#t) | [U](#u) | [V](#v) | [W](#w) | [Z](#z)

- --

## 2. A {#a}

### 2 1 Abstract Factory (抽象工厂模式) {#1-abstract-factory-抽象工厂模式}

- _定义_*: 提供一个创建一系列相关或相互依赖对象的接口，而无需指定它们具体的类。

- _形式化_*:

```coq
Record AbstractFactory : Type := {
  create : Product -> object
}.
```

- _相关_*: [02.1_GoF_Formal_Analysis.md](02_Design_Patterns/02.1_GoF_Formal_Analysis.md)

- --

### 2 2 Adaptivity (自适应性) {#2-adaptivity-自适应性}

- _定义_*: 算法根据中间结果动态调整后续查询或决策的能力。

- _度量_*: 轮次数（自适应轮）vs 总查询数

- _示例_*: 随机梯度下降（自适应学习率）

- _相关_*: [03.1_Multidimensional_Complexity.md](03_Algorithm_Complexity/03.1_Multidimensional_Complexity.md#adaptivity)

- --

### 2 3 Axiomatic Semantics (公理语义) {#3-axiomatic-semantics-公理语义}

- _定义_*: 通过逻辑公式（前置条件、后置条件）描述程序性质的语义方法。

- _形式_*: Hoare 三元组 `{P} c {Q}`

- _工具_*: Dafny, Why3, Frama-C

- _相关_*: [01.3_Axiomatic_Semantics.md](01_Formal_Semantics/01.3_Axiomatic_Semantics.md)

- --

## 3. B {#b}

### 3 1 Big-step Semantics (大步语义) {#1-big-step-semantics-大步语义}

- _定义_*: 直接求值到最终结果的操作语义，也称自然语义 (Natural Semantics)。

- _判断形式_*: `e ⇓ v`

- _对比_*: Small-step Semantics (小步语义)

- _相关_*: [01.1_Operational_Semantics.md](01_Formal_Semantics/01.1_Operational_Semantics.md#big-step)

- --

### 3 2 Builder Pattern (建造者模式) {#2-builder-pattern-建造者模式}

- _定义_*: 将一个复杂对象的构建与它的表示分离，使得同样的构建过程可以创建不同的表示。

- _特点_*: 链式调用、分步构造

- _相关_*: [02.1_GoF_Formal_Analysis.md](02_Design_Patterns/02.1_GoF_Formal_Analysis.md#builder)

- --

## 4. C {#c}

### 4 1 Cache Complexity (缓存复杂度) {#1-cache-complexity-缓存复杂度}

- _定义_*: 缓存未命中 (cache miss) 的次数。

- _模型_*: Ideal-Cache 模型（全相联、LRU、参数 Z 和 L）

- _典型下界_*: 矩阵乘法 Ω(n³/√Z)

- _相关_*: [03.1_Multidimensional_Complexity.md](03_Algorithm_Complexity/03.1_Multidimensional_Complexity.md#cache)

- --

### 4 2 Cache-oblivious Algorithm (缓存无关算法) {#2-cache-oblivious-algorithm-缓存}

- _定义_*: 无需知道缓存参数 Z 和 L 就能达到渐近最优缓存性能的算法。

- _典型例子_*: 递归矩阵乘法、Funnelsort

- _优势_*: 可移植性、自适应多级缓存

- _参考_*: [Wikipedia](https://en.wikipedia.org/wiki/Cache-oblivious_algorithm)

- --

### 4 3 Communication Complexity (通讯复杂度) {#3-communication-complexity-通讯复}

- _定义_*: 分布式算法中传输的总比特数。

- _模型_*:

- 2-party (Alice & Bob)
- multi-party (n 个参与方)

- _经典问题_*: DISJ (不相交集判定) 下界 Ω(n)

- _相关_*: [03.1_Multidimensional_Complexity.md](03_Algorithm_Complexity/03.1_Multidimensional_Complexity.md#communication)

- --

### 4 4 Composite Pattern (组合模式) {#4-composite-pattern-组合模式}

- _定义_*: 将对象组合成树形结构以表示"部分-整体"的层次结构，使得用户对单个对象和组合对象的使用具有一致性。

- _形式化_*: 代数数据类型 `data Component = Leaf a | Node [Component a]`

- _相关_*: [02.1_GoF_Formal_Analysis.md](02_Design_Patterns/02.1_GoF_Formal_Analysis.md#composite)

- --

### 4 5 Cost Semantics (成本语义) {#5-cost-semantics-成本语义}

- _定义_*: 在操作语义上附加资源计数器，精确追踪资源消耗。

- _形式_*: `⟨e, σ, κ⟩ → ⟨e', σ', κ'⟩` 其中 κ ∈ ℕ^d 是 d 维资源向量

- _应用_*: 验证时间/空间/能量界

- _相关_*: [01.1_Operational_Semantics.md](01_Formal_Semantics/01.1_Operational_Semantics.md#cost-semantics)

- --

### 4 6 CQRS (Command Query Responsibility Segregation) {#6-cqrs-command-query-responsib}

- _定义_*: 命令查询职责分离，读写操作使用不同的模型。

- _形式化_*: `Command → Event*; Query → View`

- _优势_*: 读写独立扩展、事件溯源

- _相关_*: [02.2_Distributed_Patterns.md](02_Design_Patterns/02.2_Distributed_Patterns.md)

- --

## 5. D {#d}

### 5 1 Decorator Pattern (装饰器模式) {#1-decorator-pattern-装饰器模式}

- _定义_*: 动态地给一个对象添加一些额外的职责，就增加功能来说，Decorator 模式相比生成子类更为灵活。

- _形式化_*: 函数组合 `Decorator : Component -> Component`

- _性质_*: 结合律 `(D₁ ∘ D₂) ∘ D₃ ≡ D₁ ∘ (D₂ ∘ D₃)`

- _相关_*: [02.1_GoF_Formal_Analysis.md](02_Design_Patterns/02.1_GoF_Formal_Analysis.md#decorator)

- --

### 5 2 Denotational Semantics (指称语义) {#2-denotational-semantics-指称语义}

- _定义_*: 将程序映射到数学对象（通常是函数或域）的语义方法。

- _核心_*: 语义函数 `⟦·⟧ : Expr → Domain`

- _优势_*: 组合性强、易于数学推理

- _相关_*: [01.2_Denotational_Semantics.md](01_Formal_Semantics/01.2_Denotational_Semantics.md)

- --

### 5 3 Differential Privacy (差分隐私) {#3-differential-privacy-差分隐私}

- _定义_*: 保证单条记录的添加或删除对算法输出分布的影响有界。

- _形式_*: `Pr[A(D) ∈ S] ≤ e^ε · Pr[A(D') ∈ S] + δ`

- _参数_*: ε (隐私预算), δ (失败概率)

- _相关_*: [03.1_Multidimensional_Complexity.md](03_Algorithm_Complexity/03.1_Multidimensional_Complexity.md#privacy)

- --

## 6. E {#e}

### 6 1 Energy Complexity (能量复杂度) {#1-energy-complexity-能量复杂度}

- _定义_*: 算法执行的比特翻转次数，衡量能量消耗。

- _物理基础_*: Landauer 极限 (kT ln 2)

- _典型下界_*: n-bit 乘法 Ω(n²)

- _相关_*: [03.1_Multidimensional_Complexity.md](03_Algorithm_Complexity/03.1_Multidimensional_Complexity.md#energy)

- --

### 6 2 Event Sourcing (事件溯源) {#2-event-sourcing-事件溯源}

- _定义_*: 将所有状态变更存储为事件序列，当前状态通过重放事件计算得到。

- _形式化_*: `State = fold Event* σ₀`

- _优势_*: 完整审计日志、时间旅行查询

- _相关_*: [02.2_Distributed_Patterns.md](02_Design_Patterns/02.2_Distributed_Patterns.md)

- --

## 7. F {#f}

### 7 1 Factory Method (工厂方法模式) {#1-factory-method-工厂方法模式}

- _定义_*: 定义一个创建对象的接口，让子类决定实例化哪一个类。

- _形式化_*: `create : Type -> object` (子类重写)

- _参考_*: [Wikipedia](https://en.wikipedia.org/wiki/Factory_method_pattern)

- _相关_*: [02.1_GoF_Formal_Analysis.md](02_Design_Patterns/02.1_GoF_Formal_Analysis.md)

- --

### 7 2 Formal Semantics (形式语义) {#2-formal-semantics-形式语义}

- _定义_*: 用数学方法精确定义程序行为的语义学。

- _三大类_*:

1. 操作语义 (Operational)
2. 指称语义 (Denotational)
3. 公理语义 (Axiomatic)

- _参考_*: [Wikipedia](https://en.wikipedia.org/wiki/Formal_semantics_of_programming_languages)

- _相关_*: [01_Formal_Semantics/](01_Formal_Semantics/)

- --

## 8. G {#g}

### 8 1 GoF (Gang of Four) {#1-gof-gang-of-four}

- _定义_*: Gamma, Helm, Johnson, Vlissides 四位作者，1994 年出版《Design Patterns》。

- _贡献_*: 定义了 23 个经典设计模式

- _分类_*: 创建型、结构型、行为型

- _参考_*: [Wikipedia](https://en.wikipedia.org/wiki/Design_Patterns)

- --

## 9. H {#h}

### 9 1 Hoare Triple (Hoare 三元组) {#1-hoare-triple-hoare-三元组}

- _定义_*: 公理语义的核心判断形式 `{P} c {Q}`

- _含义_*:

- P: 前置条件 (precondition)
- c: 程序/命令 (command)
- Q: 后置条件 (postcondition)

- _语义_*: 若 P 成立且 c 终止，则 Q 成立

- _相关_*: [01.3_Axiomatic_Semantics.md](01_Formal_Semantics/01.3_Axiomatic_Semantics.md)

- --

## 10. I {#i}

### 10 1 I/O Complexity (I/O 复杂度) {#1-io-complexity-io-复杂度}

- _定义_*: 读写外部存储的块数。

- _模型_*: Aggarwal-Vitter 模型 (参数 M, B, N)

- _排序下界_*: Θ((N/B) log_{M/B} (N/B))

- _相关_*: [03.1_Multidimensional_Complexity.md](03_Algorithm_Complexity/03.1_Multidimensional_Complexity.md#io), [03.5_External_Memory_Algorithms.md](03_Algorithm_Complexity/03.5_External_Memory_Algorithms.md)

- --

### 10 2 Ideal-Cache Model (理想缓存模型) {#2-ideal-cache-model-理想缓存模型}

- _定义_*: 假设全相联、LRU 替换、离线最优的缓存模型。

- _参数_*:

- Z: 缓存大小
- L: 缓存行大小

- _用途_*: 分析缓存复杂度的理论模型

- _相关_*: [03.1_Multidimensional_Complexity.md](03_Algorithm_Complexity/03.1_Multidimensional_Complexity.md#cache)

- --

## 11. K {#k}

### 11 1 K-Framework {#1-k-framework}

- _定义_*: 基于重写逻辑的编程语言语义框架。

- _特点_*:

- 可执行语义（定义即解释器）
- 自动生成符号执行器
- 支持模型检测

- _官网_*: <https://kframework.org/>

- _相关_*: [05.3_K_Framework.md](05_Formal_Verification/05.3_K_Framework.md)

- --

### 11 2 Kolmogorov Complexity (柯尔莫哥洛夫复杂度) {#2-kolmogorov-complexity-柯尔莫哥洛夫}

- _定义_*: 生成字符串 x 的最短程序长度 K(x)。

- _性质_*:

- 不可计算
- H(X) ≈ E[K(X)] (期望近似)

- _应用_*: 信息论下界、随机性度量

- _相关_*: [../../Information_Theory_Perspective/](../../Information_Theory_Perspective/)

- --

## 12. L {#l}

### 12 1 Lambda Calculus (λ-演算) {#1-lambda-calculus-λ-演算}

- _定义_*: 形式化函数定义、应用和递归的计算模型。

- _语法_*: `e ::= x | λx.e | e e`

- _性质_*: 图灵完备

- _应用_*: 函数式编程语言的理论基础

- _参考_*: [Wikipedia](https://en.wikipedia.org/wiki/Lambda_calculus)

- --

### 12 2 Landauer's Principle (Landauer 原理) {#2-landauers-principle-landauer}

- _定义_*: 擦除 1 比特信息至少需要 kT ln 2 的能量。

- _意义_*: 计算的热力学极限

- _温度_*: 室温下 ≈ 3×10⁻²¹ J

- _相关_*: [03.1_Multidimensional_Complexity.md](03_Algorithm_Complexity/03.1_Multidimensional_Complexity.md#energy)

- --

## 13. M {#m}

### 13 1 Model Checking (模型检测) {#1-model-checking-模型检测}

- _定义_*: 自动验证有限状态系统是否满足时序逻辑性质的技术。

- _逻辑_*: CTL, LTL, μ-演算

- _工具_*: mCRL2, UPPAAL, SPIN, TLA+

- _应用_*: 并发系统、分布式协议验证

- _相关_*: [05.2_Model_Checking_Tools.md](05_Formal_Verification/05.2_Model_Checking_Tools.md)

- --

## 14. N {#n}

### 14 1 Natural Semantics (自然语义) {#1-natural-semantics-自然语义}

- _定义_*: Big-step Semantics 的别名，见 [Big-step Semantics](#big-step-semantics-大步语义)。

- --

## 15. O {#o}

### 15 1 Observer Pattern (观察者模式) {#1-observer-pattern-观察者模式}

- _定义_*: 定义对象间的一对多依赖关系，当一个对象状态改变时，所有依赖于它的对象都得到通知并自动更新。

- _形式化_*: π-演算 `Subject | Observer₁ | ... | ObserverN`

- _性质_*:

- 无死锁 (AG ¬deadlock)
- 通讯线性 (Comm = N·|state|)

- _相关_*: [02.1_GoF_Formal_Analysis.md](02_Design_Patterns/02.1_GoF_Formal_Analysis.md#observer)

- --

### 15 2 Operational Semantics (操作语义) {#2-operational-semantics-操作语义}

- _定义_*: 通过定义程序如何逐步执行来给出程序意义的语义方法。

- _两种形式_*:

1. Small-step (小步语义)
2. Big-step (大步语义)

- _参考_*: [Wikipedia](https://en.wikipedia.org/wiki/Operational_semantics)

- _相关_*: [01.1_Operational_Semantics.md](01_Formal_Semantics/01.1_Operational_Semantics.md)

- --

## 16. P {#p}

### 16 1 Petri Net (Petri 网) {#1-petri-net-petri-网}

- _定义_*: 用于并发系统建模的数学工具。

- _组成_*:

- Place (库所)
- Transition (变迁)
- Token (托肯)
- Arc (弧)

- _应用_*: 工作流、并发系统验证

- _相关_*: [02.3_Workflow_Patterns.md](02_Design_Patterns/02.3_Workflow_Patterns.md)

- --

### 16 2 π-Calculus (π-演算) {#2-π-calculus-π-演算}

- _定义_*: 描述并发计算的进程代数，支持通道传递。

- _语法_*: `P ::= 0 | a(x).P | ā⟨M⟩.P | P|Q | νa.P | !P`

- _特点_*: 移动性（通道可作为消息传递）

- _应用_*: 并发模式形式化

- _参考_*: [Wikipedia](https://en.wikipedia.org/wiki/Pi-calculus)

- --

### 16 3 Privacy Budget (隐私预算) {#3-privacy-budget-隐私预算}

- _定义_*: 差分隐私中的 ε 参数，越小越隐私。

- _性质_*: 可组合性（ε₁ + ε₂）

- _典型值_*: ε ∈ [0.1, 10]

- _相关_*: [03.1_Multidimensional_Complexity.md](03_Algorithm_Complexity/03.1_Multidimensional_Complexity.md#privacy)

- --

### 16 4 Proxy Pattern (代理模式) {#4-proxy-pattern-代理模式}

- _定义_*: 为其他对象提供一种代理以控制对这个对象的访问。

- _类型_*: 虚拟代理、保护代理、远程代理、缓存代理

- _形式化_*: π-演算 `Proxy | Subject` 行为等价

- _相关_*: [02.1_GoF_Formal_Analysis.md](02_Design_Patterns/02.1_GoF_Formal_Analysis.md#proxy)

- --

## 17. Q {#q}

### 17 1 QHL (Quantitative Hoare Logic) {#1-qhl-quantitative-hoare-logic}

- _定义_*: 定量霍尔逻辑，扩展 Hoare Logic 支持资源界。

- _形式_*: `{P ∧ κ=K} c {Q ∧ κ≤K+Δ}`

- _应用_*: 验证时间/空间/能量界

- --

## 18. R {#r}

### 18 1 Rewriting Logic (重写逻辑) {#1-rewriting-logic-重写逻辑}

- _定义_*: 基于项重写的逻辑系统。

- _语法_*: `L ⟹ R`

- _工具_*: Maude, K-Framework

- _应用_*: 语言语义定义、并发系统建模

- _相关_*: [05.3_K_Framework.md](05_Formal_Verification/05.3_K_Framework.md)

- --

## 19. S {#s}

### 19 1 Saga Pattern (Saga 模式) {#1-saga-pattern-saga-模式}

- _定义_*: 分布式长事务模式，通过补偿操作保证最终一致性。

- _形式化_*: `comp₁;...;compₙ; compensateᵢ`

- _性质_*: `fold compensate σᵢ = σ₀` (可补偿性)

- _相关_*: [02.2_Distributed_Patterns.md](02_Design_Patterns/02.2_Distributed_Patterns.md)

- --

### 19 2 Sample Complexity (样本复杂度) {#2-sample-complexity-样本复杂度}

- _定义_*: 学习算法达到目标精度所需的样本数。

- _VC 维下界_*: Ω(d/ε)

- _应用_*: 机器学习理论

- _相关_*: [03.1_Multidimensional_Complexity.md](03_Algorithm_Complexity/03.1_Multidimensional_Complexity.md#sample)

- --

### 19 3 Singleton Pattern (单例模式) {#3-singleton-pattern-单例模式}

- _定义_*: 保证一个类仅有一个实例，并提供一个全局访问点。

- _形式化_*: 线性类型 `⊢ ∀ r1 r2 : &mut Singleton, r1 ≡ r2`

- _实现_*: 懒汉式、饿汉式、双重检查锁定

- _相关_*: [02.1_GoF_Formal_Analysis.md](02_Design_Patterns/02.1_GoF_Formal_Analysis.md#singleton)

- --

### 19 4 Small-step Semantics (小步语义) {#4-small-step-semantics-小步语义}

- _定义_*: 每次执行一个原子操作的操作语义。

- _判断形式_*: `⟨e, σ⟩ → ⟨e', σ'⟩`

- _优势_*: 可建模中间状态、并发、非终止

- _相关_*: [01.1_Operational_Semantics.md](01_Formal_Semantics/01.1_Operational_Semantics.md#small-step)

- --

### 19 5 Span (跨度) {#5-span-跨度}

- _定义_*: 并行算法的关键路径长度（最长依赖链）。

- _Work-Span 模型_*:

- Work = 总操作数
- Span = 关键路径长度
- 并行度 = Work / Span

- _相关_*: [03.4_Parallel_Algorithms.md](03_Algorithm_Complexity/03.4_Parallel_Algorithms.md)

- --

### 19 6 Strategy Pattern (策略模式) {#6-strategy-pattern-策略模式}

- _定义_*: 定义一系列算法，把它们一个个封装起来，并且使它们可以互相替换。

- _形式化_*: `Context : ∀α. Strategy α -> α`

- _性质_*: 可替换性 `ctx s1 ≡ ctx s2`

- _相关_*: [02.1_GoF_Formal_Analysis.md](02_Design_Patterns/02.1_GoF_Formal_Analysis.md#strategy)

- --

## 20. T {#t}

### 20 1 Theorem Prover (定理证明器) {#1-theorem-prover-定理证明器}

- _定义_*: 交互式或自动化证明数学定理的软件工具。

- _主流工具_*:

- Coq (依赖类型)
- Lean4 (数学库丰富)
- Isabelle/HOL (高阶逻辑)

- _应用_*: 程序验证、数学定理证明

- _相关_*: [05.1_Coq_Introduction.md](05_Formal_Verification/05.1_Coq_Introduction.md)

- --

### 20 2 Time Complexity (时间复杂度) {#2-time-complexity-时间复杂度}

- _定义_*: 算法执行的指令数或基本操作数。

- _表示法_*: O, Ω, Θ

- _经典下界_*: 排序 Ω(n log n)

- _相关_*: [03.1_Multidimensional_Complexity.md](03_Algorithm_Complexity/03.1_Multidimensional_Complexity.md#time)

- --

### 20 3 Type System (类型系统) {#3-type-system-类型系统}

- _定义_*: 用类型约束程序行为的形式化系统。

- _类型_*:

- 简单类型 (Simple Types)
- 依赖类型 (Dependent Types)
- 线性类型 (Linear Types)
- 定量类型 (Quantitative Types)

- _性质_*: Type Safety (Progress + Preservation)

- _相关_*: [01.4_Type_Systems.md](01_Formal_Semantics/01.4_Type_Systems.md)

- --

## 21. U {#u}

### 21 1 UH-Cost (Unified Hypergraph-Cost Model) {#1-uh-cost-unified-hypergraph-c}

- _定义_*: 统一超图成本模型，本项目提出的形式化框架。

- _形式_*: `UH-Cost = ⟨Σ, ⟶, κ, Φ⟩`

- _应用_*: 统一设计模式、算法、架构的形式化

- _相关_*: [README.md](README.md#uh-cost)

- --

## 22. V {#v}

### 22 1 Verifiability (可验证性) {#1-verifiability-可验证性}

- _定义_*: 生成和验证计算正确性证明的资源消耗。

- _维度_*:

- 证明长度
- 验证时间

- _技术_*: PCP, SNARK, STARK

- _相关_*: [03.1_Multidimensional_Complexity.md](03_Algorithm_Complexity/03.1_Multidimensional_Complexity.md#verifiability)

- --

## 23. W {#w}

### 23 1 Work (工作量) {#1-work-工作量}

- _定义_*: 并行算法的总操作数（时间 × 处理器数）。

- _关系_*: `T_parallel · P ≥ Work`

- _相关_*: [Span](#span-跨度), [03.4_Parallel_Algorithms.md](03_Algorithm_Complexity/03.4_Parallel_Algorithms.md)

- --

### 23 2 Workflow Pattern (工作流模式) {#2-workflow-pattern-工作流模式}

- _定义_*: 业务流程建模中的可复用控制流模式。

- _基础模式_*: Sequence, XOR-Split, AND-Split, XOR-Join, AND-Join

- _形式化_*: Petri 网、BPMN

- _相关_*: [02.3_Workflow_Patterns.md](02_Design_Patterns/02.3_Workflow_Patterns.md)

- --

## 24. Z {#z}

### 24 1 Z3 {#1-z3}

- _定义_*: Microsoft Research 开发的 SMT (Satisfiability Modulo Theories) 求解器。

- _应用_*: 符号执行、程序综合、约束求解

- _官网_*: <https://github.com/Z3Prover/z3>

- _相关_*: [05.4_Symbolic_Execution.md](05_Formal_Verification/05.4_Symbolic_Execution.md)

- --

## 25. 缩写表 {#缩写表}

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

- --

## 26. 符号表 {#符号表}

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

- --

## 27. 扩展阅读 {#扩展阅读}

- [00_Master_Index.md](00_Master_Index.md) - 主索引
- [README.md](README.md) - 总体概述
- [REFERENCES.md](REFERENCES.md) - 参考文献
- [LEARNING_PATHS.md](LEARNING_PATHS.md) - 学习路径

- --

- _最后更新_*: 2025-10-29
- _维护者_*: FormalScience Team
- _许可_*: MIT License


---

## 关联网络

### 前向引用

> 本文档为以下文档提供基础：
>
> - [相关文档](./README.md) (待补充)

### 后向引用

> 本文档依赖以下基础文档：
>
> - [基础文档](./README.md) (待补充)

### 交叉链接

> 相关主题：
>
> - [主题A](./README.md) (待补充)
> - [主题B](./README.md) (待补充)

---

_本文档由 FormalScience 文档规范化工具自动生成_
