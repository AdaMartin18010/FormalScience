# 05 类型理论 (Type Theory)

## 模块概述

类型理论是数学、逻辑和计算机科学的交叉领域，它使用"类型"来防止逻辑悖论和验证程序正确性。本模块全面介绍了从简单类型论到同伦类型论等高级主题，旨在为程序语言设计、软件验证和形式化数学提供坚实的理论基础。

## 模块结构

本模块根据理论的复杂性和依赖关系进行组织，结构如下：

```text
05_Type_Theory/
├── README.md                           # 本文件，模块总览
├── 05.1_Simple_Type_Theory/            # 简单类型理论
│   ├── 05.1_Simple_Type_Theory.md
│   ├── 05.1.1_Simply_Typed_Lambda_Calculus.md
│   ├── 05.1.2_Hindley_Milner.md
│   └── 05.1.3_System_F.md
├── 05.2_Dependent_Type_Theory/         # 依赖类型理论
│   ├── 05.2_Dependent_Type_Theory.md
│   ├── 05.2.1_Dependent_Types_Formalism.md
│   ├── 05.2.2_Type_Families.md
│   ├── 05.2.3_Program_Verification.md
│   ├── 05.2.4_Specification_Languages.md
│   └── 05.2.5_Dependent_Type_System.md
├── 05.3_Linear_Type_Theory/            # 线性类型理论 (及其变体)
│   ├── 05.3_Linear_Type_Theory.md
│   ├── 05.3.1_Linear_Type_Theory_Intro.md
│   ├── 05.3.2_Affine_Type_Theory.md
│   ├── 05.3.3_Linear_Function_Types.md
│   ├── 05.3.4_Linear_Data_Structures.md
│   ├── 05.3.5_Linear_Type_System.md
│   ├── 05.3.6_Affine_Type_Basics.md
│   ├── 05.3.7_Ownership_System.md
│   ├── 05.3.8_Memory_Management.md
│   └── 05.3.9_Concurrent_Types.md
├── 05.4_Homotopy_Type_Theory/          # 同伦类型理论
│   ├── 05.4_Homotopy_Type_Theory.md
│   ├── 05.4.1_Homotopy_Theory.md
│   ├── 05.4.2_Identity_Types.md
│   ├── 05.4.3_Homotopy_Equivalence.md
│   ├── 05.4.4_Higher_Inductive_Types.md
│   └── 05.4.5_Homotopy_Invariants.md
├── 05.5_Curry_Howard_Correspondence/   # Curry-Howard同构
│   └── 05.5_Curry_Howard_Correspondence.md
└── _legacy/                            # 遗留文件，待整理
```

## 核心概念

### 1. **简单类型理论 (Simple Type Theory)**

- **核心思想**: 为lambda演算中的每个项分配一个类型，以避免罗素悖论等问题。
- **关键内容**: 简单类型lambda演算 (STLC)、Hindley-Milner类型系统、多态lambda演算 (System F)。

### 2. **依赖类型理论 (Dependent Type Theory)**

- **核心思想**: 允许类型依赖于值。这使得类型系统具有更强的表达能力，能够描述更复杂的程序不变量。
- **关键内容**: Pi-types (依赖函数类型)、Sigma-types (依赖对类型)、类型族、程序验证。

### 3. **线性类型理论 (Linear Type Theory)**

- **核心思想**: 将类型视为资源，每个资源（值）必须被"使用"且仅使用一次。
- **关键内容**: 线性类型、仿射类型（最多使用一次）、所有权系统（如Rust）、会话类型。

### 4. **同伦类型理论 (Homotopy Type Theory, HoTT)**

- **核心思想**: 将类型解释为拓扑空间，将类型的元素解释为空间中的点，将等价关系解释为点之间的路径。
- **关键内容**: 同一性类型、同伦等价、高阶归纳类型。

### 5. **Curry-Howard 同构 (Curry-Howard Correspondence)**

- **核心思想**: 揭示了计算机程序和数学证明之间的深刻联系，即"命题即类型，证明即程序"。

## 与其他模块的关系

- **[03 逻辑学](.../03_Logic_Theory/README.md)**: 类型论为构造性数学和直觉主义逻辑提供了模型。
- **[03 形式语言理论](../03_Formal_Language_Theory/README.md)**: 类型系统可以看作是一种定义良好行为程序的"形式语言"。
- **[07 程序语言理论](../07_Programming_Language_Theory/README.md)**: 类型理论是现代函数式编程语言（如Haskell, Rust, Agda, Idris）设计的理论基石。
- **[08 软件工程理论](../08_Software_Engineering_Theory/README.md)**: 依赖类型为形式化验证和构建高可靠性软件提供了强大的工具。

---

[返回Refactor主目录](README.md)

---

> 本索引严格树形编号，所有内容均有本地跳转锚点和交叉引用。内容持续规范化中。

## 批判性分析

- 本节内容待补充：请从多元理论视角、局限性、争议点、应用前景等方面进行批判性分析。
