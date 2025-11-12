# 04 类型理论索引 (Type Theory Index)

## 📚 目录

- [04 类型理论索引 (Type Theory Index)](#04-类型理论索引-type-theory-index)
  - [📚 目录](#-目录)
  - [📋 概述](#-概述)
  - [📦 结构与导航](#-结构与导航)
  - [📑 学习路径](#-学习路径)
  - [🔗 交叉引用](#-交叉引用)
  - [📖 参考文献](#-参考文献)
  - [批判性分析](#批判性分析)

## 📋 目录

- [1 概述](#1-概述)
- [2 结构与导航](#2-结构与导航)
- [3 学习路径](#3-学习路径)
- [4 交叉引用](#4-交叉引用)
- [5 批判性分析](#5-批判性分析)

---

## 1 概述

类型理论为形式语言、逻辑与编程语言提供统一的语义与证明基础，覆盖从简单类型、线性/仿射、依赖类型到同伦类型的完整谱系，并支撑语言设计、验证与计算机辅助证明。

## 2 结构与导航

```text
04_Type_Theory/
├── 04.1_Simple_Type_Theory.md
│   ├── 04.1.1_Lambda_Calculus.md
│   ├── 04.1.2_Simply_Typed_Lambda_Calculus.md
│   ├── 04.1.3_Hindley_Milner_System.md
│   └── 04.1.4_System_F.md
├── 04.2_Linear_Type_Theory.md
├── 04.3_Affine_Type_Theory.md
├── 04.4_Dependent_Type_Theory.md
│   ├── 04.4.1_Dependent_Function_and_Pair_Types.md
│   └── 04.4.2_Identity_Type.md
├── 04.5_Homotopy_Type_Theory.md
├── 04.5_Curry_Howard_Correspondence/05.5_Curry_Howard_Correspondence.md
├── 04.8_Type_Theory_Applications.md
└── 04.9_Type_Theory_Frontiers.md
```

- 快速链接：
  - 依类型核心：`04.4_Dependent_Type_Theory.md`｜`04.4.1_Dependent_Function_and_Pair_Types.md`｜`04.4.2_Identity_Type.md`
  - 线性/仿射：`04.2_Linear_Type_Theory.md`｜`04.3_Affine_Type_Theory.md`｜`04.2.1_Linear_Logic.md`
  - HoTT/CH：`04.5_Homotopy_Type_Theory.md`｜`04.5_Curry_Howard_Correspondence/05.5_Curry_Howard_Correspondence.md`
  - 应用：`04.8_Type_Theory_Applications.md`

## 3 学习路径

- 基础路径：`λ演算 → STLC → HM → System F`
- 高级路径：`依赖类型 → 构造演算 → HoTT`
- 工程路径：`线性/仿射 → 所有权模型 → Rust/Haskell 代码验证`

## 4 交叉引用

- 03 形式语言：`03.5 语义理论`，`03.6 计算理论`
- 08 编程语言：`08.3 语义`，`08.2 类型系统`，`08.4 编译`
- 09 形式模型：`09.5 形式验证`，`09.4 模型检测`
- 04.5 Curry–Howard 对应：`04.5_Curry_Howard_Correspondence/05.5_Curry_Howard_Correspondence.md`

## 📖 参考文献

1. Pierce, B. C. Types and Programming Languages.
2. Harper, R. Practical Foundations for Programming Languages.
3. Martin-Löf, P. Intuitionistic Type Theory.
4. HoTT Book: Univalent Foundations of Mathematics.
5. Wadler, P. Linear Types Can Change the World.

## 5 批判性分析

- 多元理论视角：
  - Curry–Howard 对应将类型—证明—程序统一；依类型与HoTT 将数学构造内在化，支持可机化证明；线性/仿射类型引入资源语义，连接并发与系统工程。
  - 范畴与语义：笛卡尔闭范畴、对称单闭范畴、依变范畴为类型系统提供语义基座，促进“语法—语义—实现”的可交换图景。
- 局限性分析：
  - 表达力与可判定权衡：强表达（依类型、HoTT）引入类型检查复杂度与编译成本；线性/仿射带来工程心智负担。
  - 生态碎片：证明助手与语言实现差异大（Coq/Lean/Agda/Idris），可移植性与互操作性不足。
- 争议与分歧：
  - “类型即规范”与“测试优先”的工程取舍；强类型保障与开发效率之间的平衡。
  - 一体化证明栈（依类型/HoTT）是否适合作为通用工程底座，存在实践分歧。
- 应用前景：
  - 安全关键系统：以类型化不变量与形式证明护航；在编译器、协议栈、并发库中落地。
  - 可验证开发：类型驱动开发与证明对象工件进入CI流水线，提升证据可追溯性。
- 改进建议：
  - 建立“概念—定理—代码—证据”四联表；提供最小可复现示例（Rust/Haskell + Lean/Coq）。
  - 统一术语与风格基线，添加互操作桥接（导出Agda/Lean草图与测试夹具）。
