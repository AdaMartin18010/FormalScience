# 操作语义 (Operational Semantics)

## 概述

操作语义是一种形式化方法，通过定义抽象机器的状态转换来描述程序的执行行为。它关注程序执行的"如何"，即程序执行过程中状态如何变化。操作语义通常分为大步语义（自然语义）和小步语义（结构化操作语义）两种主要形式。

## 本目录内容

本目录包含与操作语义相关的文档：

- [03.5.1_Operational_Semantics.md](./03.5.1_Operational_Semantics.md) - 操作语义的英文详细介绍
- [03.5.1_操作语义.md](./03.5.1_操作语义.md) - 操作语义的中文详细介绍

## 主要概念

1. **大步语义 (Big-Step Semantics)**
   - 也称为自然语义，一步到位地描述程序结构的完整执行结果
   - 形式表示：$\langle P, \sigma \rangle \Rightarrow v$

2. **小步语义 (Small-Step Semantics)**
   - 也称为结构化操作语义，描述程序执行的每一个基本步骤
   - 形式表示：$\langle P, \sigma \rangle \rightarrow \langle P', \sigma' \rangle$

3. **配置 (Configuration)**
   - 表示程序执行的瞬时状态，通常包括剩余待执行的程序和当前存储状态

4. **推导规则 (Inference Rules)**
   - 定义如何从一个配置转换到另一个配置的规则

## 相关主题

- [指称语义](../03.5.2_Denotational_Semantics/README.md) - 另一种主要的语义模型
- [公理语义](../03.5.3_Axiomatic_Semantics/README.md) - 基于逻辑的语义模型
- [代数语义](../03.5.4_Algebraic_Semantics/README.md) - 基于代数结构的语义模型

## 参考资源

- Plotkin, G. D. (1981). A Structural Approach to Operational Semantics.
- Kahn, G. (1987). Natural Semantics.
- Winskel, G. (1993). The Formal Semantics of Programming Languages: An Introduction.
