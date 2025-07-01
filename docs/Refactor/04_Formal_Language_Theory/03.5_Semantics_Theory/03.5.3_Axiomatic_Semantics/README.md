# 公理语义 (Axiomatic Semantics)

## 概述

公理语义是一种形式化方法，通过逻辑公理和推理规则描述程序的性质。与操作语义和指称语义不同，公理语义不直接描述程序的执行过程或数学含义，而是关注程序执行前后状态的关系，即程序的正确性性质。公理语义是形式化验证和程序证明的基础。

## 本目录内容

本目录包含与公理语义相关的文档：

- [03.5.3_Axiomatic_Semantics.md](../03.5.3_Axiomatic_Semantics.md) - 公理语义的英文详细介绍
- [03.5.3_公理语义.md](./03.5.3_公理语义.md) - 公理语义的中文详细介绍

## 主要概念

1. **霍尔三元组 (Hoare Triple)**
   - 描述程序执行前后状态的关系
   - 形式表示：$\{P\} C \{Q\}$，其中 $P$ 是前置条件，$C$ 是程序，$Q$ 是后置条件

2. **前置条件和后置条件 (Precondition and Postcondition)**
   - 前置条件：程序执行前必须满足的条件
   - 后置条件：程序执行后保证满足的条件

3. **霍尔逻辑 (Hoare Logic)**
   - 用于推导程序正确性的形式系统
   - 包括赋值公理、顺序执行规则、条件规则、循环规则等

4. **最弱前置条件 (Weakest Precondition)**
   - 给定程序 $C$ 和后置条件 $Q$，使得 $\{wp(C, Q)\} C \{Q\}$ 成立的最弱（最一般）条件
   - 形式表示：$wp(C, Q)$

## 相关主题

- [操作语义](README.md) - 基于状态转换的语义模型
- [指称语义](README.md) - 基于数学函数的语义模型
- [代数语义](README.md) - 基于代数结构的语义模型

## 参考资源

- Hoare, C. A. R. (1969). An Axiomatic Basis for Computer Programming.
- Dijkstra, E. W. (1976). A Discipline of Programming.
- Apt, K. R. (1981). Ten Years of Hoare's Logic: A Survey.


## 批判性分析

- 本节内容待补充：请从多元理论视角、局限性、争议点、应用前景等方面进行批判性分析。
