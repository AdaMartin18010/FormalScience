# 指称语义 (Denotational Semantics)

## 概述

指称语义是一种形式化方法，通过将语法结构映射到数学对象（通常是函数）来描述程序的含义。与操作语义关注"如何执行"不同，指称语义关注"表示什么"，即程序的数学含义。指称语义强调组合性原则，复合表达式的含义由其组成部分的含义组合而成。

## 本目录内容

本目录包含与指称语义相关的文档：

- [03.5.2_Denotational_Semantics.md](../03.5.2_Denotational_Semantics.md) - 指称语义的英文详细介绍
- [03.5.2_指称语义.md](./03.5.2_指称语义.md) - 指称语义的中文详细介绍

## 主要概念

1. **语义函数 (Semantic Function)**
   - 将语法结构映射到语义域中的元素
   - 形式表示：$\mathcal{E}[\![e]\!] : \text{State} \rightarrow \text{Value}$

2. **语义域 (Semantic Domain)**
   - 语言表达式的含义所属的数学结构，如状态集合、函数空间或代数结构

3. **组合性原则 (Compositionality)**
   - 复合表达式的语义可以由其组成部分的语义组合而成
   - 例如：$\mathcal{E}[\![e_1 + e_2]\!]\sigma = \mathcal{E}[\![e_1]\!]\sigma + \mathcal{E}[\![e_2]\!]\sigma$

4. **域理论 (Domain Theory)**
   - 提供数学基础，处理递归定义和不动点
   - 包括完全偏序集、连续函数和不动点定理

## 相关主题

- [操作语义](README.md) - 基于状态转换的语义模型
- [公理语义](README.md) - 基于逻辑的语义模型
- [代数语义](README.md) - 基于代数结构的语义模型

## 参考资源

- Scott, D. & Strachey, C. (1971). Toward a Mathematical Semantics for Computer Languages.
- Stoy, J. E. (1977). Denotational Semantics: The Scott-Strachey Approach to Programming Language Theory.
- Schmidt, D. A. (1986). Denotational Semantics: A Methodology for Language Development.


## 批判性分析

- 本节内容待补充：请从多元理论视角、局限性、争议点、应用前景等方面进行批判性分析。
