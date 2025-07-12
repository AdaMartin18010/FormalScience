---
**文档编号**: 03-00-LOGIC
**创建时间**: 2024-12-21
**最后更新**: 2025-01-18
**版本**: 2.0 (重构版)
**状态**: 持续构建中
---

# 03 逻辑理论 (Logic Theory)

## 模块索引

- **03.1 [命题逻辑 (Propositional Logic)](./03.1_Propositional_Logic/)**
- **03.2 [谓词逻辑 (Predicate Logic)](./03.2_Predicate_Logic/)**
- **03.3 [模态逻辑 (Modal Logic)](./03.3_Modal_Logic/)**
- **03.4 [时态逻辑 (Temporal Logic)](./03.4_Temporal_Logic/)**
- **03.5 [直觉主义逻辑 (Intuitionistic Logic)](./03.5_Intuitionistic_Logic/)**
- 占位符: *非经典逻辑 (Non-classical Logic)*
- 占位符: *高阶逻辑 (Higher-order Logic)*

---

## 概述

逻辑理论是形式化科学的基石，专注于研究推理的原则、有效性和数学结构。本模块系统性地组织和阐述了从经典的命题逻辑、谓词逻辑到各种非经典逻辑（如模态逻辑、时态逻辑）的核心概念、形式系统、证明论和模型论。

## 理论基础

### 形式化定义

**定义 3.1 (逻辑系统)** 逻辑系统是一个三元组 $\mathcal{L} = (L, \vdash, \models)$，其中：

- $L$ 是由语法规则定义的良构公式集合。
- $\vdash$ 是一个语法上的**推导关系** (Syntactic Entailment)，表示可以从一组前提出发，通过推理规则导出结论。
- $\models$ 是一个语义上的**满足关系** (Semantic Entailment)，表示在一组前提为真的所有模型中，结论也为真。

**核心性质：**

- **可靠性 (Soundness)**: 如果 $\Gamma \vdash \phi$，那么 $\Gamma \models \phi$。 (所有能被证明的都是真的)
- **完备性 (Completeness)**: 如果 $\Gamma \models \phi$，那么 $\Gamma \vdash \phi$。 (所有真的都能被证明)

---

## 交叉引用

### 内部学科链接

- **[01 哲学基础](../01_Philosophical_Foundations/README.md)**: 为逻辑的本质、真理和悖论提供哲学背景。
- **[02 数学基础](../02_Mathematical_Foundations/README.md)**: 逻辑是构建数学证明和公理系统的基础。
- **[04 形式语言理论](../04_Formal_Language_Theory/README.md)**: 逻辑语言本身就是一种形式语言。

### 外部学科链接

- **[05 类型理论](../05_Type_Theory/README.md)**: Curry-Howard同构揭示了逻辑与计算之间的深刻联系。
- **[09 计算机体系结构](../09_Computer_Architecture_Theory/01_Digital_Logic_Design/README.md)**: 命题逻辑是数字电路设计的基础。
- **[13 人工智能理论](../13_Artificial_Intelligence_Theory/README.md)**: 逻辑是知识表示和自动推理的核心工具。

---

## 返回

- [返回 Refactor 主索引](../README.md)
