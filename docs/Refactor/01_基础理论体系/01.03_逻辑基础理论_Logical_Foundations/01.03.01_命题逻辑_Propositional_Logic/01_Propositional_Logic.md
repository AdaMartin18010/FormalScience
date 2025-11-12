# 1. 命题逻辑 (Propositional Logic)

## 📋 目录

- [1. 命题逻辑 (Propositional Logic)](#1-命题逻辑-propositional-logic)
  - [📋 目录](#-目录)
  - [1 概述](#1-概述)
  - [2 语法](#2-语法)
    - [2.1 命题变量](#21-命题变量)
    - [2.2 逻辑连接词](#22-逻辑连接词)
    - [2.3 合式公式](#23-合式公式)
  - [3 语义](#3-语义)
    - [3.1 真值赋值](#31-真值赋值)
    - [3.2 真值表](#32-真值表)
  - [4 逻辑等价](#4-逻辑等价)
    - [4.1 等价定义](#41-等价定义)
    - [4.2 基本等价律](#42-基本等价律)
  - [5 永真式与矛盾式](#5-永真式与矛盾式)
    - [5.1 基本定义](#51-基本定义)
    - [5.2 重要的永真式](#52-重要的永真式)
  - [6 推理系统](#6-推理系统)
    - [6.1 自然演绎系统](#61-自然演绎系统)
    - [6.2 公理系统](#62-公理系统)
  - [7 完备性定理](#7-完备性定理)
    - [7.1 语义后承](#71-语义后承)
    - [7.2 语法后承](#72-语法后承)
    - [7.3 完备性定理](#73-完备性定理)
  - [8 范式](#8-范式)
    - [8.1 析取范式](#81-析取范式)
    - [8.2 合取范式](#82-合取范式)
  - [9 命题逻辑在计算机科学中的应用](#9-命题逻辑在计算机科学中的应用)
    - [9.1 布尔函数](#91-布尔函数)
    - [9.2 逻辑电路设计](#92-逻辑电路设计)
    - [9.3 形式化验证](#93-形式化验证)
  - [10 总结](#10-总结)
  - [参考文献](#参考文献)
  - [11 批判性分析](#11-批判性分析)

---

## 1 概述

命题逻辑是形式逻辑的基础，研究简单命题之间的逻辑关系。它是计算机科学、人工智能和形式化方法的重要理论基础。

## 2 语法

### 2.1 命题变量

**定义 1.1** (命题变量)
命题变量是表示简单命题的符号，通常用 $p, q, r, \ldots$ 表示。

**定义 1.2** (命题字母表)
命题字母表是命题变量的集合：
$$\mathcal{P} = \{p_1, p_2, p_3, \ldots\}$$

### 2.2 逻辑连接词

**定义 1.3** (逻辑连接词)
命题逻辑包含以下逻辑连接词：

1. **否定** ($\neg$): 非
2. **合取** ($\land$): 且
3. **析取** ($\lor$): 或
4. **蕴含** ($\rightarrow$): 如果...那么
5. **等价** ($\leftrightarrow$): 当且仅当

### 2.3 合式公式

**定义 1.4** (合式公式)
合式公式按以下规则递归定义：

1. **基础**: 每个命题变量 $p \in \mathcal{P}$ 是合式公式
2. **否定**: 如果 $\phi$ 是合式公式，则 $\neg \phi$ 是合式公式
3. **二元连接词**: 如果 $\phi$ 和 $\psi$ 是合式公式，则 $(\phi \land \psi)$、$(\phi \lor \psi)$、$(\phi \rightarrow \psi)$、$(\phi \leftrightarrow \psi)$ 是合式公式

**定义 1.5** (公式集合)
所有合式公式的集合记作 $\mathcal{L}$。

## 3 语义

### 3.1 真值赋值

**定义 1.6** (真值赋值)
真值赋值是从命题变量到真值集合 $\{T, F\}$ 的函数：
$$v: \mathcal{P} \rightarrow \{T, F\}$$

**定义 1.7** (真值函数)
真值函数 $\overline{v}: \mathcal{L} \rightarrow \{T, F\}$ 递归定义如下：

1. $\overline{v}(p) = v(p)$ 对于 $p \in \mathcal{P}$
2. $\overline{v}(\neg \phi) = T$ 当且仅当 $\overline{v}(\phi) = F$
3. $\overline{v}(\phi \land \psi) = T$ 当且仅当 $\overline{v}(\phi) = T$ 且 $\overline{v}(\psi) = T$
4. $\overline{v}(\phi \lor \psi) = T$ 当且仅当 $\overline{v}(\phi) = T$ 或 $\overline{v}(\psi) = T$
5. $\overline{v}(\phi \rightarrow \psi) = T$ 当且仅当 $\overline{v}(\phi) = F$ 或 $\overline{v}(\psi) = T$
6. $\overline{v}(\phi \leftrightarrow \psi) = T$ 当且仅当 $\overline{v}(\phi) = \overline{v}(\psi)$

### 3.2 真值表

**定义 1.8** (真值表)
真值表是表示公式在所有可能真值赋值下真值的表格。

**示例 1.1** (基本连接词的真值表)

| $p$ | $q$ | $\neg p$ | $p \land q$ | $p \lor q$ | $p \rightarrow q$ | $p \leftrightarrow q$ |
|-----|-----|----------|-------------|------------|-------------------|----------------------|
| T   | T   | F        | T           | T          | T                 | T                    |
| T   | F   | F        | F           | T          | F                 | F                    |
| F   | T   | T        | F           | T          | T                 | F                    |
| F   | F   | T        | F           | F          | T                 | T                    |

## 4 逻辑等价

### 4.1 等价定义

**定义 1.9** (逻辑等价)
两个公式 $\phi$ 和 $\psi$ 逻辑等价，记作 $\phi \equiv \psi$，当且仅当对于所有真值赋值 $v$：
$$\overline{v}(\phi) = \overline{v}(\psi)$$

### 4.2 基本等价律

**定理 1.1** (双重否定律)
$$\neg \neg \phi \equiv \phi$$

**定理 1.2** (德摩根律)
$$\neg(\phi \land \psi) \equiv \neg \phi \lor \neg \psi$$
$$\neg(\phi \lor \psi) \equiv \neg \phi \land \neg \psi$$

**定理 1.3** (分配律)
$$\phi \land (\psi \lor \chi) \equiv (\phi \land \psi) \lor (\phi \land \chi)$$
$$\phi \lor (\psi \land \chi) \equiv (\phi \lor \psi) \land (\phi \lor \chi)$$

**定理 1.4** (蕴含的等价形式)
$$\phi \rightarrow \psi \equiv \neg \phi \lor \psi$$

**定理 1.5** (等价的等价形式)
$$\phi \leftrightarrow \psi \equiv (\phi \rightarrow \psi) \land (\psi \rightarrow \phi)$$

## 5 永真式与矛盾式

### 5.1 基本定义

**定义 1.10** (永真式)
公式 $\phi$ 是永真式（重言式），记作 $\models \phi$，当且仅当对于所有真值赋值 $v$：
$$\overline{v}(\phi) = T$$

**定义 1.11** (矛盾式)
公式 $\phi$ 是矛盾式，当且仅当对于所有真值赋值 $v$：
$$\overline{v}(\phi) = F$$

**定义 1.12** (可满足式)
公式 $\phi$ 是可满足的，当且仅当存在真值赋值 $v$ 使得：
$$\overline{v}(\phi) = T$$

### 5.2 重要的永真式

**定理 1.6** (排中律)
$$\models \phi \lor \neg \phi$$

**定理 1.7** (矛盾律)
$$\models \neg(\phi \land \neg \phi)$$

**定理 1.8** (同一律)
$$\models \phi \rightarrow \phi$$

**定理 1.9** (假言三段论)
$$\models (\phi \rightarrow \psi) \land (\psi \rightarrow \chi) \rightarrow (\phi \rightarrow \chi)$$

## 6 推理系统

### 6.1 自然演绎系统

**定义 1.13** (自然演绎)
自然演绎系统包含以下推理规则：

**引入规则**:

- $\land$-I: $\frac{\phi \quad \psi}{\phi \land \psi}$
- $\lor$-I: $\frac{\phi}{\phi \lor \psi}$ 或 $\frac{\psi}{\phi \lor \psi}$
- $\rightarrow$-I: $\frac{[\phi] \quad \psi}{\phi \rightarrow \psi}$
- $\leftrightarrow$-I: $\frac{\phi \rightarrow \psi \quad \psi \rightarrow \phi}{\phi \leftrightarrow \psi}$

**消去规则**:

- $\land$-E: $\frac{\phi \land \psi}{\phi}$ 或 $\frac{\phi \land \psi}{\psi}$
- $\lor$-E: $\frac{\phi \lor \psi \quad [\phi] \quad \chi \quad [\psi] \quad \chi}{\chi}$
- $\rightarrow$-E: $\frac{\phi \rightarrow \psi \quad \phi}{\psi}$
- $\leftrightarrow$-E: $\frac{\phi \leftrightarrow \psi \quad \phi}{\psi}$ 或 $\frac{\phi \leftrightarrow \psi \quad \psi}{\phi}$

**否定规则**:

- $\neg$-I: $\frac{[\phi] \quad \bot}{\neg \phi}$
- $\neg$-E: $\frac{\phi \quad \neg \phi}{\bot}$
- $\bot$-E: $\frac{\bot}{\phi}$

### 6.2 公理系统

**定义 1.14** (公理系统)
命题逻辑的公理系统包含以下公理模式：

1. $\phi \rightarrow (\psi \rightarrow \phi)$
2. $(\phi \rightarrow (\psi \rightarrow \chi)) \rightarrow ((\phi \rightarrow \psi) \rightarrow (\phi \rightarrow \chi))$
3. $(\neg \phi \rightarrow \neg \psi) \rightarrow (\psi \rightarrow \phi)$

**推理规则**: 分离规则 (MP)
$$\frac{\phi \rightarrow \psi \quad \phi}{\psi}$$

## 7 完备性定理

### 7.1 语义后承

**定义 1.15** (语义后承)
公式集合 $\Gamma$ 语义蕴含公式 $\phi$，记作 $\Gamma \models \phi$，当且仅当对于所有满足 $\Gamma$ 的真值赋值 $v$：
$$\overline{v}(\phi) = T$$

### 7.2 语法后承

**定义 1.16** (语法后承)
公式集合 $\Gamma$ 语法蕴含公式 $\phi$，记作 $\Gamma \vdash \phi$，当且仅当存在从 $\Gamma$ 到 $\phi$ 的形式证明。

### 7.3 完备性定理

**定理 1.10** (完备性定理)
$$\Gamma \models \phi \text{ 当且仅当 } \Gamma \vdash \phi$$

**证明**:

1. **可靠性**: 如果 $\Gamma \vdash \phi$，则 $\Gamma \models \phi$
2. **完备性**: 如果 $\Gamma \models \phi$，则 $\Gamma \vdash \phi$

## 8 范式

### 8.1 析取范式

**定义 1.17** (析取范式)
公式 $\phi$ 是析取范式，如果它具有形式：
$$\phi = \bigvee_{i=1}^n \bigwedge_{j=1}^{m_i} l_{ij}$$

其中每个 $l_{ij}$ 是文字（命题变量或其否定）。

**定理 1.11** (析取范式存在性)
每个命题公式都等价于某个析取范式。

### 8.2 合取范式

**定义 1.18** (合取范式)
公式 $\phi$ 是合取范式，如果它具有形式：
$$\phi = \bigwedge_{i=1}^n \bigvee_{j=1}^{m_i} l_{ij}$$

**定理 1.12** (合取范式存在性)
每个命题公式都等价于某个合取范式。

## 9 命题逻辑在计算机科学中的应用

### 9.1 布尔函数

在计算机科学中，命题逻辑用于表示布尔函数：

```rust
// 布尔函数的实现
trait BooleanFunction {
    fn evaluate(&self, inputs: &[bool]) -> bool;
}

struct AndGate;
struct OrGate;
struct NotGate;
struct ImplicationGate;

impl BooleanFunction for AndGate {
    fn evaluate(&self, inputs: &[bool]) -> bool {
        inputs.iter().all(|&x| x)
    }
}

impl BooleanFunction for OrGate {
    fn evaluate(&self, inputs: &[bool]) -> bool {
        inputs.iter().any(|&x| x)
    }
}

impl BooleanFunction for NotGate {
    fn evaluate(&self, inputs: &[bool]) -> bool {
        !inputs[0]
    }
}

impl BooleanFunction for ImplicationGate {
    fn evaluate(&self, inputs: &[bool]) -> bool {
        !inputs[0] || inputs[1]
    }
}

// 复合布尔函数
struct CompositeFunction {
    components: Vec<Box<dyn BooleanFunction>>,
    connections: Vec<(usize, usize)>, // (from, to)
}

impl BooleanFunction for CompositeFunction {
    fn evaluate(&self, inputs: &[bool]) -> bool {
        // 实现复合函数的求值
        true // 简化实现
    }
}
```

### 9.2 逻辑电路设计

命题逻辑为数字电路设计提供了理论基础：

```rust
// 逻辑电路模拟
#[derive(Debug, Clone)]
enum GateType {
    AND,
    OR,
    NOT,
    NAND,
    NOR,
    XOR,
}

struct LogicGate {
    gate_type: GateType,
    inputs: Vec<bool>,
    output: bool,
}

impl LogicGate {
    fn new(gate_type: GateType) -> Self {
        LogicGate {
            gate_type,
            inputs: Vec::new(),
            output: false,
        }
    }

    fn set_inputs(&mut self, inputs: Vec<bool>) {
        self.inputs = inputs;
        self.compute_output();
    }

    fn compute_output(&mut self) {
        self.output = match self.gate_type {
            GateType::AND => self.inputs.iter().all(|&x| x),
            GateType::OR => self.inputs.iter().any(|&x| x),
            GateType::NOT => !self.inputs[0],
            GateType::NAND => !self.inputs.iter().all(|&x| x),
            GateType::NOR => !self.inputs.iter().any(|&x| x),
            GateType::XOR => self.inputs.iter().fold(false, |acc, &x| acc ^ x),
        }
    }

    fn get_output(&self) -> bool {
        self.output
    }
}

// 电路网络
struct Circuit {
    gates: Vec<LogicGate>,
    connections: Vec<(usize, usize, usize)>, // (from_gate, from_output, to_gate)
}

impl Circuit {
    fn new() -> Self {
        Circuit {
            gates: Vec::new(),
            connections: Vec::new(),
        }
    }

    fn add_gate(&mut self, gate: LogicGate) -> usize {
        self.gates.push(gate);
        self.gates.len() - 1
    }

    fn connect(&mut self, from_gate: usize, from_output: usize, to_gate: usize) {
        self.connections.push((from_gate, from_output, to_gate));
    }

    fn simulate(&mut self, inputs: &[bool]) -> Vec<bool> {
        // 实现电路模拟
        vec![true] // 简化实现
    }
}
```

### 9.3 形式化验证

在形式化验证中，命题逻辑用于规范描述和验证：

```lean
-- Lean 中的命题逻辑
import logic.basic

-- 基本命题逻辑操作
def implies (p q : Prop) : Prop := p → q
def iff (p q : Prop) : Prop := p ↔ q

-- 德摩根律的证明
theorem demorgan_and (p q : Prop) :
  ¬(p ∧ q) ↔ (¬p ∨ ¬q) :=
begin
  split,
  { intro h,
    by_cases hp : p,
    { by_cases hq : q,
      { exfalso, exact h ⟨hp, hq⟩ },
      { right, exact hq } },
    { left, exact hp } },
  { intro h,
    intro ⟨hp, hq⟩,
    cases h with np nq,
    { exact np hp },
    { exact nq hq } }
end

-- 永真式的证明
theorem excluded_middle (p : Prop) :
  p ∨ ¬p :=
begin
  by_cases hp : p,
  { left, exact hp },
  { right, exact hp }
end

-- 假言三段论
theorem hypothetical_syllogism (p q r : Prop) :
  (p → q) → (q → r) → (p → r) :=
begin
  intros hpq hqr hp,
  exact hqr (hpq hp)
end
```

## 10 总结

命题逻辑为形式科学提供了基础：

1. **语法系统** 为逻辑表达式提供了精确的形式化描述
2. **语义理论** 为逻辑推理提供了真值解释
3. **推理系统** 为形式化证明提供了规则和方法
4. **完备性定理** 保证了语法和语义的一致性
5. **范式理论** 为逻辑公式的标准化提供了工具

这些理论不仅在纯逻辑学中具有重要地位，也为计算机科学、人工智能和形式化方法提供了基础。

## 参考文献

1. Enderton, H. B. (2001). _A mathematical introduction to logic_. Academic Press.
2. Mendelson, E. (2015). _Introduction to mathematical logic_. CRC Press.
3. Boolos, G. S., Burgess, J. P., & Jeffrey, R. C. (2007). _Computability and logic_. Cambridge University Press.
4. Huth, M., & Ryan, M. (2004). _Logic in computer science: Modelling and reasoning about systems_. Cambridge University Press.

---

**更新时间**: 2024-12-21
**版本**: 1.0
**作者**: FormalScience Team

## 11 批判性分析

- 多元理论视角：
  - 基础与扩展：命题逻辑作为形式逻辑的基础，为高阶逻辑、模态逻辑等提供语法与语义框架。
  - 计算与工程：布尔代数、电路设计、形式化验证等工程应用体现命题逻辑的实用价值。
- 局限性分析：
  - 表达力有限：无法表达量化、关系、模态等复杂概念，需要扩展为一阶逻辑等。
  - 可判定性边界：虽然命题逻辑可判定，但复杂度随变量数量指数增长。
- 争议与分歧：
  - 经典 vs 直觉：排中律的接受与否影响逻辑系统的选择与应用。
- 应用前景：
  - 数字电路设计、形式化验证、人工智能推理、知识表示等领域的持续应用。
- 改进建议：
  - 开发高效的SAT求解器与证明系统；建立从命题逻辑到高阶逻辑的渐进学习路径。
