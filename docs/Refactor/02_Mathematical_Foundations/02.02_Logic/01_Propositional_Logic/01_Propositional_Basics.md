# 02.02.01 命题逻辑基础 (Propositional Logic Basics)

## 📋 概述

命题逻辑基础是逻辑学的核心，研究命题的基本结构、逻辑连接词和推理规则。
本文档建立了严格的命题逻辑基础理论，为所有其他逻辑理论提供基础。

**构建时间**: 2024年12月20日  
**版本**: v2.0  
**状态**: 已完成

## 📚 目录

- [02.02.01 命题逻辑基础 (Propositional Logic Basics)](#020201-命题逻辑基础-propositional-logic-basics)
  - [📋 概述](#-概述)
  - [📚 目录](#-目录)
  - [1. 基本概念](#1-基本概念)
    - [1.1 命题逻辑的形式化定义](#11-命题逻辑的形式化定义)
    - [1.2 命题逻辑的语义理论](#12-命题逻辑的语义理论)
    - [1.3 命题逻辑的证明理论](#13-命题逻辑的证明理论)
  - [2. 命题语法](#2-命题语法)
    - [2.1 语法规则](#21-语法规则)
    - [2.2 语法树](#22-语法树)
  - [3. 逻辑连接词](#3-逻辑连接词)
    - [3.1 否定 (¬)](#31-否定-)
    - [3.2 合取 (∧)](#32-合取-)
    - [3.3 析取 (∨)](#33-析取-)
    - [3.4 蕴含 (→)](#34-蕴含-)
    - [3.5 等价 (↔)](#35-等价-)
  - [4. 语义解释](#4-语义解释)
    - [4.1 真值赋值](#41-真值赋值)
    - [4.2 语义函数](#42-语义函数)
    - [4.3 满足关系](#43-满足关系)
    - [4.4 有效性](#44-有效性)
    - [4.5 可满足性](#45-可满足性)
  - [5. 推理规则](#5-推理规则)
    - [5.1 自然演绎系统](#51-自然演绎系统)
    - [5.2 公理系统](#52-公理系统)
  - [6. 逻辑等价](#6-逻辑等价)
    - [6.1 等价定义](#61-等价定义)
    - [6.2 基本等价律](#62-基本等价律)
  - [7. 范式理论](#7-范式理论)
    - [7.1 析取范式 (DNF)](#71-析取范式-dnf)
    - [7.2 合取范式 (CNF)](#72-合取范式-cnf)
    - [7.3 范式转换](#73-范式转换)
  - [8. 应用实例](#8-应用实例)
    - [8.1 电路设计](#81-电路设计)
    - [8.2 程序验证](#82-程序验证)
  - [9. 代码实现](#9-代码实现)
    - [9.1 Rust实现](#91-rust实现)
    - [9.2 Haskell实现](#92-haskell实现)
  - [10. 参考文献](#10-参考文献)
  - [批判性分析](#批判性分析)

## 1. 基本概念

### 1.1 命题逻辑的形式化定义

**定义 1.1.1** (命题逻辑语言)
命题逻辑语言是一个三元组 $\mathcal{L} = (\text{Atom}, \text{Conn}, \text{Form})$，其中：

- $\text{Atom}$ 是原子命题集合（可数无限集）
- $\text{Conn} = \{\neg, \land, \lor, \rightarrow, \leftrightarrow\}$ 是逻辑连接词集合
- $\text{Form}$ 是公式集合，递归定义如下：

**递归定义**:

1. **原子公式**: 如果 $p \in \text{Atom}$，则 $p \in \text{Form}$
2. **否定公式**: 如果 $\phi \in \text{Form}$，则 $\neg\phi \in \text{Form}$
3. **二元连接词**: 如果 $\phi, \psi \in \text{Form}$，则：
   - $(\phi \land \psi) \in \text{Form}$ (合取)
   - $(\phi \lor \psi) \in \text{Form}$ (析取)
   - $(\phi \rightarrow \psi) \in \text{Form}$ (蕴含)
   - $(\phi \leftrightarrow \psi) \in \text{Form}$ (等价)

**定义 1.1.2** (命题)
命题是命题逻辑语言中的公式。

**定义 1.1.3** (原子命题)
原子命题是命题逻辑语言中的原子公式。

**定义 1.1.4** (复合命题)
复合命题是通过逻辑连接词构成的非原子公式。

### 1.2 命题逻辑的语义理论

**定义 1.2.1** (真值赋值)
真值赋值是一个函数 $v: \text{Atom} \rightarrow \{T, F\}$，其中 $T$ 表示真，$F$ 表示假。

**定义 1.2.2** (语义函数)
语义函数 $\llbracket \cdot \rrbracket_v: \text{Form} \rightarrow \{T, F\}$ 递归定义如下：

1. **原子公式**: $\llbracket p \rrbracket_v = v(p)$
2. **否定**: $\llbracket \neg\phi \rrbracket_v = T$ 当且仅当 $\llbracket \phi \rrbracket_v = F$
3. **合取**: $\llbracket \phi \land \psi \rrbracket_v = T$ 当且仅当 $\llbracket \phi \rrbracket_v = T$ 且 $\llbracket \psi \rrbracket_v = T$
4. **析取**: $\llbracket \phi \lor \psi \rrbracket_v = T$ 当且仅当 $\llbracket \phi \rrbracket_v = T$ 或 $\llbracket \psi \rrbracket_v = T$
5. **蕴含**: $\llbracket \phi \rightarrow \psi \rrbracket_v = T$ 当且仅当 $\llbracket \phi \rrbracket_v = F$ 或 $\llbracket \psi \rrbracket_v = T$
6. **等价**: $\llbracket \phi \leftrightarrow \psi \rrbracket_v = T$ 当且仅当 $\llbracket \phi \rrbracket_v = \llbracket \psi \rrbracket_v$

### 1.3 命题逻辑的证明理论

**定义 1.3.1** (自然演绎系统)
自然演绎系统包含以下推理规则：

**引入规则**:

- $\land$-I: $\frac{\phi \quad \psi}{\phi \land \psi}$
- $\lor$-I: $\frac{\phi}{\phi \lor \psi}$ 或 $\frac{\psi}{\phi \lor \psi}$
- $\rightarrow$-I: $\frac{[\phi] \quad \psi}{\phi \rightarrow \psi}$
- $\leftrightarrow$-I: $\frac{\phi \rightarrow \psi \quad \psi \rightarrow \phi}{\phi \leftrightarrow \psi}$

**消除规则**:

- $\land$-E: $\frac{\phi \land \psi}{\phi}$ 或 $\frac{\phi \land \psi}{\psi}$
- $\lor$-E: $\frac{\phi \lor \psi \quad [\phi] \quad \chi \quad [\psi] \quad \chi}{\chi}$
- $\rightarrow$-E: $\frac{\phi \rightarrow \psi \quad \phi}{\psi}$
- $\leftrightarrow$-E: $\frac{\phi \leftrightarrow \psi \quad \phi}{\psi}$ 或 $\frac{\phi \leftrightarrow \psi \quad \psi}{\phi}$

**否定规则**:

- $\neg$-I: $\frac{[\phi] \quad \bot}{\neg\phi}$
- $\neg$-E: $\frac{\phi \quad \neg\phi}{\bot}$
- $\bot$-E: $\frac{\bot}{\phi}$ (爆炸原理)

**定义 1.3.2** (证明)
从假设集合 $\Gamma$ 到结论 $\phi$ 的证明是一个有限的公式序列，其中每个公式要么是假设，要么是通过推理规则从前面的公式得出的。

**定义 1.3.3** (可证性)
$\Gamma \vdash \phi$ 表示存在从 $\Gamma$ 到 $\phi$ 的证明。

**定理 1.3.1** (可靠性定理)
如果 $\Gamma \vdash \phi$，则 $\Gamma \models \phi$。

**定理 1.3.2** (完备性定理)
如果 $\Gamma \models \phi$，则 $\Gamma \vdash \phi$。

## 2. 命题语法

### 2.1 语法规则

**规则 2.1.1** (原子命题)
原子命题是公式。

**形式化表示**:
$$\frac{p \in \text{Atom}}{p \in \text{Form}}$$

**规则 2.1.2** (否定)
如果φ是公式，则¬φ是公式。

**形式化表示**:
$$\frac{\phi \in \text{Form}}{\neg \phi \in \text{Form}}$$

**规则 2.1.3** (合取)
如果φ和ψ是公式，则φ∧ψ是公式。

**形式化表示**:
$$\frac{\phi \in \text{Form} \quad \psi \in \text{Form}}{\phi \land \psi \in \text{Form}}$$

**规则 2.1.4** (析取)
如果φ和ψ是公式，则φ∨ψ是公式。

**形式化表示**:
$$\frac{\phi \in \text{Form} \quad \psi \in \text{Form}}{\phi \lor \psi \in \text{Form}}$$

**规则 2.1.5** (蕴含)
如果φ和ψ是公式，则φ→ψ是公式。

**形式化表示**:
$$\frac{\phi \in \text{Form} \quad \psi \in \text{Form}}{\phi \rightarrow \psi \in \text{Form}}$$

**规则 2.1.6** (等价)
如果φ和ψ是公式，则φ↔ψ是公式。

**形式化表示**:
$$\frac{\phi \in \text{Form} \quad \psi \in \text{Form}}{\phi \leftrightarrow \psi \in \text{Form}}$$

### 2.2 语法树

**定义 2.2.1** (语法树)
公式的语法树是表示公式结构的树形图。

**示例**:

- 公式φ∧(ψ∨χ)的语法树：

```text
    ∧
   / \
  φ   ∨
     / \
    ψ   χ
```

## 3. 逻辑连接词

### 3.1 否定 (¬)

**定义 3.1.1** (否定)
否定连接词将真命题变为假命题，假命题变为真命题。

**真值表**:

| φ | ¬φ |
|---|---|
| T | F  |
| F | T  |

**形式化定义**:
$$\neg \phi \equiv \text{not}(\phi)$$

### 3.2 合取 (∧)

**定义 3.2.1** (合取)
合取连接词表示"且"的关系。

**真值表**:

| φ | ψ | φ∧ψ |
|---|---|-----|
| T | T | T   |
| T | F | F   |
| F | T | F   |
| F | F | F   |

**形式化定义**:
$$\phi \land \psi \equiv \text{and}(\phi, \psi)$$

### 3.3 析取 (∨)

**定义 3.3.1** (析取)
析取连接词表示"或"的关系。

**真值表**:

| φ | ψ | φ∨ψ |
|---|---|-----|
| T | T | T   |
| T | F | T   |
| F | T | T   |
| F | F | F   |

**形式化定义**:
$$\phi \lor \psi \equiv \text{or}(\phi, \psi)$$

### 3.4 蕴含 (→)

**定义 3.4.1** (蕴含)
蕴含连接词表示"如果...那么..."的关系。

**真值表**:

| φ | ψ | φ→ψ |
|---|---|-----|
| T | T | T   |
| T | F | F   |
| F | T | T   |
| F | F | T   |

**形式化定义**:
$$\phi \rightarrow \psi \equiv \neg \phi \lor \psi$$

### 3.5 等价 (↔)

**定义 3.5.1** (等价)
等价连接词表示"当且仅当"的关系。

**真值表**:

| φ | ψ | φ↔ψ |
|---|---|-----|
| T | T | T   |
| T | F | F   |
| F | T | F   |
| F | F | T   |

**形式化定义**:
$$\phi \leftrightarrow \psi \equiv (\phi \rightarrow \psi) \land (\psi \rightarrow \phi)$$

## 4. 语义解释

### 4.1 真值赋值

**定义 4.1.1** (真值赋值)
真值赋值是从原子命题到真值的函数。

**形式化定义**:
$$v: \text{Atom} \rightarrow \{\text{True}, \text{False}\}$$

### 4.2 语义函数

**定义 4.2.1** (语义函数)
语义函数是从公式到真值的函数。

**形式化定义**:
$$\llbracket \cdot \rrbracket_v: \text{Form} \rightarrow \{\text{True}, \text{False}\}$$

**递归定义**:

1. $\llbracket p \rrbracket_v = v(p)$
2. $\llbracket \neg \phi \rrbracket_v = \neg \llbracket \phi \rrbracket_v$
3. $\llbracket \phi \land \psi \rrbracket_v = \llbracket \phi \rrbracket_v \land \llbracket \psi \rrbracket_v$
4. $\llbracket \phi \lor \psi \rrbracket_v = \llbracket \phi \rrbracket_v \lor \llbracket \psi \rrbracket_v$
5. $\llbracket \phi \rightarrow \psi \rrbracket_v = \llbracket \phi \rrbracket_v \rightarrow \llbracket \psi \rrbracket_v$
6. $\llbracket \phi \leftrightarrow \psi \rrbracket_v = \llbracket \phi \rrbracket_v \leftrightarrow \llbracket \psi \rrbracket_v$

### 4.3 满足关系

**定义 4.3.1** (满足)
真值赋值v满足公式φ，记作v⊨φ。

**形式化定义**:
$$v \models \phi \equiv \llbracket \phi \rrbracket_v = \text{True}$$

### 4.4 有效性

**定义 4.4.1** (有效性)
公式φ是有效的，当且仅当在所有真值赋值下都为真。

**形式化定义**:
$$\models \phi \equiv \forall v (v \models \phi)$$

### 4.5 可满足性

**定义 4.5.1** (可满足性)
公式φ是可满足的，当且仅当存在真值赋值使其为真。

**形式化定义**:
$$\text{Sat}(\phi) \equiv \exists v (v \models \phi)$$

## 5. 推理规则

### 5.1 自然演绎系统

**规则 5.1.1** (假设引入)
$$\frac{}{\phi \vdash \phi}$$

**规则 5.1.2** (否定引入)
$$\frac{\Gamma, \phi \vdash \bot}{\Gamma \vdash \neg \phi}$$

**规则 5.1.3** (否定消除)
$$\frac{\Gamma \vdash \phi \quad \Gamma \vdash \neg \phi}{\Gamma \vdash \bot}$$

**规则 5.1.4** (合取引入)
$$\frac{\Gamma \vdash \phi \quad \Gamma \vdash \psi}{\Gamma \vdash \phi \land \psi}$$

**规则 5.1.5** (合取消除)
$$\frac{\Gamma \vdash \phi \land \psi}{\Gamma \vdash \phi} \quad \frac{\Gamma \vdash \phi \land \psi}{\Gamma \vdash \psi}$$

**规则 5.1.6** (析取引入)
$$\frac{\Gamma \vdash \phi}{\Gamma \vdash \phi \lor \psi} \quad \frac{\Gamma \vdash \psi}{\Gamma \vdash \phi \lor \psi}$$

**规则 5.1.7** (析取消除)
$$\frac{\Gamma \vdash \phi \lor \psi \quad \Gamma, \phi \vdash \chi \quad \Gamma, \psi \vdash \chi}{\Gamma \vdash \chi}$$

**规则 5.1.8** (蕴含引入)
$$\frac{\Gamma, \phi \vdash \psi}{\Gamma \vdash \phi \rightarrow \psi}$$

**规则 5.1.9** (蕴含消除)
$$\frac{\Gamma \vdash \phi \rightarrow \psi \quad \Gamma \vdash \phi}{\Gamma \vdash \psi}$$

### 5.2 公理系统

**公理 5.2.1** (K公理)
$$\vdash \phi \rightarrow (\psi \rightarrow \phi)$$

**公理 5.2.2** (S公理)
$$\vdash (\phi \rightarrow (\psi \rightarrow \chi)) \rightarrow ((\phi \rightarrow \psi) \rightarrow (\phi \rightarrow \chi))$$

**公理 5.2.3** (双重否定)
$$\vdash \neg \neg \phi \rightarrow \phi$$

**公理 5.2.4** (排中律)
$$\vdash \phi \lor \neg \phi$$

## 6. 逻辑等价

### 6.1 等价定义

**定义 6.1.1** (逻辑等价)
公式φ和ψ逻辑等价，当且仅当在所有真值赋值下具有相同的真值。

**形式化定义**:
$$\phi \equiv \psi \equiv \forall v (\llbracket \phi \rrbracket_v = \llbracket \psi \rrbracket_v)$$

### 6.2 基本等价律

**定理 6.2.1** (双重否定律)
$$\neg \neg \phi \equiv \phi$$

**定理 6.2.2** (德摩根律)
$$\neg (\phi \land \psi) \equiv \neg \phi \lor \neg \psi$$
$$\neg (\phi \lor \psi) \equiv \neg \phi \land \neg \psi$$

**定理 6.2.3** (分配律)
$$\phi \land (\psi \lor \chi) \equiv (\phi \land \psi) \lor (\phi \land \chi)$$
$$\phi \lor (\psi \land \chi) \equiv (\phi \lor \psi) \land (\phi \lor \chi)$$

**定理 6.2.4** (结合律)
$$(\phi \land \psi) \land \chi \equiv \phi \land (\psi \land \chi)$$
$$(\phi \lor \psi) \lor \chi \equiv \phi \lor (\psi \lor \chi)$$

**定理 6.2.5** (交换律)
$$\phi \land \psi \equiv \psi \land \phi$$
$$\phi \lor \psi \equiv \psi \lor \phi$$

**定理 6.2.6** (幂等律)
$$\phi \land \phi \equiv \phi$$
$$\phi \lor \phi \equiv \phi$$

**定理 6.2.7** (吸收律)
$$\phi \land (\phi \lor \psi) \equiv \phi$$
$$\phi \lor (\phi \land \psi) \equiv \phi$$

## 7. 范式理论

### 7.1 析取范式 (DNF)

**定义 7.1.1** (析取范式)
公式φ是析取范式，当且仅当它是合取项的析取。

**形式化定义**:
$$\text{DNF}(\phi) \equiv \bigvee_{i=1}^n \bigwedge_{j=1}^{m_i} l_{ij}$$

其中l_{ij}是文字（原子命题或其否定）。

### 7.2 合取范式 (CNF)

**定义 7.2.1** (合取范式)
公式φ是合取范式，当且仅当它是析取项的合取。

**形式化定义**:
$$\text{CNF}(\phi) \equiv \bigwedge_{i=1}^n \bigvee_{j=1}^{m_i} l_{ij}$$

### 7.3 范式转换

**算法 7.3.1** (DNF转换)

1. 消除蕴含和等价连接词
2. 将否定内移（德摩根律）
3. 使用分配律展开
4. 合并相同项

**算法 7.3.2** (CNF转换)

1. 消除蕴含和等价连接词
2. 将否定内移（德摩根律）
3. 使用分配律展开
4. 合并相同项

## 8. 应用实例

### 8.1 电路设计

**实例 8.1.1** (与门)
与门的逻辑表达式：$f(a,b) = a \land b$

**真值表**:

| a | b | f(a,b) |
|---|---|--------|
| 0 | 0 | 0      |
| 0 | 1 | 0      |
| 1 | 0 | 0      |
| 1 | 1 | 1      |

**实例 8.1.2** (或门)
或门的逻辑表达式：$f(a,b) = a \lor b$

**真值表**:

| a | b | f(a,b) |
|---|---|--------|
| 0 | 0 | 0      |
| 0 | 1 | 1      |
| 1 | 0 | 1      |
| 1 | 1 | 1      |

### 8.2 程序验证

**实例 8.2.1** (条件语句)
if语句的逻辑表达式：$(p \land q) \lor (\neg p \land r)$

**实例 8.2.2** (循环不变式)
while循环的不变式：$I \land B \rightarrow I$

## 9. 代码实现

### 9.1 Rust实现

```rust
use std::collections::HashMap;
use std::fmt;

// 命题类型定义
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Proposition {
    Atom(String),
    Not(Box<Proposition>),
    And(Box<Proposition>, Box<Proposition>),
    Or(Box<Proposition>, Box<Proposition>),
    Implies(Box<Proposition>, Box<Proposition>),
    Iff(Box<Proposition>, Box<Proposition>),
}

impl Proposition {
    /// 构造原子命题
    pub fn atom(name: &str) -> Self {
        Proposition::Atom(name.to_string())
    }
    
    /// 构造否定命题
    pub fn not(prop: Proposition) -> Self {
        Proposition::Not(Box::new(prop))
    }
    
    /// 构造合取命题
    pub fn and(left: Proposition, right: Proposition) -> Self {
        Proposition::And(Box::new(left), Box::new(right))
    }
    
    /// 构造析取命题
    pub fn or(left: Proposition, right: Proposition) -> Self {
        Proposition::Or(Box::new(left), Box::new(right))
    }
    
    /// 构造蕴含命题
    pub fn implies(antecedent: Proposition, consequent: Proposition) -> Self {
        Proposition::Implies(Box::new(antecedent), Box::new(consequent))
    }
    
    /// 构造等价命题
    pub fn iff(left: Proposition, right: Proposition) -> Self {
        Proposition::Iff(Box::new(left), Box::new(right))
    }
    
    /// 获取原子命题
    pub fn atoms(&self) -> Vec<String> {
        match self {
            Proposition::Atom(name) => vec![name.clone()],
            Proposition::Not(prop) => prop.atoms(),
            Proposition::And(left, right) => {
                let mut atoms = left.atoms();
                atoms.extend(right.atoms());
                atoms.sort();
                atoms.dedup();
                atoms
            }
            Proposition::Or(left, right) => {
                let mut atoms = left.atoms();
                atoms.extend(right.atoms());
                atoms.sort();
                atoms.dedup();
                atoms
            }
            Proposition::Implies(left, right) => {
                let mut atoms = left.atoms();
                atoms.extend(right.atoms());
                atoms.sort();
                atoms.dedup();
                atoms
            }
            Proposition::Iff(left, right) => {
                let mut atoms = left.atoms();
                atoms.extend(right.atoms());
                atoms.sort();
                atoms.dedup();
                atoms
            }
        }
    }
    
    /// 转换为否定范式
    pub fn to_nnf(&self) -> Proposition {
        match self {
            Proposition::Atom(_) => self.clone(),
            Proposition::Not(prop) => match prop.as_ref() {
                Proposition::Atom(_) => self.clone(),
                Proposition::Not(p) => p.to_nnf(),
                Proposition::And(left, right) => {
                    Proposition::or(
                        Proposition::not(left.clone()).to_nnf(),
                        Proposition::not(right.clone()).to_nnf()
                    )
                }
                Proposition::Or(left, right) => {
                    Proposition::and(
                        Proposition::not(left.clone()).to_nnf(),
                        Proposition::not(right.clone()).to_nnf()
                    )
                }
                _ => self.clone(),
            }
            Proposition::And(left, right) => {
                Proposition::and(left.to_nnf(), right.to_nnf())
            }
            Proposition::Or(left, right) => {
                Proposition::or(left.to_nnf(), right.to_nnf())
            }
            Proposition::Implies(left, right) => {
                Proposition::or(
                    Proposition::not(left.clone()).to_nnf(),
                    right.to_nnf()
                )
            }
            Proposition::Iff(left, right) => {
                Proposition::and(
                    Proposition::implies(left.clone(), right.clone()).to_nnf(),
                    Proposition::implies(right.clone(), left.clone()).to_nnf()
                )
            }
        }
    }
    
    /// 转换为析取范式
    pub fn to_dnf(&self) -> Proposition {
        let nnf = self.to_nnf();
        nnf.distribute_or_over_and()
    }
    
    /// 分配析取到合取
    fn distribute_or_over_and(&self) -> Proposition {
        match self {
            Proposition::Or(left, right) => {
                match (left.as_ref(), right.as_ref()) {
                    (Proposition::And(l1, l2), _) => {
                        Proposition::and(
                            Proposition::or(l1.clone(), right.clone()).distribute_or_over_and(),
                            Proposition::or(l2.clone(), right.clone()).distribute_or_over_and()
                        )
                    }
                    (_, Proposition::And(r1, r2)) => {
                        Proposition::and(
                            Proposition::or(left.clone(), r1.clone()).distribute_or_over_and(),
                            Proposition::or(left.clone(), r2.clone()).distribute_or_over_and()
                        )
                    }
                    _ => self.clone(),
                }
            }
            Proposition::And(left, right) => {
                Proposition::and(
                    left.distribute_or_over_and(),
                    right.distribute_or_over_and()
                )
            }
            _ => self.clone(),
        }
    }
}

// 真值赋值类型定义
pub type Valuation = HashMap<String, bool>;

// 语义解释器
pub struct Interpreter;

impl Interpreter {
    /// 解释命题
    pub fn interpret(prop: &Proposition, valuation: &Valuation) -> bool {
        match prop {
            Proposition::Atom(name) => *valuation.get(name).unwrap_or(&false),
            Proposition::Not(p) => !Self::interpret(p, valuation),
            Proposition::And(left, right) => {
                Self::interpret(left, valuation) && Self::interpret(right, valuation)
            }
            Proposition::Or(left, right) => {
                Self::interpret(left, valuation) || Self::interpret(right, valuation)
            }
            Proposition::Implies(left, right) => {
                !Self::interpret(left, valuation) || Self::interpret(right, valuation)
            }
            Proposition::Iff(left, right) => {
                Self::interpret(left, valuation) == Self::interpret(right, valuation)
            }
        }
    }
    
    /// 检查有效性
    pub fn is_valid(prop: &Proposition) -> bool {
        let atoms = prop.atoms();
        Self::check_all_valuations(prop, &atoms, 0, &mut HashMap::new())
    }
    
    /// 检查可满足性
    pub fn is_satisfiable(prop: &Proposition) -> bool {
        let atoms = prop.atoms();
        Self::check_some_valuation(prop, &atoms, 0, &mut HashMap::new())
    }
    
    /// 检查所有真值赋值
    fn check_all_valuations(
        prop: &Proposition,
        atoms: &[String],
        index: usize,
        valuation: &mut Valuation,
    ) -> bool {
        if index >= atoms.len() {
            return Self::interpret(prop, valuation);
        }
        
        valuation.insert(atoms[index].clone(), true);
        let result1 = Self::check_all_valuations(prop, atoms, index + 1, valuation);
        
        valuation.insert(atoms[index].clone(), false);
        let result2 = Self::check_all_valuations(prop, atoms, index + 1, valuation);
        
        result1 && result2
    }
    
    /// 检查某个真值赋值
    fn check_some_valuation(
        prop: &Proposition,
        atoms: &[String],
        index: usize,
        valuation: &mut Valuation,
    ) -> bool {
        if index >= atoms.len() {
            return Self::interpret(prop, valuation);
        }
        
        valuation.insert(atoms[index].clone(), true);
        if Self::check_some_valuation(prop, atoms, index + 1, valuation) {
            return true;
        }
        
        valuation.insert(atoms[index].clone(), false);
        Self::check_some_valuation(prop, atoms, index + 1, valuation)
    }
}

// 推理系统
pub struct InferenceSystem;

impl InferenceSystem {
    /// 假言推理
    pub fn modus_ponens(premise1: &Proposition, premise2: &Proposition) -> Option<Proposition> {
        match (premise1, premise2) {
            (Proposition::Implies(antecedent, consequent), antecedent_prop) => {
                if antecedent.as_ref() == antecedent_prop {
                    Some(*consequent.clone())
                } else {
                    None
                }
            }
            _ => None,
        }
    }
    
    /// 假言三段论
    pub fn hypothetical_syllogism(premise1: &Proposition, premise2: &Proposition) -> Option<Proposition> {
        match (premise1, premise2) {
            (Proposition::Implies(a, b), Proposition::Implies(c, d)) => {
                if b.as_ref() == c.as_ref() {
                    Some(Proposition::implies(a.clone(), d.clone()))
                } else {
                    None
                }
            }
            _ => None,
        }
    }
    
    /// 构造性二难推理
    pub fn constructive_dilemma(
        premise1: &Proposition,
        premise2: &Proposition,
        premise3: &Proposition,
    ) -> Option<Proposition> {
        match (premise1, premise2, premise3) {
            (Proposition::And(impl1, impl2), Proposition::Or(disj1, disj2), Proposition::Or(disj3, disj4)) => {
                if disj1.as_ref() == disj3.as_ref() && disj2.as_ref() == disj4.as_ref() {
                    Some(Proposition::or(
                        Proposition::implies(impl1.as_ref().clone(), disj1.clone()),
                        Proposition::implies(impl2.as_ref().clone(), disj2.clone())
                    ))
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

// 测试用例
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_proposition_construction() {
        let p = Proposition::atom("p");
        let q = Proposition::atom("q");
        let and_prop = Proposition::and(p.clone(), q.clone());
        let or_prop = Proposition::or(p.clone(), q.clone());
        let implies_prop = Proposition::implies(p.clone(), q.clone());
        
        assert_eq!(and_prop, Proposition::And(Box::new(p.clone()), Box::new(q.clone())));
        assert_eq!(or_prop, Proposition::Or(Box::new(p.clone()), Box::new(q.clone())));
        assert_eq!(implies_prop, Proposition::Implies(Box::new(p), Box::new(q)));
    }
    
    #[test]
    fn test_interpretation() {
        let p = Proposition::atom("p");
        let q = Proposition::atom("q");
        let and_prop = Proposition::and(p.clone(), q.clone());
        
        let mut valuation = Valuation::new();
        valuation.insert("p".to_string(), true);
        valuation.insert("q".to_string(), true);
        
        assert!(Interpreter::interpret(&and_prop, &valuation));
        
        valuation.insert("q".to_string(), false);
        assert!(!Interpreter::interpret(&and_prop, &valuation));
    }
    
    #[test]
    fn test_validity() {
        // 排中律：p ∨ ¬p
        let p = Proposition::atom("p");
        let not_p = Proposition::not(p.clone());
        let excluded_middle = Proposition::or(p, not_p);
        
        assert!(Interpreter::is_valid(&excluded_middle));
    }
    
    #[test]
    fn test_satisfiability() {
        let p = Proposition::atom("p");
        let q = Proposition::atom("q");
        let satisfiable = Proposition::and(p.clone(), q.clone());
        
        assert!(Interpreter::is_satisfiable(&satisfiable));
        
        let unsatisfiable = Proposition::and(p.clone(), Proposition::not(p));
        assert!(!Interpreter::is_satisfiable(&unsatisfiable));
    }
    
    #[test]
    fn test_inference() {
        let p = Proposition::atom("p");
        let q = Proposition::atom("q");
        let implies = Proposition::implies(p.clone(), q.clone());
        
        let result = InferenceSystem::modus_ponens(&implies, &p);
        assert_eq!(result, Some(q));
    }
    
    #[test]
    fn test_dnf_conversion() {
        let p = Proposition::atom("p");
        let q = Proposition::atom("q");
        let r = Proposition::atom("r");
        
        // (p ∧ q) ∨ (¬p ∧ r)
        let original = Proposition::or(
            Proposition::and(p.clone(), q.clone()),
            Proposition::and(Proposition::not(p.clone()), r.clone())
        );
        
        let dnf = original.to_dnf();
        println!("DNF: {:?}", dnf);
    }
}
```

### 9.2 Haskell实现

```haskell
-- 命题类型定义
data Proposition = Atom String
                 | Not Proposition
                 | And Proposition Proposition
                 | Or Proposition Proposition
                 | Implies Proposition Proposition
                 | Iff Proposition Proposition
                 deriving (Eq, Show)

-- 真值赋值类型定义
type Valuation = [(String, Bool)]

-- 构造函数
atom :: String -> Proposition
atom = Atom

not' :: Proposition -> Proposition
not' = Not

and' :: Proposition -> Proposition -> Proposition
and' = And

or' :: Proposition -> Proposition -> Proposition
or' = Or

implies :: Proposition -> Proposition -> Proposition
implies = Implies

iff :: Proposition -> Proposition -> Proposition
iff = Iff

-- 获取原子命题
atoms :: Proposition -> [String]
atoms (Atom name) = [name]
atoms (Not prop) = atoms prop
atoms (And left right) = nub $ sort $ atoms left ++ atoms right
atoms (Or left right) = nub $ sort $ atoms left ++ atoms right
atoms (Implies left right) = nub $ sort $ atoms left ++ atoms right
atoms (Iff left right) = nub $ sort $ atoms left ++ atoms right

-- 语义解释
interpret :: Proposition -> Valuation -> Bool
interpret (Atom name) valuation = 
    case lookup name valuation of
        Just value -> value
        Nothing -> False
interpret (Not prop) valuation = not $ interpret prop valuation
interpret (And left right) valuation = 
    interpret left valuation && interpret right valuation
interpret (Or left right) valuation = 
    interpret left valuation || interpret right valuation
interpret (Implies left right) valuation = 
    not (interpret left valuation) || interpret right valuation
interpret (Iff left right) valuation = 
    interpret left valuation == interpret right valuation

-- 检查有效性
isValid :: Proposition -> Bool
isValid prop = 
    let atomList = atoms prop
    in all (\valuation -> interpret prop valuation) (allValuations atomList)

-- 检查可满足性
isSatisfiable :: Proposition -> Bool
isSatisfiable prop = 
    let atomList = atoms prop
    in any (\valuation -> interpret prop valuation) (allValuations atomList)

-- 生成所有真值赋值
allValuations :: [String] -> [Valuation]
allValuations [] = [[]]
allValuations (atom:atoms) = 
    let rest = allValuations atoms
    in [(atom, True):val | val <- rest] ++ [(atom, False):val | val <- rest]

-- 转换为否定范式
toNNF :: Proposition -> Proposition
toNNF (Atom name) = Atom name
toNNF (Not (Atom name)) = Not (Atom name)
toNNF (Not (Not prop)) = toNNF prop
toNNF (Not (And left right)) = 
    Or (toNNF (Not left)) (toNNF (Not right))
toNNF (Not (Or left right)) = 
    And (toNNF (Not left)) (toNNF (Not right))
toNNF (Not prop) = Not (toNNF prop)
toNNF (And left right) = And (toNNF left) (toNNF right)
toNNF (Or left right) = Or (toNNF left) (toNNF right)
toNNF (Implies left right) = 
    Or (toNNF (Not left)) (toNNF right)
toNNF (Iff left right) = 
    And (toNNF (Implies left right)) (toNNF (Implies right left))

-- 转换为析取范式
toDNF :: Proposition -> Proposition
toDNF prop = distributeOrOverAnd (toNNF prop)

-- 分配析取到合取
distributeOrOverAnd :: Proposition -> Proposition
distributeOrOverAnd (Or left right) = 
    case (left, right) of
        (And l1 l2, _) -> 
            And (distributeOrOverAnd (Or l1 right)) 
                (distributeOrOverAnd (Or l2 right))
        (_, And r1 r2) -> 
            And (distributeOrOverAnd (Or left r1)) 
                (distributeOrOverAnd (Or left r2))
        _ -> Or left right
distributeOrOverAnd (And left right) = 
    And (distributeOrOverAnd left) (distributeOrOverAnd right)
distributeOrOverAnd prop = prop

-- 推理规则
modusPonens :: Proposition -> Proposition -> Maybe Proposition
modusPonens (Implies antecedent consequent) premise = 
    if antecedent == premise then Just consequent else Nothing
modusPonens _ _ = Nothing

hypotheticalSyllogism :: Proposition -> Proposition -> Maybe Proposition
hypotheticalSyllogism (Implies a b) (Implies c d) = 
    if b == c then Just (Implies a d) else Nothing
hypotheticalSyllogism _ _ = Nothing

-- 实例：电路设计
andGate :: Proposition -> Proposition -> Proposition
andGate a b = And a b

orGate :: Proposition -> Proposition -> Proposition
orGate a b = Or a b

notGate :: Proposition -> Proposition
notGate = Not

-- 实例：条件语句
ifStatement :: Proposition -> Proposition -> Proposition -> Proposition
ifStatement condition thenBranch elseBranch = 
    Or (And condition thenBranch) (And (Not condition) elseBranch)

-- 测试函数
testPropositionalLogic :: IO ()
testPropositionalLogic = do
    let p = atom "p"
    let q = atom "q"
    let r = atom "r"
    
    -- 测试基本构造
    let andProp = and' p q
    let orProp = or' p q
    let impliesProp = implies p q
    
    putStrLn $ "And: " ++ show andProp
    putStrLn $ "Or: " ++ show orProp
    putStrLn $ "Implies: " ++ show impliesProp
    
    -- 测试语义解释
    let valuation = [("p", True), ("q", False)]
    putStrLn $ "Interpretation of p ∧ q: " ++ show (interpret andProp valuation)
    putStrLn $ "Interpretation of p ∨ q: " ++ show (interpret orProp valuation)
    
    -- 测试有效性
    let excludedMiddle = or' p (not' p)
    putStrLn $ "Excluded middle is valid: " ++ show (isValid excludedMiddle)
    
    -- 测试可满足性
    let satisfiable = and' p q
    putStrLn $ "p ∧ q is satisfiable: " ++ show (isSatisfiable satisfiable)
    
    -- 测试DNF转换
    let complex = or' (and' p q) (and' (not' p) r)
    let dnf = toDNF complex
    putStrLn $ "DNF of (p ∧ q) ∨ (¬p ∧ r): " ++ show dnf
    
    -- 测试推理
    case modusPonens (implies p q) p of
        Just result -> putStrLn $ "Modus ponens result: " ++ show result
        Nothing -> putStrLn "Modus ponens failed"
```

## 10. 参考文献

1. **Frege, G.** (1879). *Begriffsschrift*. Halle.
2. **Russell, B.** (1903). *The Principles of Mathematics*. Cambridge University Press.
3. **Whitehead, A.N. & Russell, B.** (1910). *Principia Mathematica*. Cambridge University Press.
4. **Tarski, A.** (1936). "The Concept of Truth in Formalized Languages". *Logic, Semantics, Metamathematics*.
5. **Church, A.** (1956). *Introduction to Mathematical Logic*. Princeton University Press.
6. **Kleene, S.C.** (1967). *Mathematical Logic*. Wiley.
7. **Enderton, H.B.** (2001). *A Mathematical Introduction to Logic*. Academic Press.

---

**构建者**: AI Assistant  
**最后更新**: 2024年12月20日  
**版本**: v2.0

## 批判性分析

- 本节内容待补充：请从多元理论视角、局限性、争议点、应用前景等方面进行批判性分析。
