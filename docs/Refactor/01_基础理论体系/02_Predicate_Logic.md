# 02. 谓词逻辑 (Predicate Logic)

## 目录

1. [基本概念](#1-基本概念)
2. [语法](#2-语法)
3. [语义](#3-语义)
4. [推理系统](#4-推理系统)
5. [范式理论](#5-范式理论)
6. [完备性定理](#6-完备性定理)
7. [模型论基础](#7-模型论基础)
8. [一阶逻辑](#8-一阶逻辑)
9. [高阶逻辑](#9-高阶逻辑)
10. [应用与算法](#10-应用与算法)

## 1. 基本概念

### 1.1 谓词逻辑概述

**定义 1.1.1** (谓词逻辑)
谓词逻辑是研究量化语句的逻辑系统，它扩展了命题逻辑，能够处理包含个体、谓词和量词的复杂语句。

**定义 1.1.2** (语言)
谓词逻辑的语言 $\mathcal{L}$ 包含：

- 个体变量：$x, y, z, ...$
- 个体常项：$a, b, c, ...$
- 谓词符号：$P, Q, R, ...$
- 函数符号：$f, g, h, ...$
- 逻辑连接词：$\neg, \land, \lor, \to, \leftrightarrow$
- 量词：$\forall$（全称量词），$\exists$（存在量词）
- 等号：$=$

### 1.2 项与公式

**定义 1.2.1** (项)
项递归定义如下：

1. 个体变量和个体常项是项
2. 如果 $f$ 是 $n$ 元函数符号，$t_1, ..., t_n$ 是项，则 $f(t_1, ..., t_n)$ 是项
3. 只有通过上述规则构造的表达式才是项

**定义 1.2.2** (原子公式)
原子公式是形如 $P(t_1, ..., t_n)$ 或 $t_1 = t_2$ 的表达式，其中 $P$ 是 $n$ 元谓词符号，$t_1, ..., t_n$ 是项。

**定义 1.2.3** (公式)
公式递归定义如下：

1. 原子公式是公式
2. 如果 $\phi$ 是公式，则 $\neg\phi$ 是公式
3. 如果 $\phi$ 和 $\psi$ 是公式，则 $(\phi \land \psi)$、$(\phi \lor \psi)$、$(\phi \to \psi)$、$(\phi \leftrightarrow \psi)$ 是公式
4. 如果 $\phi$ 是公式，$x$ 是变量，则 $\forall x \phi$ 和 $\exists x \phi$ 是公式
5. 只有通过上述规则构造的表达式才是公式

## 2. 语法

### 2.1 自由变量与约束变量

**定义 2.1.1** (自由变量)
变量 $x$ 在公式 $\phi$ 中自由出现，递归定义如下：

1. 在原子公式 $P(t_1, ..., t_n)$ 中，$x$ 自由出现当且仅当 $x$ 在某个 $t_i$ 中出现
2. 在 $\neg\phi$ 中，$x$ 自由出现当且仅当 $x$ 在 $\phi$ 中自由出现
3. 在 $\phi \circ \psi$ 中（$\circ$ 是二元连接词），$x$ 自由出现当且仅当 $x$ 在 $\phi$ 或 $\psi$ 中自由出现
4. 在 $\forall y \phi$ 或 $\exists y \phi$ 中，$x$ 自由出现当且仅当 $x \neq y$ 且 $x$ 在 $\phi$ 中自由出现

**定义 2.1.2** (约束变量)
变量 $x$ 在公式 $\phi$ 中约束出现，如果 $x$ 在 $\phi$ 中出现但不自由出现。

**定义 2.1.3** (句子)
不包含自由变量的公式称为句子或闭公式。

### 2.2 替换

**定义 2.2.1** (替换)
用项 $t$ 替换公式 $\phi$ 中变量 $x$ 的所有自由出现，记作 $\phi[t/x]$，递归定义如下：

1. 如果 $\phi$ 是原子公式 $P(t_1, ..., t_n)$，则 $\phi[t/x] = P(t_1[t/x], ..., t_n[t/x])$
2. $[\neg\phi](t/x) = \neg(\phi[t/x])$
3. $[\phi \circ \psi](t/x) = \phi[t/x] \circ \psi[t/x]$
4. $[\forall y \phi](t/x) = \forall y (\phi[t/x])$（如果 $y \neq x$）
5. $[\exists y \phi](t/x) = \exists y (\phi[t/x])$（如果 $y \neq x$）

**定义 2.2.2** (可替换性)
项 $t$ 对变量 $x$ 在公式 $\phi$ 中可替换，如果 $t$ 中没有任何变量在 $\phi$ 中被 $x$ 约束。

## 3. 语义

### 3.1 结构

**定义 3.1.1** (结构)
语言 $\mathcal{L}$ 的结构 $\mathcal{A}$ 包含：

1. 非空集合 $A$（论域）
2. 对每个 $n$ 元谓词符号 $P$，指派 $P^{\mathcal{A}} \subseteq A^n$
3. 对每个 $n$ 元函数符号 $f$，指派 $f^{\mathcal{A}}: A^n \to A$
4. 对每个个体常项 $c$，指派 $c^{\mathcal{A}} \in A$

### 3.2 赋值

**定义 3.2.1** (赋值)
结构 $\mathcal{A}$ 上的赋值是函数 $s: \text{Var} \to A$，其中 $\text{Var}$ 是变量集。

**定义 3.2.2** (项的解释)
项 $t$ 在结构 $\mathcal{A}$ 和赋值 $s$ 下的解释 $t^{\mathcal{A}}[s]$ 递归定义：

1. $x^{\mathcal{A}}[s] = s(x)$
2. $c^{\mathcal{A}}[s] = c^{\mathcal{A}}$
3. $f(t_1, ..., t_n)^{\mathcal{A}}[s] = f^{\mathcal{A}}(t_1^{\mathcal{A}}[s], ..., t_n^{\mathcal{A}}[s])$

### 3.3 满足关系

**定义 3.3.1** (满足关系)
结构 $\mathcal{A}$ 和赋值 $s$ 满足公式 $\phi$，记作 $\mathcal{A} \models \phi[s]$，递归定义：

1. $\mathcal{A} \models P[t_1, ..., t_n](s)$ 当且仅当 $(t_1^{\mathcal{A}}[s], ..., t_n^{\mathcal{A}}[s]) \in P^{\mathcal{A}}$
2. $\mathcal{A} \models t_1 = t_2[s]$ 当且仅当 $t_1^{\mathcal{A}}[s] = t_2^{\mathcal{A}}[s]$
3. $\mathcal{A} \models \neg\phi[s]$ 当且仅当 $\mathcal{A} \not\models \phi[s]$
4. $\mathcal{A} \models \phi \land \psi[s]$ 当且仅当 $\mathcal{A} \models \phi[s]$ 且 $\mathcal{A} \models \psi[s]$
5. $\mathcal{A} \models \phi \lor \psi[s]$ 当且仅当 $\mathcal{A} \models \phi[s]$ 或 $\mathcal{A} \models \psi[s]$
6. $\mathcal{A} \models \phi \to \psi[s]$ 当且仅当 $\mathcal{A} \not\models \phi[s]$ 或 $\mathcal{A} \models \psi[s]$
7. $\mathcal{A} \models \forall x \phi[s]$ 当且仅当对所有 $a \in A$，$\mathcal{A} \models \phi[s(x|a)]$
8. $\mathcal{A} \models \exists x \phi[s]$ 当且仅当存在 $a \in A$，$\mathcal{A} \models \phi[s(x|a)]$

其中 $s(x|a)$ 表示将赋值 $s$ 中 $x$ 的值改为 $a$。

### 3.4 有效性、可满足性与逻辑后承

**定义 3.4.1** (有效性)
公式 $\phi$ 是有效的，记作 $\models \phi$，如果对所有结构 $\mathcal{A}$ 和赋值 $s$，都有 $\mathcal{A} \models \phi[s]$。

**定义 3.4.2** (可满足性)
公式 $\phi$ 是可满足的，如果存在结构 $\mathcal{A}$ 和赋值 $s$，使得 $\mathcal{A} \models \phi[s]$。

**定义 3.4.3** (逻辑后承)
公式 $\psi$ 是公式集 $\Gamma$ 的逻辑后承，记作 $\Gamma \models \psi$，如果对所有结构 $\mathcal{A}$ 和赋值 $s$，如果 $\mathcal{A} \models \phi[s]$ 对所有 $\phi \in \Gamma$，则 $\mathcal{A} \models \psi[s]$。

## 4. 推理系统

### 4.1 自然演绎系统

**定义 4.1.1** (自然演绎规则)
谓词逻辑的自然演绎系统包含命题逻辑的所有规则，以及以下量词规则：

**全称引入** (∀I)：
$$\frac{\phi[t/x]}{\forall x \phi}$$
其中 $t$ 是任意项，$t$ 对 $x$ 在 $\phi$ 中可替换。

**全称消除** (∀E)：
$$\frac{\forall x \phi}{\phi[t/x]}$$
其中 $t$ 是任意项，$t$ 对 $x$ 在 $\phi$ 中可替换。

**存在引入** (∃I)：
$$\frac{\phi[t/x]}{\exists x \phi}$$
其中 $t$ 是任意项，$t$ 对 $x$ 在 $\phi$ 中可替换。

**存在消除** (∃E)：
$$\frac{\exists x \phi \quad \phi[y/x] \vdash \psi}{\psi}$$
其中 $y$ 是新的变量，不在 $\phi$ 或 $\psi$ 中自由出现。

### 4.2 希尔伯特系统

**定义 4.2.1** (公理)
谓词逻辑的希尔伯特系统包含以下公理：

**命题逻辑公理**：

1. $\phi \to (\psi \to \phi)$
2. $(\phi \to (\psi \to \chi)) \to ((\phi \to \psi) \to (\phi \to \chi))$
3. $(\neg\phi \to \neg\psi) \to (\psi \to \phi)$

**量词公理**：

1. $\forall x \phi \to \phi[t/x]$（$t$ 对 $x$ 在 $\phi$ 中可替换）
2. $\phi[t/x] \to \exists x \phi$（$t$ 对 $x$ 在 $\phi$ 中可替换）
3. $\forall x (\phi \to \psi) \to (\forall x \phi \to \forall x \psi)$
4. $\forall x (\phi \to \psi) \to (\exists x \phi \to \exists x \psi)$

**推理规则**：

- 分离规则：从 $\phi$ 和 $\phi \to \psi$ 推出 $\psi$
- 概括规则：从 $\phi$ 推出 $\forall x \phi$（$x$ 不在 $\phi$ 中自由出现）

### 4.3 证明示例

**定理 4.3.1** (量词对偶性)
$\neg\forall x \phi \leftrightarrow \exists x \neg\phi$

**证明**：

```lean
-- Lean 4 证明示例
theorem quantifier_duality (α : Type*) (P : α → Prop) :
  (¬∀ x, P x) ↔ (∃ x, ¬P x) :=
begin
  split,
  { -- 从左到右
    intro h,
    -- 使用排中律和选择公理
    sorry
  },
  { -- 从右到左
    intro h,
    cases h with x hx,
    intro h_forall,
    exact hx (h_forall x)
  }
end
```

## 5. 范式理论

### 5.1 前束范式

**定义 5.1.1** (前束范式)
公式 $\phi$ 是前束范式，如果它具有形式：
$$Q_1 x_1 Q_2 x_2 \cdots Q_n x_n \psi$$
其中 $Q_i$ 是量词（$\forall$ 或 $\exists$），$\psi$ 是不包含量词的公式（矩阵）。

**定理 5.1.1** (前束范式存在性)
每个公式都等价于某个前束范式。

**证明**：
通过以下步骤将任意公式转换为前束范式：

1. 消除 $\to$ 和 $\leftrightarrow$
2. 将否定符号内移
3. 重命名变量避免冲突
4. 将量词前移

```rust
// Rust 实现：前束范式转换
#[derive(Clone, Debug)]
pub enum Quantifier {
    ForAll(String),
    Exists(String),
}

#[derive(Clone, Debug)]
pub struct PrenexForm {
    pub quantifiers: Vec<Quantifier>,
    pub matrix: Formula,
}

pub fn to_prenex_form(formula: &Formula) -> PrenexForm {
    let mut result = formula.clone();

    // 步骤1：消除蕴含和等价
    result = eliminate_implications(&result);

    // 步骤2：否定内移
    result = move_negations_inward(&result);

    // 步骤3：变量重命名
    result = rename_variables(&result);

    // 步骤4：量词前移
    let (quantifiers, matrix) = move_quantifiers_forward(&result);

    PrenexForm { quantifiers, matrix }
}
```

### 5.2 斯科伦范式

**定义 5.2.1** (斯科伦范式)
前束范式是斯科伦范式，如果所有存在量词都在全称量词之前。

**定理 5.2.1** (斯科伦范式存在性)
每个公式都等价于某个斯科伦范式。

### 5.3 合取范式与析取范式

**定义 5.3.1** (合取范式)
不包含量词的公式是合取范式，如果它是析取式的合取。

**定义 5.3.2** (析取范式)
不包含量词的公式是析取范式，如果它是合取式的析取。

## 6. 完备性定理

### 6.1 哥德尔完备性定理

**定理 6.1.1** (哥德尔完备性定理)
如果 $\Gamma \models \phi$，则 $\Gamma \vdash \phi$。

**证明**：
使用亨金构造法：

1. 将 $\Gamma$ 扩展为极大一致集
2. 构造典范模型
3. 证明该模型满足 $\Gamma$ 但不满足 $\phi$（如果 $\Gamma \not\vdash \phi$）

### 6.2 紧致性定理

**定理 6.2.1** (紧致性定理)
公式集 $\Gamma$ 是可满足的当且仅当 $\Gamma$ 的每个有限子集都是可满足的。

**推论 6.2.1** (紧致性定理的推论)
如果 $\Gamma \models \phi$，则存在 $\Gamma$ 的有限子集 $\Delta$ 使得 $\Delta \models \phi$。

### 6.3 勒文海姆-斯科伦定理

**定理 6.3.1** (勒文海姆-斯科伦定理)
如果可数语言的理论有无限模型，则它对任意无限基数都有模型。

## 7. 模型论基础

### 7.1 初等等价

**定义 7.1.1** (初等等价)
结构 $\mathcal{A}$ 和 $\mathcal{B}$ 初等等价，记作 $\mathcal{A} \equiv \mathcal{B}$，如果它们满足相同的句子。

### 7.2 初等嵌入

**定义 7.2.1** (初等嵌入)
函数 $f: A \to B$ 是初等嵌入，如果对所有公式 $\phi(x_1, ..., x_n)$ 和 $a_1, ..., a_n \in A$：
$$\mathcal{A} \models \phi[a_1, ..., a_n] \text{ 当且仅当 } \mathcal{B} \models \phi[f(a_1), ..., f(a_n)]$$

### 7.3 饱和模型

**定义 7.3.1** (饱和模型)
结构 $\mathcal{A}$ 是 $\kappa$-饱和的，如果对每个基数 $\lambda < \kappa$ 和每个类型 $p$，如果 $p$ 在 $\mathcal{A}$ 中是可实现的，则 $p$ 在 $\mathcal{A}$ 中是可满足的。

## 8. 一阶逻辑

### 8.1 一阶理论

**定义 8.1.1** (一阶理论)
一阶理论是句子的集合，在逻辑后承下封闭。

**定义 8.1.2** (公理化理论)
理论 $T$ 是公理化的，如果存在递归集 $\Gamma$ 使得 $T = \{\phi \mid \Gamma \vdash \phi\}$。

### 8.2 模型完全性

**定义 8.2.1** (模型完全性)
理论 $T$ 是模型完全的，如果对任意模型 $\mathcal{A}, \mathcal{B} \models T$，如果 $\mathcal{A} \subseteq \mathcal{B}$，则 $\mathcal{A} \preceq \mathcal{B}$。

### 8.3 量词消去

**定义 8.3.1** (量词消去)
理论 $T$ 允许量词消去，如果对每个公式 $\phi$，存在无量词公式 $\psi$ 使得 $T \vdash \phi \leftrightarrow \psi$。

## 9. 高阶逻辑

### 9.1 二阶逻辑

**定义 9.1.1** (二阶逻辑)
二阶逻辑允许量化谓词和函数。

**语法扩展**：

- 谓词变量：$X, Y, Z, ...$
- 函数变量：$F, G, H, ...$
- 二阶量词：$\forall X, \exists X, \forall F, \exists F$

### 9.2 高阶逻辑的性质

**定理 9.2.1** (高阶逻辑的不完备性)
二阶逻辑不是递归可公理化的。

**定理 9.2.2** (紧致性定理失效)
二阶逻辑不满足紧致性定理。

## 10. 应用与算法

### 10.1 自动定理证明

#### 10.1.1 归结方法

基于前束范式和斯科伦化的自动证明方法。

```rust
// Rust 实现：归结方法
pub struct ResolutionProver {
    clauses: Vec<Clause>,
}

impl ResolutionProver {
    pub fn new(formula: &Formula) -> Self {
        let prenex = to_prenex_form(formula);
        let skolem = to_skolem_form(&prenex);
        let clauses = to_clauses(&skolem.matrix);

        ResolutionProver { clauses }
    }

    pub fn prove(&mut self) -> bool {
        let mut new_clauses = Vec::new();

        loop {
            // 生成所有可能的归结
            for i in 0..self.clauses.len() {
                for j in i+1..self.clauses.len() {
                    if let Some(resolvent) = self.clauses[i].resolve(&self.clauses[j]) {
                        if resolvent.is_empty() {
                            return true; // 找到空子句，证明完成
                        }
                        if !self.clauses.contains(&resolvent) && !new_clauses.contains(&resolvent) {
                            new_clauses.push(resolvent);
                        }
                    }
                }
            }

            if new_clauses.is_empty() {
                return false; // 无法生成新的子句
            }

            self.clauses.extend(new_clauses.drain(..));
        }
    }
}
```

#### 10.1.2 表方法

基于语义表的证明方法。

### 10.2 模型检查

#### 10.2.1 有限模型检查

检查公式在有限结构上的有效性。

```rust
// Rust 实现：有限模型检查
pub struct FiniteModelChecker {
    domain_size: usize,
    predicates: Vec<Vec<Vec<bool>>>,
    functions: Vec<Vec<Vec<usize>>>,
}

impl FiniteModelChecker {
    pub fn new(domain_size: usize, predicate_count: usize, function_count: usize) -> Self {
        FiniteModelChecker {
            domain_size,
            predicates: vec![vec![vec![false; domain_size]; domain_size]; predicate_count],
            functions: vec![vec![vec![0; domain_size]; domain_size]; function_count],
        }
    }

    pub fn check_formula(&self, formula: &Formula) -> bool {
        // 枚举所有可能的赋值
        self.check_all_assignments(formula, &mut vec![0; formula.free_variables().len()], 0)
    }

    fn check_all_assignments(&self, formula: &Formula, assignment: &mut Vec<usize>, pos: usize) -> bool {
        if pos == assignment.len() {
            return self.evaluate_formula(formula, assignment);
        }

        for value in 0..self.domain_size {
            assignment[pos] = value;
            if !self.check_all_assignments(formula, assignment, pos + 1) {
                return false;
            }
        }
        true
    }
}
```

### 10.3 逻辑编程

#### 10.3.1 Prolog 语言

基于一阶逻辑的编程语言。

```prolog
% Prolog 示例：家族关系
parent(john, mary).
parent(john, bob).
parent(mary, ann).
parent(bob, charlie).

grandparent(X, Z) :- parent(X, Y), parent(Y, Z).
ancestor(X, Y) :- parent(X, Y).
ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).

% 查询
% ?- grandparent(john, ann).
% ?- ancestor(john, charlie).
```

#### 10.3.2 约束逻辑编程

扩展逻辑编程以处理约束。

### 10.4 数据库理论

#### 10.4.1 关系代数

基于一阶逻辑的数据库查询语言。

```sql
-- SQL 示例：关系代数
SELECT name, age
FROM students
WHERE age > 18 AND department = 'Computer Science';

-- 等价的一阶逻辑公式
-- ∃x ∃y (Student(x, name, age, 'Computer Science') ∧ age > 18)
```

#### 10.4.2 数据库完整性约束

使用一阶逻辑表达数据库约束。

## 参考文献

1. Enderton, H. B. (2001). _A Mathematical Introduction to Logic_. Academic Press.
2. Mendelson, E. (2015). _Introduction to Mathematical Logic_. CRC Press.
3. Shoenfield, J. R. (2001). _Mathematical Logic_. A K Peters.
4. Boolos, G. S., Burgess, J. P., & Jeffrey, R. C. (2007). _Computability and Logic_. Cambridge University Press.
5. Chang, C. C., & Keisler, H. J. (2012). _Model Theory_. Dover Publications.

## 交叉引用

- [01_Philosophical_Foundations/01_Epistemological_Foundations.md](../01_Philosophical_Foundations/01_Epistemological_Foundations.md) - 逻辑推理的认识论基础
- [02_Mathematical_Foundations/01_Set_Theory.md](../02_Mathematical_Foundations/01_Set_Theory/01_Set_Theory.md) - 集合论基础
- [03_Logic_Theory/01_Propositional_Logic.md](01_Propositional_Logic.md) - 命题逻辑基础
- [03_Formal_Language_Theory/03.2_Formal_Grammars.md](../03_Formal_Language_Theory/03.2_Formal_Grammars.md) - 形式语言理论
- [05_Type_Theory/01_Type_Theory_Foundations.md](../05_Type_Theory/01_Type_Theory_Foundations.md) - 类型理论基础
- [12_Database_Theory/01_Relational_Database_Theory.md](../12_Database_Theory/01_Relational_Database_Theory.md) - 关系数据库理论

## 批判性分析

- 多元理论视角：
  - 表达力与复杂性：一阶逻辑在表达力与可判定性间取得平衡，为数学与计算机科学提供基础。
  - 模型论与证明论：语义与语法的双重视角，通过完备性定理实现统一。
- 局限性分析：
  - 不完备性：哥德尔不完备性定理揭示一阶逻辑的固有局限性。
  - 计算复杂度：一般一阶逻辑不可判定，需要特殊子集或近似方法。
- 争议与分歧：
  - 选择公理：在集合论中的采用影响数学体系的构建。
- 应用前景：
  - 自动定理证明、程序验证、知识表示、数据库理论等领域的持续发展。
- 改进建议：
  - 开发高效的证明系统与模型检查工具；建立从一阶逻辑到高阶逻辑的扩展框架。
