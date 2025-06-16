# 命题逻辑基础 (Propositional Logic Basics)

## 📋 概述

命题逻辑是逻辑学的基础，研究命题之间的逻辑关系。本文档建立了严格的命题逻辑形式化体系，包括命题的基本概念、逻辑连接词、推理规则和语义解释。

## 📚 目录

1. [基本概念](#1-基本概念)
2. [逻辑连接词](#2-逻辑连接词)
3. [命题公式](#3-命题公式)
4. [推理规则](#4-推理规则)
5. [语义解释](#5-语义解释)
6. [命题逻辑定理](#6-命题逻辑定理)
7. [命题逻辑算法](#7-命题逻辑算法)
8. [应用实例](#8-应用实例)
9. [参考文献](#9-参考文献)

## 1. 基本概念

### 1.1 命题的定义

**定义 1.1 (命题)**
命题是一个有真假值的陈述句。我们用 $p, q, r, \ldots$ 表示命题变元，用 $T$ 表示真，用 $F$ 表示假。

**定义 1.2 (原子命题)**
原子命题是不可再分解的基本命题，也称为命题变元。

**定义 1.3 (复合命题)**
复合命题是由原子命题通过逻辑连接词构成的命题。

**定义 1.4 (真值)**
真值是命题的真假性，用 $v(p)$ 表示命题 $p$ 的真值：
$$v(p) \in \{T, F\}$$

### 1.2 命题的基本性质

**公理 1.1 (排中律)**
对于任意命题 $p$，$p$ 为真或 $p$ 为假：
$$\forall p(v(p) = T \lor v(p) = F)$$

**公理 1.2 (矛盾律)**
对于任意命题 $p$，$p$ 不能同时为真和为假：
$$\forall p(\neg(v(p) = T \land v(p) = F))$$

**公理 1.3 (同一律)**
对于任意命题 $p$，$p$ 等价于 $p$：
$$\forall p(p \leftrightarrow p)$$

## 2. 逻辑连接词

### 2.1 基本连接词

**定义 2.1 (否定)**
否定连接词 $\neg$ 表示"非"，满足：
- $v(\neg p) = T$ 当且仅当 $v(p) = F$
- $v(\neg p) = F$ 当且仅当 $v(p) = T$

**定义 2.2 (合取)**
合取连接词 $\land$ 表示"且"，满足：
- $v(p \land q) = T$ 当且仅当 $v(p) = T$ 且 $v(q) = T$
- $v(p \land q) = F$ 当且仅当 $v(p) = F$ 或 $v(q) = F$

**定义 2.3 (析取)**
析取连接词 $\lor$ 表示"或"，满足：
- $v(p \lor q) = T$ 当且仅当 $v(p) = T$ 或 $v(q) = T$
- $v(p \lor q) = F$ 当且仅当 $v(p) = F$ 且 $v(q) = F$

**定义 2.4 (蕴含)**
蕴含连接词 $\rightarrow$ 表示"如果...那么"，满足：
- $v(p \rightarrow q) = T$ 当且仅当 $v(p) = F$ 或 $v(q) = T$
- $v(p \rightarrow q) = F$ 当且仅当 $v(p) = T$ 且 $v(q) = F$

**定义 2.5 (等价)**
等价连接词 $\leftrightarrow$ 表示"当且仅当"，满足：
- $v(p \leftrightarrow q) = T$ 当且仅当 $v(p) = v(q)$
- $v(p \leftrightarrow q) = F$ 当且仅当 $v(p) \neq v(q)$

### 2.2 真值表

**表 2.1 (基本连接词真值表)**

| $p$ | $q$ | $\neg p$ | $p \land q$ | $p \lor q$ | $p \rightarrow q$ | $p \leftrightarrow q$ |
|-----|-----|----------|-------------|------------|-------------------|----------------------|
| T   | T   | F        | T           | T          | T                 | T                    |
| T   | F   | F        | F           | T          | F                 | F                    |
| F   | T   | T        | F           | T          | T                 | F                    |
| F   | F   | T        | F           | F          | T                 | T                    |

### 2.3 连接词的性质

**定理 2.1 (德摩根律)**
1. $\neg(p \land q) \leftrightarrow \neg p \lor \neg q$
2. $\neg(p \lor q) \leftrightarrow \neg p \land \neg q$

**定理 2.2 (分配律)**
1. $p \land (q \lor r) \leftrightarrow (p \land q) \lor (p \land r)$
2. $p \lor (q \land r) \leftrightarrow (p \lor q) \land (p \lor r)$

**定理 2.3 (双重否定律)**
$\neg \neg p \leftrightarrow p$

## 3. 命题公式

### 3.1 公式的定义

**定义 3.1 (命题公式)**
命题公式的递归定义：
1. 原子命题是公式
2. 如果 $\phi$ 是公式，那么 $\neg \phi$ 是公式
3. 如果 $\phi$ 和 $\psi$ 是公式，那么 $(\phi \land \psi)$、$(\phi \lor \psi)$、$(\phi \rightarrow \psi)$、$(\phi \leftrightarrow \psi)$ 是公式
4. 只有通过以上规则构造的才是公式

**定义 3.2 (子公式)**
子公式是公式的组成部分，递归定义：
1. 公式 $\phi$ 是 $\phi$ 的子公式
2. 如果 $\neg \psi$ 是 $\phi$ 的子公式，那么 $\psi$ 是 $\phi$ 的子公式
3. 如果 $(\psi_1 \circ \psi_2)$ 是 $\phi$ 的子公式，那么 $\psi_1$ 和 $\psi_2$ 是 $\phi$ 的子公式

### 3.2 公式的分类

**定义 3.3 (重言式)**
重言式是在所有真值赋值下都为真的公式：
$$\forall v(v(\phi) = T)$$

**定义 3.4 (矛盾式)**
矛盾式是在所有真值赋值下都为假的公式：
$$\forall v(v(\phi) = F)$$

**定义 3.5 (可满足式)**
可满足式是至少在一个真值赋值下为真的公式：
$$\exists v(v(\phi) = T)$$

**定义 3.6 (偶然式)**
偶然式既不是重言式也不是矛盾式的公式。

### 3.3 公式的等价

**定义 3.7 (逻辑等价)**
两个公式 $\phi$ 和 $\psi$ 逻辑等价，记作 $\phi \equiv \psi$，当且仅当在所有真值赋值下它们具有相同的真值：
$$\phi \equiv \psi \leftrightarrow \forall v(v(\phi) = v(\psi))$$

**定理 3.1 (等价关系)**
逻辑等价是等价关系：
1. 自反性：$\phi \equiv \phi$
2. 对称性：$\phi \equiv \psi \rightarrow \psi \equiv \phi$
3. 传递性：$(\phi \equiv \psi \land \psi \equiv \chi) \rightarrow \phi \equiv \chi$

## 4. 推理规则

### 4.1 基本推理规则

**规则 4.1 (肯定前件)**
$$\frac{p \rightarrow q \quad p}{q} \quad \text{(MP)}$$

**规则 4.2 (否定后件)**
$$\frac{p \rightarrow q \quad \neg q}{\neg p} \quad \text{(MT)}$$

**规则 4.3 (假言三段论)**
$$\frac{p \rightarrow q \quad q \rightarrow r}{p \rightarrow r} \quad \text{(HS)}$$

**规则 4.4 (构造性二难)**
$$\frac{p \rightarrow q \quad r \rightarrow s \quad p \lor r}{q \lor s} \quad \text{(CD)}$$

**规则 4.5 (析取三段论)**
$$\frac{p \lor q \quad \neg p}{q} \quad \text{(DS)}$$

### 4.2 导出规则

**规则 4.6 (合取引入)**
$$\frac{p \quad q}{p \land q} \quad \text{(Conj)}$$

**规则 4.7 (合取消除)**
$$\frac{p \land q}{p} \quad \text{(Simp)}$$

**规则 4.8 (析取引入)**
$$\frac{p}{p \lor q} \quad \text{(Add)}$$

**规则 4.9 (等价替换)**
$$\frac{p \leftrightarrow q \quad \phi(p)}{\phi(q)} \quad \text{(Equiv)}$$

### 4.3 证明系统

**定义 4.1 (证明)**
证明是从前提推出结论的有限序列，每一步都应用了推理规则。

**定义 4.2 (有效性)**
推理是有效的，当且仅当前提为真时结论必为真。

**定义 4.3 (完备性)**
证明系统是完备的，当且仅当所有有效的推理都能在系统中得到证明。

## 5. 语义解释

### 5.1 真值赋值

**定义 5.1 (真值赋值)**
真值赋值是从命题变元到真值的函数：
$$v: \mathcal{P} \rightarrow \{T, F\}$$
其中 $\mathcal{P}$ 是命题变元的集合。

**定义 5.2 (真值赋值扩展)**
真值赋值可以扩展到所有公式：
1. $v(\neg \phi) = T$ 当且仅当 $v(\phi) = F$
2. $v(\phi \land \psi) = T$ 当且仅当 $v(\phi) = T$ 且 $v(\psi) = T$
3. $v(\phi \lor \psi) = T$ 当且仅当 $v(\phi) = T$ 或 $v(\psi) = T$
4. $v(\phi \rightarrow \psi) = T$ 当且仅当 $v(\phi) = F$ 或 $v(\psi) = T$
5. $v(\phi \leftrightarrow \psi) = T$ 当且仅当 $v(\phi) = v(\psi)$

### 5.2 语义概念

**定义 5.3 (满足)**
真值赋值 $v$ 满足公式 $\phi$，记作 $v \models \phi$，当且仅当 $v(\phi) = T$。

**定义 5.4 (逻辑蕴含)**
公式集 $\Gamma$ 逻辑蕴含公式 $\phi$，记作 $\Gamma \models \phi$，当且仅当所有满足 $\Gamma$ 的真值赋值都满足 $\phi$。

**定义 5.5 (逻辑等价)**
公式 $\phi$ 和 $\psi$ 逻辑等价，记作 $\phi \models \psi$，当且仅当 $\phi \models \psi$ 且 $\psi \models \phi$。

### 5.3 语义定理

**定理 5.1 (可靠性定理)**
如果 $\Gamma \vdash \phi$，那么 $\Gamma \models \phi$。

**定理 5.2 (完备性定理)**
如果 $\Gamma \models \phi$，那么 $\Gamma \vdash \phi$。

**定理 5.3 (紧致性定理)**
如果 $\Gamma \models \phi$，那么存在 $\Gamma$ 的有限子集 $\Delta$ 使得 $\Delta \models \phi$。

## 6. 命题逻辑定理

### 6.1 基本定理

**定理 6.1 (重言式定理)**
如果 $\phi$ 是重言式，那么 $\vdash \phi$。

**定理 6.2 (矛盾式定理)**
如果 $\phi$ 是矛盾式，那么 $\phi \vdash \psi$ 对于任意公式 $\psi$。

**定理 6.3 (可满足性定理)**
公式 $\phi$ 是可满足的，当且仅当 $\neg \phi$ 不是重言式。

### 6.2 高级定理

**定理 6.4 (析取范式定理)**
每个命题公式都等价于一个析取范式。

**定理 6.5 (合取范式定理)**
每个命题公式都等价于一个合取范式。

**定理 6.6 (主析取范式定理)**
每个命题公式都等价于唯一的主析取范式。

**定理 6.7 (主合取范式定理)**
每个命题公式都等价于唯一的主合取范式。

### 6.3 复杂性定理

**定理 6.8 (可满足性问题)**
命题逻辑的可满足性问题是NP完全问题。

**定理 6.9 (重言式问题)**
命题逻辑的重言式问题是co-NP完全问题。

**定理 6.10 (等价性问题)**
命题逻辑的等价性问题是co-NP完全问题。

## 7. 命题逻辑算法

### 7.1 真值表算法

```rust
/// 真值表算法
pub trait TruthTable {
    /// 计算公式的真值表
    fn truth_table(&self, formula: &Formula) -> Vec<TruthAssignment>;
    
    /// 检查公式是否为重言式
    fn is_tautology(&self, formula: &Formula) -> bool;
    
    /// 检查公式是否为矛盾式
    fn is_contradiction(&self, formula: &Formula) -> bool;
    
    /// 检查公式是否为可满足式
    fn is_satisfiable(&self, formula: &Formula) -> bool;
    
    /// 检查两个公式是否等价
    fn are_equivalent(&self, formula1: &Formula, formula2: &Formula) -> bool;
}

/// 真值表实现
pub struct TruthTableImpl {
    variables: Vec<Variable>,
}

impl TruthTable for TruthTableImpl {
    fn truth_table(&self, formula: &Formula) -> Vec<TruthAssignment> {
        let mut assignments = Vec::new();
        let num_vars = self.variables.len();
        
        // 生成所有可能的真值赋值
        for i in 0..(1 << num_vars) {
            let mut assignment = TruthAssignment::new();
            
            for (j, var) in self.variables.iter().enumerate() {
                let value = (i & (1 << j)) != 0;
                assignment.set(var.clone(), value);
            }
            
            let result = self.evaluate(formula, &assignment);
            assignment.set_result(result);
            assignments.push(assignment);
        }
        
        assignments
    }
    
    fn is_tautology(&self, formula: &Formula) -> bool {
        self.truth_table(formula).iter().all(|a| a.result())
    }
    
    fn is_contradiction(&self, formula: &Formula) -> bool {
        self.truth_table(formula).iter().all(|a| !a.result())
    }
    
    fn is_satisfiable(&self, formula: &Formula) -> bool {
        self.truth_table(formula).iter().any(|a| a.result())
    }
    
    fn are_equivalent(&self, formula1: &Formula, formula2: &Formula) -> bool {
        let table1 = self.truth_table(formula1);
        let table2 = self.truth_table(formula2);
        
        table1.iter().zip(table2.iter()).all(|(a1, a2)| a1.result() == a2.result())
    }
    
    fn evaluate(&self, formula: &Formula, assignment: &TruthAssignment) -> bool {
        match formula {
            Formula::Variable(var) => assignment.get(var),
            Formula::Negation(inner) => !self.evaluate(inner, assignment),
            Formula::Conjunction(left, right) => {
                self.evaluate(left, assignment) && self.evaluate(right, assignment)
            }
            Formula::Disjunction(left, right) => {
                self.evaluate(left, assignment) || self.evaluate(right, assignment)
            }
            Formula::Implication(left, right) => {
                !self.evaluate(left, assignment) || self.evaluate(right, assignment)
            }
            Formula::Equivalence(left, right) => {
                self.evaluate(left, assignment) == self.evaluate(right, assignment)
            }
        }
    }
}
```

### 7.2 证明搜索算法

```rust
/// 证明搜索算法
pub trait ProofSearch {
    /// 搜索证明
    fn search_proof(&self, premises: &[Formula], conclusion: &Formula) -> Option<Proof>;
    
    /// 检查推理是否有效
    fn is_valid_inference(&self, premises: &[Formula], conclusion: &Formula) -> bool;
    
    /// 生成反例
    fn generate_counterexample(&self, premises: &[Formula], conclusion: &Formula) -> Option<TruthAssignment>;
    
    /// 应用推理规则
    fn apply_rule(&self, rule: &InferenceRule, premises: &[Formula]) -> Option<Formula>;
}

/// 证明搜索实现
pub struct ProofSearchImpl {
    rules: Vec<InferenceRule>,
    truth_table: Box<dyn TruthTable>,
}

impl ProofSearch for ProofSearchImpl {
    fn search_proof(&self, premises: &[Formula], conclusion: &Formula) -> Option<Proof> {
        let mut proof = Proof::new();
        
        // 添加前提
        for premise in premises {
            proof.add_premise(premise.clone());
        }
        
        // 搜索证明
        self.search_backward(&mut proof, conclusion)
    }
    
    fn is_valid_inference(&self, premises: &[Formula], conclusion: &Formula) -> bool {
        // 使用真值表检查有效性
        let combined_premise = if premises.is_empty() {
            conclusion.clone()
        } else {
            premises.iter().fold(premises[0].clone(), |acc, p| {
                Formula::Conjunction(Box::new(acc), Box::new(p.clone()))
            })
        };
        
        let implication = Formula::Implication(Box::new(combined_premise), Box::new(conclusion.clone()));
        self.truth_table.is_tautology(&implication)
    }
    
    fn generate_counterexample(&self, premises: &[Formula], conclusion: &Formula) -> Option<TruthAssignment> {
        // 生成反例
        let combined_premise = if premises.is_empty() {
            conclusion.clone()
        } else {
            premises.iter().fold(premises[0].clone(), |acc, p| {
                Formula::Conjunction(Box::new(acc), Box::new(p.clone()))
            })
        };
        
        let implication = Formula::Implication(Box::new(combined_premise), Box::new(conclusion.clone()));
        
        // 找到使蕴含为假的赋值
        for assignment in self.truth_table.truth_table(&implication) {
            if !assignment.result() {
                return Some(assignment);
            }
        }
        
        None
    }
    
    fn apply_rule(&self, rule: &InferenceRule, premises: &[Formula]) -> Option<Formula> {
        rule.apply(premises)
    }
    
    fn search_backward(&self, proof: &mut Proof, goal: &Formula) -> Option<Proof> {
        // 反向证明搜索
        if proof.contains(goal) {
            return Some(proof.clone());
        }
        
        // 尝试应用推理规则
        for rule in &self.rules {
            if let Some(new_goals) = rule.backward_apply(goal) {
                for new_goal in new_goals {
                    let mut new_proof = proof.clone();
                    if let Some(sub_proof) = self.search_backward(&mut new_proof, &new_goal) {
                        sub_proof.apply_rule(rule, goal);
                        return Some(sub_proof);
                    }
                }
            }
        }
        
        None
    }
}
```

## 8. 应用实例

### 8.1 数学应用

**实例 8.1 (数学推理)**
证明：如果 $p \rightarrow q$ 且 $q \rightarrow r$，那么 $p \rightarrow r$。

**证明**：
1. $p \rightarrow q$ (前提)
2. $q \rightarrow r$ (前提)
3. $p \rightarrow r$ (假言三段论，从1和2)

**实例 8.2 (逻辑等价)**
证明：$\neg(p \land q) \leftrightarrow \neg p \lor \neg q$ (德摩根律)

**证明**：
通过真值表验证：

| $p$ | $q$ | $p \land q$ | $\neg(p \land q)$ | $\neg p$ | $\neg q$ | $\neg p \lor \neg q$ |
|-----|-----|-------------|-------------------|----------|----------|----------------------|
| T   | T   | T           | F                 | F        | F        | F                    |
| T   | F   | F           | T                 | F        | T        | T                    |
| F   | T   | F           | T                 | T        | F        | T                    |
| F   | F   | F           | T                 | T        | T        | T                    |

### 8.2 计算机科学应用

**实例 8.3 (电路设计)**
设计一个电路实现 $p \land (q \lor r)$：

```rust
/// 电路实现
pub struct Circuit {
    inputs: Vec<bool>,
    gates: Vec<Gate>,
}

pub enum Gate {
    And(usize, usize),  // 输入索引
    Or(usize, usize),   // 输入索引
    Not(usize),         // 输入索引
}

impl Circuit {
    pub fn evaluate(&self, inputs: &[bool]) -> bool {
        let mut values = inputs.to_vec();
        
        for gate in &self.gates {
            let result = match gate {
                Gate::And(i, j) => values[*i] && values[*j],
                Gate::Or(i, j) => values[*i] || values[*j],
                Gate::Not(i) => !values[*i],
            };
            values.push(result);
        }
        
        values.last().copied().unwrap_or(false)
    }
}
```

**实例 8.4 (程序验证)**
验证程序逻辑：如果 $x > 0$ 且 $y > 0$，那么 $x + y > 0$。

**形式化**：
- $p$: $x > 0$
- $q$: $y > 0$
- $r$: $x + y > 0$
- 要证明：$(p \land q) \rightarrow r$

**证明**：
1. 假设 $p \land q$
2. 从 $p$ 得到 $x > 0$
3. 从 $q$ 得到 $y > 0$
4. 因此 $x + y > 0 + 0 = 0$
5. 所以 $r$ 成立
6. 因此 $(p \land q) \rightarrow r$

### 8.3 哲学应用

**实例 8.5 (苏格拉底论证)**
苏格拉底论证：
1. 所有人都是会死的
2. 苏格拉底是人
3. 因此苏格拉底是会死的

**形式化**：
- $p$: 所有人都是会死的
- $q$: 苏格拉底是人
- $r$: 苏格拉底是会死的
- 要证明：$(p \land q) \rightarrow r$

**实例 8.6 (悖论分析)**
说谎者悖论：这句话是假的。

**形式化**：
- $p$: 这句话是假的
- 如果 $p$ 为真，那么 $p$ 为假
- 如果 $p$ 为假，那么 $p$ 为真
- 矛盾：$p \land \neg p$

## 9. 参考文献

1. Enderton, H.B. *A Mathematical Introduction to Logic*. Academic Press, 2001.
2. Mendelson, E. *Introduction to Mathematical Logic*. Chapman & Hall, 2009.
3. Boolos, G.S., Burgess, J.P., & Jeffrey, R.C. *Computability and Logic*. Cambridge University Press, 2007.
4. Huth, M., & Ryan, M. *Logic in Computer Science: Modelling and Reasoning about Systems*. Cambridge University Press, 2004.
5. Smullyan, R.M. *First-Order Logic*. Dover, 1995.
6. Quine, W.V.O. *Methods of Logic*. Harvard University Press, 1982.
7. Copi, I.M., & Cohen, C. *Introduction to Logic*. Pearson, 2005.
8. Lemmon, E.J. *Beginning Logic*. Hackett, 1978.

---

**最后更新时间**: 2024年12月20日  
**版本**: v1.0  
**维护者**: 逻辑学理论团队 