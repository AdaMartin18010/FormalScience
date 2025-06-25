# 逻辑理论 (Logic Theory)

## 概述

逻辑理论是形式化科学的基础，研究推理的有效性和真值的数学结构。本文档系统化阐述命题逻辑、谓词逻辑、模态逻辑等核心逻辑系统及其形式化理论。

## 理论基础

### 形式化定义

**定义 10.1 (逻辑系统)** 逻辑系统是一个三元组 $\mathcal{L} = (L, \vdash, \models)$，其中：

- $L$ 是语言集合
- $\vdash$ 是语法推导关系
- $\models$ 是语义满足关系

**定义 10.2 (逻辑有效性)** 公式 $\phi$ 是逻辑有效的当且仅当：
$$\models \phi \Leftrightarrow \forall \mathcal{M}: \mathcal{M} \models \phi$$

## 命题逻辑 (Propositional Logic)

### 语法

**定义 10.3 (命题公式)** 命题公式的BNF定义：
$$\phi ::= p \mid \neg \phi \mid \phi \land \psi \mid \phi \lor \psi \mid \phi \rightarrow \psi \mid \phi \leftrightarrow \psi$$

其中 $p$ 是命题变量。

```rust
#[derive(Debug, Clone, PartialEq)]
pub enum PropositionalFormula {
    Atom(String),
    Not(Box<PropositionalFormula>),
    And(Box<PropositionalFormula>, Box<PropositionalFormula>),
    Or(Box<PropositionalFormula>, Box<PropositionalFormula>),
    Implies(Box<PropositionalFormula>, Box<PropositionalFormula>),
    Iff(Box<PropositionalFormula>, Box<PropositionalFormula>),
}

impl PropositionalFormula {
    pub fn atom(name: &str) -> Self {
        PropositionalFormula::Atom(name.to_string())
    }

    pub fn not(phi: PropositionalFormula) -> Self {
        PropositionalFormula::Not(Box::new(phi))
    }

    pub fn and(phi: PropositionalFormula, psi: PropositionalFormula) -> Self {
        PropositionalFormula::And(Box::new(phi), Box::new(psi))
    }

    pub fn or(phi: PropositionalFormula, psi: PropositionalFormula) -> Self {
        PropositionalFormula::Or(Box::new(phi), Box::new(psi))
    }

    pub fn implies(phi: PropositionalFormula, psi: PropositionalFormula) -> Self {
        PropositionalFormula::Implies(Box::new(phi), Box::new(psi))
    }

    pub fn iff(phi: PropositionalFormula, psi: PropositionalFormula) -> Self {
        PropositionalFormula::Iff(Box::new(phi), Box::new(psi))
    }
}
```

### 语义

**定义 10.4 (真值赋值)** 真值赋值是一个函数 $v: Prop \rightarrow \{0, 1\}$，其中：

- $v(p) = 1$ 表示命题 $p$ 为真
- $v(p) = 0$ 表示命题 $p$ 为假

**定义 10.5 (满足关系)** 满足关系 $\models$ 递归定义：

- $v \models p$ 当且仅当 $v(p) = 1$
- $v \models \neg \phi$ 当且仅当 $v \not\models \phi$
- $v \models \phi \land \psi$ 当且仅当 $v \models \phi$ 且 $v \models \psi$
- $v \models \phi \lor \psi$ 当且仅当 $v \models \phi$ 或 $v \models \psi$
- $v \models \phi \rightarrow \psi$ 当且仅当 $v \not\models \phi$ 或 $v \models \psi$

```rust
use std::collections::HashMap;

pub struct PropositionalSemantics;

impl PropositionalSemantics {
    pub fn evaluate(
        formula: &PropositionalFormula,
        valuation: &HashMap<String, bool>,
    ) -> bool {
        match formula {
            PropositionalFormula::Atom(name) => {
                *valuation.get(name).unwrap_or(&false)
            }
            PropositionalFormula::Not(phi) => {
                !Self::evaluate(phi, valuation)
            }
            PropositionalFormula::And(phi, psi) => {
                Self::evaluate(phi, valuation) && Self::evaluate(psi, valuation)
            }
            PropositionalFormula::Or(phi, psi) => {
                Self::evaluate(phi, valuation) || Self::evaluate(psi, valuation)
            }
            PropositionalFormula::Implies(phi, psi) => {
                !Self::evaluate(phi, valuation) || Self::evaluate(psi, valuation)
            }
            PropositionalFormula::Iff(phi, psi) => {
                Self::evaluate(phi, valuation) == Self::evaluate(psi, valuation)
            }
        }
    }

    pub fn is_tautology(formula: &PropositionalFormula) -> bool {
        let atoms = Self::collect_atoms(formula);
        Self::check_all_valuations(formula, &atoms, 0, &mut HashMap::new())
    }

    pub fn is_satisfiable(formula: &PropositionalFormula) -> bool {
        let atoms = Self::collect_atoms(formula);
        Self::check_some_valuation(formula, &atoms, 0, &mut HashMap::new())
    }

    fn collect_atoms(formula: &PropositionalFormula) -> Vec<String> {
        let mut atoms = Vec::new();
        Self::collect_atoms_recursive(formula, &mut atoms);
        atoms.sort();
        atoms.dedup();
        atoms
    }

    fn collect_atoms_recursive(formula: &PropositionalFormula, atoms: &mut Vec<String>) {
        match formula {
            PropositionalFormula::Atom(name) => {
                atoms.push(name.clone());
            }
            PropositionalFormula::Not(phi) => {
                Self::collect_atoms_recursive(phi, atoms);
            }
            PropositionalFormula::And(phi, psi) => {
                Self::collect_atoms_recursive(phi, atoms);
                Self::collect_atoms_recursive(psi, atoms);
            }
            PropositionalFormula::Or(phi, psi) => {
                Self::collect_atoms_recursive(phi, atoms);
                Self::collect_atoms_recursive(psi, atoms);
            }
            PropositionalFormula::Implies(phi, psi) => {
                Self::collect_atoms_recursive(phi, atoms);
                Self::collect_atoms_recursive(psi, atoms);
            }
            PropositionalFormula::Iff(phi, psi) => {
                Self::collect_atoms_recursive(phi, atoms);
                Self::collect_atoms_recursive(psi, atoms);
            }
        }
    }

    fn check_all_valuations(
        formula: &PropositionalFormula,
        atoms: &[String],
        index: usize,
        valuation: &mut HashMap<String, bool>,
    ) -> bool {
        if index >= atoms.len() {
            return Self::evaluate(formula, valuation);
        }

        let atom = &atoms[index];
        valuation.insert(atom.clone(), true);
        let result1 = Self::check_all_valuations(formula, atoms, index + 1, valuation);
        valuation.insert(atom.clone(), false);
        let result2 = Self::check_all_valuations(formula, atoms, index + 1, valuation);
        valuation.remove(atom);

        result1 && result2
    }

    fn check_some_valuation(
        formula: &PropositionalFormula,
        atoms: &[String],
        index: usize,
        valuation: &mut HashMap<String, bool>,
    ) -> bool {
        if index >= atoms.len() {
            return Self::evaluate(formula, valuation);
        }

        let atom = &atoms[index];
        valuation.insert(atom.clone(), true);
        let result1 = Self::check_some_valuation(formula, atoms, index + 1, valuation);
        if result1 {
            return true;
        }
        valuation.insert(atom.clone(), false);
        let result2 = Self::check_some_valuation(formula, atoms, index + 1, valuation);
        valuation.remove(atom);

        result2
    }
}
```

### 证明系统

**定义 10.6 (自然演绎)** 自然演绎系统包含以下规则：

**引入规则：**

- $\land I$: $\frac{\phi \quad \psi}{\phi \land \psi}$
- $\lor I_L$: $\frac{\phi}{\phi \lor \psi}$
- $\lor I_R$: $\frac{\psi}{\phi \lor \psi}$
- $\rightarrow I$: $\frac{[\phi] \quad \psi}{\phi \rightarrow \psi}$

**消除规则：**

- $\land E_L$: $\frac{\phi \land \psi}{\phi}$
- $\land E_R$: $\frac{\phi \land \psi}{\psi}$
- $\lor E$: $\frac{\phi \lor \psi \quad [\phi] \quad \chi \quad [\psi] \quad \chi}{\chi}$
- $\rightarrow E$: $\frac{\phi \quad \phi \rightarrow \psi}{\psi}$

```rust
#[derive(Debug, Clone)]
pub enum ProofRule {
    AndIntro(PropositionalFormula, PropositionalFormula),
    AndElimLeft(PropositionalFormula),
    AndElimRight(PropositionalFormula),
    OrIntroLeft(PropositionalFormula, PropositionalFormula),
    OrIntroRight(PropositionalFormula, PropositionalFormula),
    OrElim(PropositionalFormula, PropositionalFormula, PropositionalFormula),
    ImpliesIntro(PropositionalFormula, PropositionalFormula),
    ImpliesElim(PropositionalFormula, PropositionalFormula),
    NotIntro(PropositionalFormula),
    NotElim(PropositionalFormula),
    Assumption(PropositionalFormula),
}

#[derive(Debug, Clone)]
pub struct Proof {
    pub premises: Vec<PropositionalFormula>,
    pub conclusion: PropositionalFormula,
    pub steps: Vec<ProofStep>,
}

#[derive(Debug, Clone)]
pub struct ProofStep {
    pub formula: PropositionalFormula,
    pub rule: ProofRule,
    pub dependencies: Vec<usize>,
}

pub struct NaturalDeduction;

impl NaturalDeduction {
    pub fn prove_implies_intro(
        premise: PropositionalFormula,
        conclusion: PropositionalFormula,
    ) -> Proof {
        let mut proof = Proof {
            premises: vec![premise.clone()],
            conclusion: PropositionalFormula::implies(premise.clone(), conclusion.clone()),
            steps: Vec::new(),
        };

        // 添加假设
        proof.steps.push(ProofStep {
            formula: premise.clone(),
            rule: ProofRule::Assumption(premise.clone()),
            dependencies: vec![0],
        });

        // 添加结论
        proof.steps.push(ProofStep {
            formula: conclusion.clone(),
            rule: ProofRule::Assumption(conclusion.clone()),
            dependencies: vec![1],
        });

        // 应用蕴含引入规则
        proof.steps.push(ProofStep {
            formula: PropositionalFormula::implies(premise, conclusion),
            rule: ProofRule::ImpliesIntro(
                proof.steps[0].formula.clone(),
                proof.steps[1].formula.clone(),
            ),
            dependencies: vec![0, 1],
        });

        proof
    }

    pub fn prove_modus_ponens(
        premise1: PropositionalFormula,
        premise2: PropositionalFormula,
    ) -> Proof {
        let mut proof = Proof {
            premises: vec![premise1.clone(), premise2.clone()],
            conclusion: match &premise2 {
                PropositionalFormula::Implies(_, psi) => *psi.clone(),
                _ => panic!("Second premise must be an implication"),
            },
            steps: Vec::new(),
        };

        // 添加前提
        proof.steps.push(ProofStep {
            formula: premise1.clone(),
            rule: ProofRule::Assumption(premise1.clone()),
            dependencies: vec![0],
        });

        proof.steps.push(ProofStep {
            formula: premise2.clone(),
            rule: ProofRule::Assumption(premise2.clone()),
            dependencies: vec![1],
        });

        // 应用蕴含消除规则
        proof.steps.push(ProofStep {
            formula: proof.conclusion.clone(),
            rule: ProofRule::ImpliesElim(premise1, premise2),
            dependencies: vec![0, 1],
        });

        proof
    }

    pub fn prove_and_intro(
        premise1: PropositionalFormula,
        premise2: PropositionalFormula,
    ) -> Proof {
        let mut proof = Proof {
            premises: vec![premise1.clone(), premise2.clone()],
            conclusion: PropositionalFormula::and(premise1.clone(), premise2.clone()),
            steps: Vec::new(),
        };

        // 添加前提
        proof.steps.push(ProofStep {
            formula: premise1.clone(),
            rule: ProofRule::Assumption(premise1.clone()),
            dependencies: vec![0],
        });

        proof.steps.push(ProofStep {
            formula: premise2.clone(),
            rule: ProofRule::Assumption(premise2.clone()),
            dependencies: vec![1],
        });

        // 应用合取引入规则
        proof.steps.push(ProofStep {
            formula: proof.conclusion.clone(),
            rule: ProofRule::AndIntro(premise1, premise2),
            dependencies: vec![0, 1],
        });

        proof
    }
}
```

## 谓词逻辑 (Predicate Logic)

### 语法1

**定义 10.7 (一阶语言)** 一阶语言是一个四元组 $\mathcal{L} = (C, F, P, V)$，其中：

- $C$ 是常元集合
- $F$ 是函数符号集合
- $P$ 是谓词符号集合
- $V$ 是变量集合

**定义 10.8 (项)** 项的BNF定义：
$$t ::= c \mid x \mid f(t_1, \ldots, t_n)$$

**定义 10.9 (公式)** 公式的BNF定义：
$$\phi ::= P(t_1, \ldots, t_n) \mid \neg \phi \mid \phi \land \psi \mid \phi \lor \psi \mid \phi \rightarrow \psi \mid \forall x \phi \mid \exists x \phi$$

```rust
#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    Constant(String),
    Variable(String),
    Function(String, Vec<Term>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum PredicateFormula {
    Atom(String, Vec<Term>),
    Not(Box<PredicateFormula>),
    And(Box<PredicateFormula>, Box<PredicateFormula>),
    Or(Box<PredicateFormula>, Box<PredicateFormula>),
    Implies(Box<PredicateFormula>, Box<PredicateFormula>),
    ForAll(String, Box<PredicateFormula>),
    Exists(String, Box<PredicateFormula>),
}

impl PredicateFormula {
    pub fn atom(predicate: &str, terms: Vec<Term>) -> Self {
        PredicateFormula::Atom(predicate.to_string(), terms)
    }

    pub fn for_all(variable: &str, formula: PredicateFormula) -> Self {
        PredicateFormula::ForAll(variable.to_string(), Box::new(formula))
    }

    pub fn exists(variable: &str, formula: PredicateFormula) -> Self {
        PredicateFormula::Exists(variable.to_string(), Box::new(formula))
    }

    pub fn free_variables(&self) -> Vec<String> {
        let mut vars = Vec::new();
        Self::collect_free_variables(self, &mut vars);
        vars.sort();
        vars.dedup();
        vars
    }

    fn collect_free_variables(formula: &PredicateFormula, vars: &mut Vec<String>) {
        match formula {
            PredicateFormula::Atom(_, terms) => {
                for term in terms {
                    Self::collect_term_variables(term, vars);
                }
            }
            PredicateFormula::Not(phi) => {
                Self::collect_free_variables(phi, vars);
            }
            PredicateFormula::And(phi, psi) => {
                Self::collect_free_variables(phi, vars);
                Self::collect_free_variables(psi, vars);
            }
            PredicateFormula::Or(phi, psi) => {
                Self::collect_free_variables(phi, vars);
                Self::collect_free_variables(psi, vars);
            }
            PredicateFormula::Implies(phi, psi) => {
                Self::collect_free_variables(phi, vars);
                Self::collect_free_variables(psi, vars);
            }
            PredicateFormula::ForAll(var, phi) => {
                Self::collect_free_variables(phi, vars);
                vars.retain(|v| v != var);
            }
            PredicateFormula::Exists(var, phi) => {
                Self::collect_free_variables(phi, vars);
                vars.retain(|v| v != var);
            }
        }
    }

    fn collect_term_variables(term: &Term, vars: &mut Vec<String>) {
        match term {
            Term::Variable(name) => vars.push(name.clone()),
            Term::Function(_, args) => {
                for arg in args {
                    Self::collect_term_variables(arg, vars);
                }
            }
            Term::Constant(_) => {}
        }
    }
}
```

### 语义1

**定义 10.10 (结构)** 结构是一个对偶 $\mathcal{M} = (D, I)$，其中：

- $D$ 是非空论域
- $I$ 是解释函数

**定义 10.11 (赋值)** 赋值是一个函数 $s: V \rightarrow D$，将变量映射到论域元素。

**定义 10.12 (满足关系)** 满足关系 $\mathcal{M}, s \models \phi$ 递归定义：

- $\mathcal{M}, s \models P(t_1, \ldots, t_n)$ 当且仅当 $(I(t_1), \ldots, I(t_n)) \in I(P)$
- $\mathcal{M}, s \models \forall x \phi$ 当且仅当对所有 $d \in D$，$\mathcal{M}, s[x \mapsto d] \models \phi$
- $\mathcal{M}, s \models \exists x \phi$ 当且仅当存在 $d \in D$，$\mathcal{M}, s[x \mapsto d] \models \phi$

```rust
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct Structure {
    pub domain: Vec<String>,
    pub interpretation: Interpretation,
}

#[derive(Debug, Clone)]
pub struct Interpretation {
    pub constants: HashMap<String, String>,
    pub functions: HashMap<String, Vec<String>>,
    pub predicates: HashMap<String, Vec<Vec<String>>>,
}

pub struct PredicateSemantics;

impl PredicateSemantics {
    pub fn evaluate_term(
        term: &Term,
        structure: &Structure,
        assignment: &HashMap<String, String>,
    ) -> String {
        match term {
            Term::Constant(name) => {
                structure.interpretation.constants.get(name)
                    .cloned()
                    .unwrap_or_else(|| format!("undefined_constant_{}", name))
            }
            Term::Variable(name) => {
                assignment.get(name)
                    .cloned()
                    .unwrap_or_else(|| format!("undefined_variable_{}", name))
            }
            Term::Function(name, args) => {
                let arg_values: Vec<String> = args.iter()
                    .map(|arg| Self::evaluate_term(arg, structure, assignment))
                    .collect();
                
                if let Some(function) = structure.interpretation.functions.get(name) {
                    // 简化的函数求值
                    format!("{}({})", name, arg_values.join(", "))
                } else {
                    format!("undefined_function_{}({})", name, arg_values.join(", "))
                }
            }
        }
    }

    pub fn evaluate_formula(
        formula: &PredicateFormula,
        structure: &Structure,
        assignment: &HashMap<String, String>,
    ) -> bool {
        match formula {
            PredicateFormula::Atom(predicate, terms) => {
                let term_values: Vec<String> = terms.iter()
                    .map(|term| Self::evaluate_term(term, structure, assignment))
                    .collect();
                
                if let Some(extension) = structure.interpretation.predicates.get(predicate) {
                    extension.contains(&term_values)
                } else {
                    false
                }
            }
            PredicateFormula::Not(phi) => {
                !Self::evaluate_formula(phi, structure, assignment)
            }
            PredicateFormula::And(phi, psi) => {
                Self::evaluate_formula(phi, structure, assignment) &&
                Self::evaluate_formula(psi, structure, assignment)
            }
            PredicateFormula::Or(phi, psi) => {
                Self::evaluate_formula(phi, structure, assignment) ||
                Self::evaluate_formula(psi, structure, assignment)
            }
            PredicateFormula::Implies(phi, psi) => {
                !Self::evaluate_formula(phi, structure, assignment) ||
                Self::evaluate_formula(psi, structure, assignment)
            }
            PredicateFormula::ForAll(variable, phi) => {
                for element in &structure.domain {
                    let mut new_assignment = assignment.clone();
                    new_assignment.insert(variable.clone(), element.clone());
                    if !Self::evaluate_formula(phi, structure, &new_assignment) {
                        return false;
                    }
                }
                true
            }
            PredicateFormula::Exists(variable, phi) => {
                for element in &structure.domain {
                    let mut new_assignment = assignment.clone();
                    new_assignment.insert(variable.clone(), element.clone());
                    if Self::evaluate_formula(phi, structure, &new_assignment) {
                        return true;
                    }
                }
                false
            }
        }
    }

    pub fn is_valid(formula: &PredicateFormula) -> bool {
        // 简化的有效性检查
        // 实际实现需要检查所有可能的结构和赋值
        true
    }

    pub fn is_satisfiable(formula: &PredicateFormula) -> bool {
        // 简化的可满足性检查
        // 实际实现需要寻找满足的结构和赋值
        true
    }
}
```

## 模态逻辑 (Modal Logic)

### 语法2

**定义 10.13 (模态公式)** 模态公式的BNF定义：
$$\phi ::= p \mid \neg \phi \mid \phi \land \psi \mid \phi \lor \psi \mid \phi \rightarrow \psi \mid \Box \phi \mid \Diamond \phi$$

其中 $\Box$ 是必然算子，$\Diamond$ 是可能算子。

```rust
#[derive(Debug, Clone, PartialEq)]
pub enum ModalFormula {
    Atom(String),
    Not(Box<ModalFormula>),
    And(Box<ModalFormula>, Box<ModalFormula>),
    Or(Box<ModalFormula>, Box<ModalFormula>),
    Implies(Box<ModalFormula>, Box<ModalFormula>),
    Necessity(Box<ModalFormula>),
    Possibility(Box<ModalFormula>),
}

impl ModalFormula {
    pub fn necessity(phi: ModalFormula) -> Self {
        ModalFormula::Necessity(Box::new(phi))
    }

    pub fn possibility(phi: ModalFormula) -> Self {
        ModalFormula::Possibility(Box::new(phi))
    }

    pub fn dual(phi: &ModalFormula) -> ModalFormula {
        match phi {
            ModalFormula::Necessity(psi) => ModalFormula::possibility(Self::not(*psi.clone())),
            ModalFormula::Possibility(psi) => ModalFormula::necessity(Self::not(*psi.clone())),
            _ => phi.clone(),
        }
    }

    fn not(phi: ModalFormula) -> ModalFormula {
        ModalFormula::Not(Box::new(phi))
    }
}
```

### 语义2

**定义 10.14 (克里普克模型)** 克里普克模型是一个三元组 $\mathcal{M} = (W, R, V)$，其中：

- $W$ 是可能世界集合
- $R \subseteq W \times W$ 是可达关系
- $V: W \times Prop \rightarrow \{0, 1\}$ 是赋值函数

**定义 10.15 (模态满足关系)** 满足关系 $\mathcal{M}, w \models \phi$ 递归定义：

- $\mathcal{M}, w \models \Box \phi$ 当且仅当对所有 $v$ 使得 $wRv$，$\mathcal{M}, v \models \phi$
- $\mathcal{M}, w \models \Diamond \phi$ 当且仅当存在 $v$ 使得 $wRv$ 且 $\mathcal{M}, v \models \phi$

```rust
#[derive(Debug, Clone)]
pub struct KripkeModel {
    pub worlds: Vec<String>,
    pub accessibility: Vec<(String, String)>,
    pub valuation: HashMap<(String, String), bool>,
}

pub struct ModalSemantics;

impl ModalSemantics {
    pub fn evaluate(
        formula: &ModalFormula,
        model: &KripkeModel,
        world: &str,
    ) -> bool {
        match formula {
            ModalFormula::Atom(prop) => {
                *model.valuation.get(&(world.to_string(), prop.clone())).unwrap_or(&false)
            }
            ModalFormula::Not(phi) => {
                !Self::evaluate(phi, model, world)
            }
            ModalFormula::And(phi, psi) => {
                Self::evaluate(phi, model, world) && Self::evaluate(psi, model, world)
            }
            ModalFormula::Or(phi, psi) => {
                Self::evaluate(phi, model, world) || Self::evaluate(psi, model, world)
            }
            ModalFormula::Implies(phi, psi) => {
                !Self::evaluate(phi, model, world) || Self::evaluate(psi, model, world)
            }
            ModalFormula::Necessity(phi) => {
                let accessible_worlds = Self::get_accessible_worlds(model, world);
                accessible_worlds.iter().all(|w| Self::evaluate(phi, model, w))
            }
            ModalFormula::Possibility(phi) => {
                let accessible_worlds = Self::get_accessible_worlds(model, world);
                accessible_worlds.iter().any(|w| Self::evaluate(phi, model, w))
            }
        }
    }

    fn get_accessible_worlds(model: &KripkeModel, world: &str) -> Vec<String> {
        model.accessibility.iter()
            .filter(|(w1, _)| w1 == world)
            .map(|(_, w2)| w2.clone())
            .collect()
    }

    pub fn is_valid_in_model(formula: &ModalFormula, model: &KripkeModel) -> bool {
        model.worlds.iter().all(|world| Self::evaluate(formula, model, world))
    }

    pub fn is_satisfiable_in_model(formula: &ModalFormula, model: &KripkeModel) -> bool {
        model.worlds.iter().any(|world| Self::evaluate(formula, model, world))
    }
}
```

## 形式化验证

### 逻辑等价性

**定义 10.16 (逻辑等价)** 两个公式 $\phi$ 和 $\psi$ 逻辑等价当且仅当：
$$\models \phi \leftrightarrow \psi$$

**定理 10.1 (德摩根律)** 对于任意公式 $\phi$ 和 $\psi$：
$$\neg(\phi \land \psi) \equiv \neg\phi \lor \neg\psi$$
$$\neg(\phi \lor \psi) \equiv \neg\phi \land \neg\psi$$

**定理 10.2 (量词对偶性)** 对于任意公式 $\phi$：
$$\neg\forall x \phi \equiv \exists x \neg\phi$$
$$\neg\exists x \phi \equiv \forall x \neg\phi$$

```rust
pub struct LogicalEquivalence;

impl LogicalEquivalence {
    pub fn de_morgan_not_and(phi: &PropositionalFormula, psi: &PropositionalFormula) -> bool {
        let left = PropositionalFormula::not(PropositionalFormula::and(phi.clone(), psi.clone()));
        let right = PropositionalFormula::or(
            PropositionalFormula::not(phi.clone()),
            PropositionalFormula::not(psi.clone()),
        );
        
        PropositionalSemantics::is_tautology(&PropositionalFormula::iff(left, right))
    }

    pub fn de_morgan_not_or(phi: &PropositionalFormula, psi: &PropositionalFormula) -> bool {
        let left = PropositionalFormula::not(PropositionalFormula::or(phi.clone(), psi.clone()));
        let right = PropositionalFormula::and(
            PropositionalFormula::not(phi.clone()),
            PropositionalFormula::not(psi.clone()),
        );
        
        PropositionalSemantics::is_tautology(&PropositionalFormula::iff(left, right))
    }

    pub fn quantifier_duality_not_forall(formula: &PredicateFormula) -> bool {
        // 检查 ¬∀x φ ≡ ∃x ¬φ
        // 简化实现
        true
    }

    pub fn quantifier_duality_not_exists(formula: &PredicateFormula) -> bool {
        // 检查 ¬∃x φ ≡ ∀x ¬φ
        // 简化实现
        true
    }
}
```

### 证明系统2

**定理 10.3 (完备性)** 对于命题逻辑：
$$\vdash \phi \Leftrightarrow \models \phi$$

**定理 10.4 (可靠性)** 对于谓词逻辑：
$$\vdash \phi \Rightarrow \models \phi$$

**证明** 通过结构归纳法证明每个推理规则保持有效性。

## 总结

逻辑理论为形式化推理提供了严格的数学基础。命题逻辑处理简单命题，谓词逻辑处理量化语句，模态逻辑处理可能性和必然性。这些逻辑系统为计算机科学、人工智能和哲学提供了重要的理论基础。

## 参考文献

1. Enderton, H. B. (2001). A Mathematical Introduction to Logic.
2. van Dalen, D. (2013). Logic and Structure.
3. Blackburn, P., de Rijke, M., & Venema, Y. (2001). Modal Logic.

## 相关链接

- [集合论](../02_Mathematical_Foundations/01_Set_Theory/README.md)
- [范畴论](../02_Mathematical_Foundations/07_Category_Theory/README.md)
- [形式语言理论](../04_Formal_Language_Theory/README.md)
