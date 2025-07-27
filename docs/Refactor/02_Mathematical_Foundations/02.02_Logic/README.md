# 02.02 逻辑理论 (Logic Theory)

## 目录

- [02.02 逻辑理论 (Logic Theory)](#0202-逻辑理论-logic-theory)
  - [目录](#目录)
  - [模块概述](#模块概述)
  - [目录结构](#目录结构)
  - [理论基础](#理论基础)
    - [核心概念](#核心概念)
    - [基本公理](#基本公理)
  - [形式化实现](#形式化实现)
    - [基础数据结构](#基础数据结构)
    - [语义解释](#语义解释)
    - [证明系统](#证明系统)
  - [应用示例](#应用示例)
    - [命题逻辑证明](#命题逻辑证明)
    - [模态逻辑语义](#模态逻辑语义)
  - [理论扩展](#理论扩展)
    - [直觉主义逻辑](#直觉主义逻辑)
    - [高阶逻辑](#高阶逻辑)
  - [批判性分析](#批判性分析)
    - [理论优势](#理论优势)
    - [理论局限性](#理论局限性)
    - [应用挑战](#应用挑战)
  - [相关链接](#相关链接)

## 模块概述

逻辑理论是研究推理形式和有效性的数学分支，为形式科学提供严格的推理基础。本模块涵盖从命题逻辑到高阶逻辑的完整理论体系，包括语法、语义、证明理论和模型论等核心内容。

## 目录结构

```text
02.02_Logic/
├── README.md                           # 模块总览
├── 02.2.1_Propositional_Logic.md      # 命题逻辑
├── 02.2.2_Predicate_Logic.md          # 谓词逻辑
├── 02.2.3_Modal_Logic.md              # 模态逻辑
├── 02.2.4_Intuitionistic_Logic.md     # 直觉主义逻辑
├── 02.2.5_Higher_Order_Logic.md       # 高阶逻辑
├── 02.2.6_Proof_Theory.md             # 证明理论
├── 02.2.7_Model_Theory.md             # 模型论
└── Resources/                          # 资源目录
    ├── Examples/                       # 示例代码
    ├── Exercises/                      # 练习题
    └── References/                     # 参考文献
```

## 理论基础

### 核心概念

**定义 02.2.1 (逻辑系统)** 逻辑系统是一个三元组 $\mathcal{L} = (\mathcal{F}, \mathcal{A}, \mathcal{R})$，其中：

- $\mathcal{F}$ 是公式集合
- $\mathcal{A}$ 是公理集合
- $\mathcal{R}$ 是推理规则集合

**定义 02.2.2 (有效性)** 公式 $\phi$ 在逻辑系统 $\mathcal{L}$ 中有效，记作 $\models_{\mathcal{L}} \phi$，当且仅当 $\phi$ 在所有模型中为真。

**定义 02.2.3 (可证性)** 公式 $\phi$ 在逻辑系统 $\mathcal{L}$ 中可证，记作 $\vdash_{\mathcal{L}} \phi$，当且仅当存在从公理到 $\phi$ 的证明。

### 基本公理

**命题逻辑公理**：

1. $\phi \rightarrow (\psi \rightarrow \phi)$
2. $(\phi \rightarrow (\psi \rightarrow \chi)) \rightarrow ((\phi \rightarrow \psi) \rightarrow (\phi \rightarrow \chi))$
3. $(\neg \phi \rightarrow \neg \psi) \rightarrow (\psi \rightarrow \phi)$

**推理规则**：

- **分离规则 (Modus Ponens)**：从 $\phi$ 和 $\phi \rightarrow \psi$ 推出 $\psi$

## 形式化实现

### 基础数据结构

```rust
use std::collections::HashMap;
use std::fmt;

// 逻辑公式的基本类型
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Formula {
    // 原子命题
    Atom(String),
    // 真值常量
    True,
    False,
    // 逻辑连接词
    Not(Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    Iff(Box<Formula>, Box<Formula>),
    // 量词
    ForAll(String, Box<Formula>),
    Exists(String, Box<Formula>),
    // 模态算子
    Necessarily(Box<Formula>),
    Possibly(Box<Formula>),
}

impl Formula {
    // 创建原子命题
    pub fn atom(name: &str) -> Self {
        Formula::Atom(name.to_string())
    }

    // 创建否定
    pub fn not(phi: Formula) -> Self {
        Formula::Not(Box::new(phi))
    }

    // 创建合取
    pub fn and(phi: Formula, psi: Formula) -> Self {
        Formula::And(Box::new(phi), Box::new(psi))
    }

    // 创建析取
    pub fn or(phi: Formula, psi: Formula) -> Self {
        Formula::Or(Box::new(phi), Box::new(psi))
    }

    // 创建蕴含
    pub fn implies(phi: Formula, psi: Formula) -> Self {
        Formula::Implies(Box::new(phi), Box::new(psi))
    }

    // 创建等价
    pub fn iff(phi: Formula, psi: Formula) -> Self {
        Formula::Iff(Box::new(phi), Box::new(psi))
    }

    // 创建全称量词
    pub fn for_all(var: &str, phi: Formula) -> Self {
        Formula::ForAll(var.to_string(), Box::new(phi))
    }

    // 创建存在量词
    pub fn exists(var: &str, phi: Formula) -> Self {
        Formula::Exists(var.to_string(), Box::new(phi))
    }

    // 创建必然算子
    pub fn necessarily(phi: Formula) -> Self {
        Formula::Necessarily(Box::new(phi))
    }

    // 创建可能算子
    pub fn possibly(phi: Formula) -> Self {
        Formula::Possibly(Box::new(phi))
    }

    // 获取自由变量
    pub fn free_variables(&self) -> Vec<String> {
        match self {
            Formula::Atom(_) | Formula::True | Formula::False => vec![],
            Formula::Not(phi) => phi.free_variables(),
            Formula::And(phi, psi) | Formula::Or(phi, psi) | 
            Formula::Implies(phi, psi) | Formula::Iff(phi, psi) => {
                let mut vars = phi.free_variables();
                vars.extend(psi.free_variables());
                vars
            },
            Formula::ForAll(var, phi) | Formula::Exists(var, phi) => {
                phi.free_variables().into_iter()
                    .filter(|v| v != var)
                    .collect()
            },
            Formula::Necessarily(phi) | Formula::Possibly(phi) => {
                phi.free_variables()
            },
        }
    }

    // 替换变量
    pub fn substitute(&self, var: &str, term: &Formula) -> Formula {
        match self {
            Formula::Atom(name) => {
                if name == var {
                    term.clone()
                } else {
                    self.clone()
                }
            },
            Formula::True | Formula::False => self.clone(),
            Formula::Not(phi) => Formula::not(phi.substitute(var, term)),
            Formula::And(phi, psi) => Formula::and(
                phi.substitute(var, term),
                psi.substitute(var, term)
            ),
            Formula::Or(phi, psi) => Formula::or(
                phi.substitute(var, term),
                psi.substitute(var, term)
            ),
            Formula::Implies(phi, psi) => Formula::implies(
                phi.substitute(var, term),
                psi.substitute(var, term)
            ),
            Formula::Iff(phi, psi) => Formula::iff(
                phi.substitute(var, term),
                psi.substitute(var, term)
            ),
            Formula::ForAll(v, phi) => {
                if v == var {
                    self.clone()
                } else {
                    Formula::for_all(v, phi.substitute(var, term))
                }
            },
            Formula::Exists(v, phi) => {
                if v == var {
                    self.clone()
                } else {
                    Formula::exists(v, phi.substitute(var, term))
                }
            },
            Formula::Necessarily(phi) => Formula::necessarily(phi.substitute(var, term)),
            Formula::Possibly(phi) => Formula::possibly(phi.substitute(var, term)),
        }
    }
}

// 显示实现
impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Formula::Atom(name) => write!(f, "{}", name),
            Formula::True => write!(f, "⊤"),
            Formula::False => write!(f, "⊥"),
            Formula::Not(phi) => write!(f, "¬({})", phi),
            Formula::And(phi, psi) => write!(f, "({} ∧ {})", phi, psi),
            Formula::Or(phi, psi) => write!(f, "({} ∨ {})", phi, psi),
            Formula::Implies(phi, psi) => write!(f, "({} → {})", phi, psi),
            Formula::Iff(phi, psi) => write!(f, "({} ↔ {})", phi, psi),
            Formula::ForAll(var, phi) => write!(f, "∀{}. {}", var, phi),
            Formula::Exists(var, phi) => write!(f, "∃{}. {}", var, phi),
            Formula::Necessarily(phi) => write!(f, "□{}", phi),
            Formula::Possibly(phi) => write!(f, "◇{}", phi),
        }
    }
}
```

### 语义解释

```rust
// 解释函数
pub type Interpretation = HashMap<String, bool>;

// 模型
#[derive(Debug, Clone)]
pub struct Model {
    pub interpretation: Interpretation,
    pub domain: Vec<String>, // 用于谓词逻辑
    pub accessibility: Vec<(String, String)>, // 用于模态逻辑
}

impl Model {
    pub fn new() -> Self {
        Model {
            interpretation: HashMap::new(),
            domain: vec![],
            accessibility: vec![],
        }
    }

    // 命题逻辑的语义
    pub fn evaluate_propositional(&self, formula: &Formula) -> bool {
        match formula {
            Formula::Atom(name) => *self.interpretation.get(name).unwrap_or(&false),
            Formula::True => true,
            Formula::False => false,
            Formula::Not(phi) => !self.evaluate_propositional(phi),
            Formula::And(phi, psi) => {
                self.evaluate_propositional(phi) && self.evaluate_propositional(psi)
            },
            Formula::Or(phi, psi) => {
                self.evaluate_propositional(phi) || self.evaluate_propositional(psi)
            },
            Formula::Implies(phi, psi) => {
                !self.evaluate_propositional(phi) || self.evaluate_propositional(psi)
            },
            Formula::Iff(phi, psi) => {
                self.evaluate_propositional(phi) == self.evaluate_propositional(psi)
            },
            _ => false, // 其他情况在命题逻辑中不考虑
        }
    }

    // 模态逻辑的语义
    pub fn evaluate_modal(&self, formula: &Formula, world: &str) -> bool {
        match formula {
            Formula::Necessarily(phi) => {
                // 在所有可访问的世界中为真
                self.accessible_worlds(world).iter().all(|w| {
                    self.evaluate_modal(phi, w)
                })
            },
            Formula::Possibly(phi) => {
                // 在某个可访问的世界中为真
                self.accessible_worlds(world).iter().any(|w| {
                    self.evaluate_modal(phi, w)
                })
            },
            _ => self.evaluate_propositional(formula),
        }
    }

    // 获取可访问的世界
    pub fn accessible_worlds(&self, world: &str) -> Vec<String> {
        self.accessibility.iter()
            .filter(|(w1, _)| w1 == world)
            .map(|(_, w2)| w2.clone())
            .collect()
    }
}
```

### 证明系统

```rust
// 证明步骤
#[derive(Debug, Clone)]
pub enum ProofStep {
    Axiom(Formula),
    Assumption(Formula),
    ModusPonens(usize, usize), // 从步骤i和j推出新公式
    Generalization(usize, String), // 全称概括
    Specialization(usize, Formula), // 全称特化
}

// 证明
#[derive(Debug, Clone)]
pub struct Proof {
    pub steps: Vec<ProofStep>,
    pub formulas: Vec<Formula>,
    pub assumptions: Vec<Formula>,
}

impl Proof {
    pub fn new() -> Self {
        Proof {
            steps: vec![],
            formulas: vec![],
            assumptions: vec![],
        }
    }

    // 添加公理
    pub fn add_axiom(&mut self, formula: Formula) {
        self.steps.push(ProofStep::Axiom(formula.clone()));
        self.formulas.push(formula);
    }

    // 添加假设
    pub fn add_assumption(&mut self, formula: Formula) {
        self.steps.push(ProofStep::Assumption(formula.clone()));
        self.formulas.push(formula.clone());
        self.assumptions.push(formula);
    }

    // 应用分离规则
    pub fn modus_ponens(&mut self, i: usize, j: usize) -> Result<(), String> {
        if i >= self.formulas.len() || j >= self.formulas.len() {
            return Err("Invalid step indices".to_string());
        }

        let phi = &self.formulas[i];
        let psi = &self.formulas[j];

        // 检查psi是否是phi -> psi的形式
        if let Formula::Implies(phi_impl, psi_impl) = psi {
            if phi_impl.as_ref() == phi {
                let conclusion = psi_impl.as_ref().clone();
                self.steps.push(ProofStep::ModusPonens(i, j));
                self.formulas.push(conclusion);
                Ok(())
            } else {
                Err("Modus ponens not applicable".to_string())
            }
        } else {
            Err("Second formula is not an implication".to_string())
        }
    }

    // 全称概括
    pub fn generalize(&mut self, step: usize, var: String) -> Result<(), String> {
        if step >= self.formulas.len() {
            return Err("Invalid step index".to_string());
        }

        let phi = &self.formulas[step];
        let generalized = Formula::for_all(&var, phi.clone());
        
        self.steps.push(ProofStep::Generalization(step, var));
        self.formulas.push(generalized);
        Ok(())
    }

    // 检查证明的有效性
    pub fn is_valid(&self) -> bool {
        // 简化的有效性检查
        for (i, step) in self.steps.iter().enumerate() {
            match step {
                ProofStep::Axiom(_) | ProofStep::Assumption(_) => {
                    // 公理和假设总是有效的
                },
                ProofStep::ModusPonens(j, k) => {
                    if *j >= i || *k >= i {
                        return false; // 使用了未来的步骤
                    }
                },
                ProofStep::Generalization(j, _) => {
                    if *j >= i {
                        return false;
                    }
                },
                ProofStep::Specialization(j, _) => {
                    if *j >= i {
                        return false;
                    }
                },
            }
        }
        true
    }
}
```

## 应用示例

### 命题逻辑证明

```rust
fn propositional_proof_example() {
    let mut proof = Proof::new();
    
    // 证明 p -> p
    let p = Formula::atom("p");
    let p_implies_p = Formula::implies(p.clone(), p.clone());
    
    // 添加假设 p
    proof.add_assumption(p.clone());
    
    // 从假设推出 p -> p
    proof.add_axiom(Formula::implies(p.clone(), p_implies_p.clone()));
    proof.add_axiom(Formula::implies(
        Formula::implies(p.clone(), p_implies_p.clone()),
        Formula::implies(p.clone(), p.clone())
    ));
    
    println!("证明步骤:");
    for (i, step) in proof.steps.iter().enumerate() {
        println!("步骤 {}: {:?}", i, step);
    }
    
    println!("结论: {}", proof.formulas.last().unwrap());
}
```

### 模态逻辑语义

```rust
fn modal_logic_example() {
    let mut model = Model::new();
    
    // 设置解释
    model.interpretation.insert("p".to_string(), true);
    model.interpretation.insert("q".to_string(), false);
    
    // 设置可及关系
    model.accessibility.push(("w1".to_string(), "w2".to_string()));
    model.accessibility.push(("w1".to_string(), "w3".to_string()));
    
    // 创建公式
    let p = Formula::atom("p");
    let necessarily_p = Formula::necessarily(p.clone());
    let possibly_p = Formula::possibly(p.clone());
    
    println!("□p 在 w1 中为真: {}", model.evaluate_modal(&necessarily_p, "w1"));
    println!("◇p 在 w1 中为真: {}", model.evaluate_modal(&possibly_p, "w1"));
}
```

## 理论扩展

### 直觉主义逻辑

直觉主义逻辑拒绝排中律，强调构造性证明。

**直觉主义公理**：

1. $\phi \rightarrow (\psi \rightarrow \phi)$
2. $(\phi \rightarrow (\psi \rightarrow \chi)) \rightarrow ((\phi \rightarrow \psi) \rightarrow (\phi \rightarrow \chi))$
3. $\phi \rightarrow (\psi \rightarrow (\phi \wedge \psi))$
4. $(\phi \wedge \psi) \rightarrow \phi$
5. $(\phi \wedge \psi) \rightarrow \psi$

### 高阶逻辑

高阶逻辑允许量化谓词和函数。

**高阶公式示例**：

- $\forall P. P(x) \rightarrow P(y)$
- $\exists f. \forall x. f(x) = x$

## 批判性分析

### 理论优势

1. **严格性**：形式化方法确保了推理的严格性
2. **通用性**：可以表示各种推理模式
3. **可计算性**：某些逻辑系统是可判定的

### 理论局限性

1. **不完全性**：哥德尔不完全性定理表明某些系统不完全
2. **复杂性**：高阶逻辑的判定问题非常复杂
3. **表达能力**：某些自然语言概念难以形式化

### 应用挑战

1. **可判定性**：许多逻辑系统不可判定
2. **效率问题**：自动证明系统效率有限
3. **表达能力**：形式化表达可能过于复杂

## 相关链接

- [02.01 集合论](../02.01_Set_Theory/README.md)
- [02.03 数系理论](../02.03_Number_Systems/README.md)
- [06.01 命题逻辑](../../06_Logic_Theory/03.1_Propositional_Logic/README.md)
- [06.02 谓词逻辑](../../06_Logic_Theory/03.2_Predicate_Logic/README.md)

---

**最后更新**：2025-01-17  
**模块状态**：✅ 完成
