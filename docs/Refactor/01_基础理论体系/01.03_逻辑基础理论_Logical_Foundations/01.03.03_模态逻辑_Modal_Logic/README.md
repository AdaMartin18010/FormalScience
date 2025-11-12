# 模态逻辑 (Modal Logic)

## 📋 目录

- [1 概述](#1-概述)
- [2 理论基础](#2-理论基础)
  - [2.1 形式化定义](#21-形式化定义)
- [3 语法实现](#3-语法实现)
  - [3.1 数据结构](#31-数据结构)
  - [3.2 解析器实现](#32-解析器实现)
- [4 语义实现](#4-语义实现)
  - [4.1 克里普克模型](#41-克里普克模型)
  - [4.2 模态系统](#42-模态系统)
- [5 形式化验证](#5-形式化验证)
  - [5.1 框架对应性](#51-框架对应性)
  - [5.2 完备性定理](#52-完备性定理)
  - [5.3 紧致性定理](#53-紧致性定理)
- [6 应用领域](#6-应用领域)
  - [6.1 认知逻辑](#61-认知逻辑)
  - [6.2 时态逻辑](#62-时态逻辑)
  - [6.3 道义逻辑](#63-道义逻辑)
- [7 总结](#7-总结)
- [8 相关链接](#8-相关链接)
- [9 批判性分析](#9-批判性分析)

---

## 1 概述

模态逻辑是研究必然性和可能性概念的数学理论，广泛应用于哲学、计算机科学和人工智能。
本文档详细阐述模态逻辑的语法、语义、克里普克模型和各种模态系统。

## 2 理论基础

### 2.1 形式化定义

**定义 10.3.1 (模态语言)** 模态语言是一个三元组 $\mathcal{L} = (Prop, Conn, Form)$，其中：

- $Prop$ 是命题变量集合
- $Conn$ 是逻辑连接词集合 $\{\neg, \land, \lor, \rightarrow, \leftrightarrow, \Box, \Diamond\}$
- $Form$ 是模态公式集合

**定义 10.3.2 (模态公式)** 模态公式的BNF定义：
$$\phi ::= p \mid \neg \phi \mid \phi \land \psi \mid \phi \lor \psi \mid \phi \rightarrow \psi \mid \phi \leftrightarrow \psi \mid \Box \phi \mid \Diamond \phi$$

其中 $\Box$ 是必然算子，$\Diamond$ 是可能算子。

**定义 10.3.3 (对偶性)** 必然和可能算子是对偶的：
$$\Box \phi \equiv \neg \Diamond \neg \phi$$
$$\Diamond \phi \equiv \neg \Box \neg \phi$$

## 3 语法实现

### 3.1 数据结构

```rust
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ModalFormula {
    Atom(String),
    Not(Box<ModalFormula>),
    And(Box<ModalFormula>, Box<ModalFormula>),
    Or(Box<ModalFormula>, Box<ModalFormula>),
    Implies(Box<ModalFormula>, Box<ModalFormula>),
    Iff(Box<ModalFormula>, Box<ModalFormula>),
    Necessity(Box<ModalFormula>),
    Possibility(Box<ModalFormula>),
}

impl ModalFormula {
    pub fn atom(name: &str) -> Self {
        ModalFormula::Atom(name.to_string())
    }

    pub fn not(phi: ModalFormula) -> Self {
        ModalFormula::Not(Box::new(phi))
    }

    pub fn and(phi: ModalFormula, psi: ModalFormula) -> Self {
        ModalFormula::And(Box::new(phi), Box::new(psi))
    }

    pub fn or(phi: ModalFormula, psi: ModalFormula) -> Self {
        ModalFormula::Or(Box::new(phi), Box::new(psi))
    }

    pub fn implies(phi: ModalFormula, psi: ModalFormula) -> Self {
        ModalFormula::Implies(Box::new(phi), Box::new(psi))
    }

    pub fn iff(phi: ModalFormula, psi: ModalFormula) -> Self {
        ModalFormula::Iff(Box::new(phi), Box::new(psi))
    }

    pub fn necessity(phi: ModalFormula) -> Self {
        ModalFormula::Necessity(Box::new(phi))
    }

    pub fn possibility(phi: ModalFormula) -> Self {
        ModalFormula::Possibility(Box::new(phi))
    }

    pub fn dual(phi: &ModalFormula) -> ModalFormula {
        match phi {
            ModalFormula::Necessity(psi) => {
                ModalFormula::possibility(Self::not(*psi.clone()))
            }
            ModalFormula::Possibility(psi) => {
                ModalFormula::necessity(Self::not(*psi.clone()))
            }
            _ => phi.clone(),
        }
    }

    pub fn collect_atoms(&self) -> Vec<String> {
        let mut atoms = Vec::new();
        self.collect_atoms_recursive(&mut atoms);
        atoms.sort();
        atoms.dedup();
        atoms
    }

    fn collect_atoms_recursive(&self, atoms: &mut Vec<String>) {
        match self {
            ModalFormula::Atom(name) => {
                atoms.push(name.clone());
            }
            ModalFormula::Not(phi) => {
                phi.collect_atoms_recursive(atoms);
            }
            ModalFormula::And(phi, psi) => {
                phi.collect_atoms_recursive(atoms);
                psi.collect_atoms_recursive(atoms);
            }
            ModalFormula::Or(phi, psi) => {
                phi.collect_atoms_recursive(atoms);
                psi.collect_atoms_recursive(atoms);
            }
            ModalFormula::Implies(phi, psi) => {
                phi.collect_atoms_recursive(atoms);
                psi.collect_atoms_recursive(atoms);
            }
            ModalFormula::Iff(phi, psi) => {
                phi.collect_atoms_recursive(atoms);
                psi.collect_atoms_recursive(atoms);
            }
            ModalFormula::Necessity(phi) => {
                phi.collect_atoms_recursive(atoms);
            }
            ModalFormula::Possibility(phi) => {
                phi.collect_atoms_recursive(atoms);
            }
        }
    }

    pub fn complexity(&self) -> usize {
        match self {
            ModalFormula::Atom(_) => 0,
            ModalFormula::Not(phi) => 1 + phi.complexity(),
            ModalFormula::And(phi, psi) => 1 + phi.complexity() + psi.complexity(),
            ModalFormula::Or(phi, psi) => 1 + phi.complexity() + psi.complexity(),
            ModalFormula::Implies(phi, psi) => 1 + phi.complexity() + psi.complexity(),
            ModalFormula::Iff(phi, psi) => 1 + phi.complexity() + psi.complexity(),
            ModalFormula::Necessity(phi) => 1 + phi.complexity(),
            ModalFormula::Possibility(phi) => 1 + phi.complexity(),
        }
    }

    pub fn is_atomic(&self) -> bool {
        matches!(self, ModalFormula::Atom(_))
    }

    pub fn is_modal(&self) -> bool {
        matches!(self, ModalFormula::Necessity(_) | ModalFormula::Possibility(_))
    }

    pub fn modal_depth(&self) -> usize {
        match self {
            ModalFormula::Atom(_) => 0,
            ModalFormula::Not(phi) => phi.modal_depth(),
            ModalFormula::And(phi, psi) => phi.modal_depth().max(psi.modal_depth()),
            ModalFormula::Or(phi, psi) => phi.modal_depth().max(psi.modal_depth()),
            ModalFormula::Implies(phi, psi) => phi.modal_depth().max(psi.modal_depth()),
            ModalFormula::Iff(phi, psi) => phi.modal_depth().max(psi.modal_depth()),
            ModalFormula::Necessity(phi) => 1 + phi.modal_depth(),
            ModalFormula::Possibility(phi) => 1 + phi.modal_depth(),
        }
    }
}

impl std::fmt::Display for ModalFormula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ModalFormula::Atom(name) => write!(f, "{}", name),
            ModalFormula::Not(phi) => {
                if phi.is_atomic() || phi.is_modal() {
                    write!(f, "¬{}", phi)
                } else {
                    write!(f, "¬({})", phi)
                }
            }
            ModalFormula::And(phi, psi) => {
                write!(f, "({} ∧ {})", phi, psi)
            }
            ModalFormula::Or(phi, psi) => {
                write!(f, "({} ∨ {})", phi, psi)
            }
            ModalFormula::Implies(phi, psi) => {
                write!(f, "({} → {})", phi, psi)
            }
            ModalFormula::Iff(phi, psi) => {
                write!(f, "({} ↔ {})", phi, psi)
            }
            ModalFormula::Necessity(phi) => {
                write!(f, "□{}", phi)
            }
            ModalFormula::Possibility(phi) => {
                write!(f, "◇{}", phi)
            }
        }
    }
}
```

### 3.2 解析器实现

```rust
pub struct ModalParser {
    tokens: Vec<ModalToken>,
    position: usize,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ModalToken {
    Atom(String),
    Not,
    And,
    Or,
    Implies,
    Iff,
    Necessity,
    Possibility,
    LeftParen,
    RightParen,
    End,
}

impl ModalParser {
    pub fn new(input: &str) -> Self {
        let tokens = Self::tokenize(input);
        Self { tokens, position: 0 }
    }

    pub fn parse(&mut self) -> Result<ModalFormula, String> {
        let formula = self.parse_implication()?;
        self.expect_token(ModalToken::End)?;
        Ok(formula)
    }

    fn parse_implication(&mut self) -> Result<ModalFormula, String> {
        let mut left = self.parse_equivalence()?;
        
        while self.check_token(&ModalToken::Implies) {
            self.advance();
            let right = self.parse_equivalence()?;
            left = ModalFormula::implies(left, right);
        }
        
        Ok(left)
    }

    fn parse_equivalence(&mut self) -> Result<ModalFormula, String> {
        let mut left = self.parse_or()?;
        
        while self.check_token(&ModalToken::Iff) {
            self.advance();
            let right = self.parse_or()?;
            left = ModalFormula::iff(left, right);
        }
        
        Ok(left)
    }

    fn parse_or(&mut self) -> Result<ModalFormula, String> {
        let mut left = self.parse_and()?;
        
        while self.check_token(&ModalToken::Or) {
            self.advance();
            let right = self.parse_and()?;
            left = ModalFormula::or(left, right);
        }
        
        Ok(left)
    }

    fn parse_and(&mut self) -> Result<ModalFormula, String> {
        let mut left = self.parse_modal()?;
        
        while self.check_token(&ModalToken::And) {
            self.advance();
            let right = self.parse_modal()?;
            left = ModalFormula::and(left, right);
        }
        
        Ok(left)
    }

    fn parse_modal(&mut self) -> Result<ModalFormula, String> {
        if self.check_token(&ModalToken::Necessity) {
            self.advance();
            let formula = self.parse_modal()?;
            Ok(ModalFormula::necessity(formula))
        } else if self.check_token(&ModalToken::Possibility) {
            self.advance();
            let formula = self.parse_modal()?;
            Ok(ModalFormula::possibility(formula))
        } else {
            self.parse_not()
        }
    }

    fn parse_not(&mut self) -> Result<ModalFormula, String> {
        if self.check_token(&ModalToken::Not) {
            self.advance();
            let formula = self.parse_not()?;
            Ok(ModalFormula::not(formula))
        } else {
            self.parse_primary()
        }
    }

    fn parse_primary(&mut self) -> Result<ModalFormula, String> {
        match self.current_token() {
            ModalToken::Atom(name) => {
                self.advance();
                Ok(ModalFormula::atom(name))
            }
            ModalToken::LeftParen => {
                self.advance();
                let formula = self.parse_implication()?;
                self.expect_token(ModalToken::RightParen)?;
                Ok(formula)
            }
            _ => Err(format!("Unexpected token: {:?}", self.current_token())),
        }
    }

    fn tokenize(input: &str) -> Vec<ModalToken> {
        let mut tokens = Vec::new();
        let mut chars = input.chars().peekable();
        
        while let Some(ch) = chars.next() {
            match ch {
                ' ' | '\t' | '\n' => continue,
                '¬' | '~' => tokens.push(ModalToken::Not),
                '∧' | '&' => tokens.push(ModalToken::And),
                '∨' | '|' => tokens.push(ModalToken::Or),
                '→' | '>' => tokens.push(ModalToken::Implies),
                '↔' | '=' => tokens.push(ModalToken::Iff),
                '□' => tokens.push(ModalToken::Necessity),
                '◇' => tokens.push(ModalToken::Possibility),
                '(' => tokens.push(ModalToken::LeftParen),
                ')' => tokens.push(ModalToken::RightParen),
                'a'..='z' | 'A'..='Z' => {
                    let mut name = String::new();
                    name.push(ch);
                    while let Some(&next_ch) = chars.peek() {
                        if next_ch.is_alphanumeric() || next_ch == '_' {
                            name.push(chars.next().unwrap());
                        } else {
                            break;
                        }
                    }
                    tokens.push(ModalToken::Atom(name));
                }
                _ => {
                    // 忽略未知字符
                }
            }
        }
        
        tokens.push(ModalToken::End);
        tokens
    }

    fn current_token(&self) -> &ModalToken {
        &self.tokens[self.position]
    }

    fn check_token(&self, token: &ModalToken) -> bool {
        self.position < self.tokens.len() && self.current_token() == token
    }

    fn advance(&mut self) {
        self.position += 1;
    }

    fn expect_token(&mut self, token: ModalToken) -> Result<(), String> {
        if self.check_token(&token) {
            self.advance();
            Ok(())
        } else {
            Err(format!("Expected {:?}, got {:?}", token, self.current_token()))
        }
    }
}
```

## 4 语义实现

### 4.1 克里普克模型

```rust
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct KripkeModel {
    pub worlds: Vec<String>,
    pub accessibility: Vec<(String, String)>,
    pub valuation: HashMap<(String, String), bool>,
}

impl KripkeModel {
    pub fn new(worlds: Vec<String>) -> Self {
        Self {
            worlds,
            accessibility: Vec::new(),
            valuation: HashMap::new(),
        }
    }

    pub fn add_accessibility(&mut self, from: String, to: String) {
        self.accessibility.push((from, to));
    }

    pub fn set_valuation(&mut self, world: String, proposition: String, value: bool) {
        self.valuation.insert((world, proposition), value);
    }

    pub fn get_accessible_worlds(&self, world: &str) -> Vec<String> {
        self.accessibility.iter()
            .filter(|(w1, _)| w1 == world)
            .map(|(_, w2)| w2.clone())
            .collect()
    }

    pub fn is_reflexive(&self) -> bool {
        self.worlds.iter().all(|world| {
            self.accessibility.contains(&(world.clone(), world.clone()))
        })
    }

    pub fn is_symmetric(&self) -> bool {
        self.accessibility.iter().all(|(w1, w2)| {
            self.accessibility.contains(&(w2.clone(), w1.clone()))
        })
    }

    pub fn is_transitive(&self) -> bool {
        self.accessibility.iter().all(|(w1, w2)| {
            self.get_accessible_worlds(w2).iter().all(|w3| {
                self.accessibility.contains(&(w1.clone(), w3.clone()))
            })
        })
    }

    pub fn is_serial(&self) -> bool {
        self.worlds.iter().all(|world| {
            !self.get_accessible_worlds(world).is_empty()
        })
    }

    pub fn is_euclidean(&self) -> bool {
        self.accessibility.iter().all(|(w1, w2)| {
            self.get_accessible_worlds(w1).iter().all(|w3| {
                self.accessibility.contains(&(w2.clone(), w3.clone()))
            })
        })
    }
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
            ModalFormula::Iff(phi, psi) => {
                Self::evaluate(phi, model, world) == Self::evaluate(psi, model, world)
            }
            ModalFormula::Necessity(phi) => {
                let accessible_worlds = model.get_accessible_worlds(world);
                accessible_worlds.iter().all(|w| Self::evaluate(phi, model, w))
            }
            ModalFormula::Possibility(phi) => {
                let accessible_worlds = model.get_accessible_worlds(world);
                accessible_worlds.iter().any(|w| Self::evaluate(phi, model, w))
            }
        }
    }

    pub fn is_valid_in_model(formula: &ModalFormula, model: &KripkeModel) -> bool {
        model.worlds.iter().all(|world| Self::evaluate(formula, model, world))
    }

    pub fn is_satisfiable_in_model(formula: &ModalFormula, model: &KripkeModel) -> bool {
        model.worlds.iter().any(|world| Self::evaluate(formula, model, world))
    }

    pub fn is_valid_in_frame_class(formula: &ModalFormula, frame_property: FrameProperty) -> bool {
        // 简化的框架类有效性检查
        // 实际实现需要检查所有满足给定性质的框架
        true
    }

    pub fn is_satisfiable_in_frame_class(formula: &ModalFormula, frame_property: FrameProperty) -> bool {
        // 简化的框架类可满足性检查
        true
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum FrameProperty {
    Reflexive,
    Symmetric,
    Transitive,
    Serial,
    Euclidean,
    Equivalence, // 等价关系（自反、对称、传递）
    Preorder,    // 预序关系（自反、传递）
    PartialOrder, // 偏序关系（自反、反对称、传递）
}
```

### 4.2 模态系统

```rust
pub struct ModalSystem {
    pub name: String,
    pub axioms: Vec<ModalFormula>,
    pub rules: Vec<InferenceRule>,
}

#[derive(Debug, Clone)]
pub enum InferenceRule {
    ModusPonens,
    Necessitation,
    Substitution,
    UniformSubstitution,
}

impl ModalSystem {
    pub fn system_k() -> Self {
        Self {
            name: "K".to_string(),
            axioms: vec![
                // K公理：□(φ → ψ) → (□φ → □ψ)
                ModalFormula::implies(
                    ModalFormula::necessity(ModalFormula::implies(
                        ModalFormula::atom("p"),
                        ModalFormula::atom("q"),
                    )),
                    ModalFormula::implies(
                        ModalFormula::necessity(ModalFormula::atom("p")),
                        ModalFormula::necessity(ModalFormula::atom("q")),
                    ),
                ),
            ],
            rules: vec![
                InferenceRule::ModusPonens,
                InferenceRule::Necessitation,
                InferenceRule::Substitution,
            ],
        }
    }

    pub fn system_t() -> Self {
        let mut t = Self::system_k();
        t.name = "T".to_string();
        t.axioms.push(
            // T公理：□φ → φ
            ModalFormula::implies(
                ModalFormula::necessity(ModalFormula::atom("p")),
                ModalFormula::atom("p"),
            ),
        );
        t
    }

    pub fn system_s4() -> Self {
        let mut s4 = Self::system_t();
        s4.name = "S4".to_string();
        s4.axioms.push(
            // 4公理：□φ → □□φ
            ModalFormula::implies(
                ModalFormula::necessity(ModalFormula::atom("p")),
                ModalFormula::necessity(ModalFormula::necessity(ModalFormula::atom("p"))),
            ),
        );
        s4
    }

    pub fn system_s5() -> Self {
        let mut s5 = Self::system_s4();
        s5.name = "S5".to_string();
        s5.axioms.push(
            // 5公理：◇φ → □◇φ
            ModalFormula::implies(
                ModalFormula::possibility(ModalFormula::atom("p")),
                ModalFormula::necessity(ModalFormula::possibility(ModalFormula::atom("p"))),
            ),
        );
        s5
    }

    pub fn system_b() -> Self {
        let mut b = Self::system_t();
        b.name = "B".to_string();
        b.axioms.push(
            // B公理：φ → □◇φ
            ModalFormula::implies(
                ModalFormula::atom("p"),
                ModalFormula::necessity(ModalFormula::possibility(ModalFormula::atom("p"))),
            ),
        );
        b
    }

    pub fn system_d() -> Self {
        let mut d = Self::system_k();
        d.name = "D".to_string();
        d.axioms.push(
            // D公理：□φ → ◇φ
            ModalFormula::implies(
                ModalFormula::necessity(ModalFormula::atom("p")),
                ModalFormula::possibility(ModalFormula::atom("p")),
            ),
        );
        d
    }
}

pub struct ModalProof {
    pub system: ModalSystem,
    pub premises: Vec<ModalFormula>,
    pub conclusion: ModalFormula,
    pub steps: Vec<ModalProofStep>,
}

#[derive(Debug, Clone)]
pub struct ModalProofStep {
    pub formula: ModalFormula,
    pub rule: ModalInferenceRule,
    pub dependencies: Vec<usize>,
}

#[derive(Debug, Clone)]
pub enum ModalInferenceRule {
    Axiom(ModalFormula),
    Assumption(ModalFormula),
    ModusPonens(usize, usize),
    Necessitation(usize),
    Substitution(usize, HashMap<String, ModalFormula>),
}

pub struct ModalProofSystem;

impl ModalProofSystem {
    pub fn prove_necessity_distribution(
        phi: ModalFormula,
        psi: ModalFormula,
    ) -> ModalProof {
        let mut proof = ModalProof {
            system: ModalSystem::system_k(),
            premises: vec![
                ModalFormula::implies(phi.clone(), psi.clone()),
            ],
            conclusion: ModalFormula::implies(
                ModalFormula::necessity(phi.clone()),
                ModalFormula::necessity(psi.clone()),
            ),
            steps: Vec::new(),
        };

        // 添加前提
        proof.steps.push(ModalProofStep {
            formula: ModalFormula::implies(phi.clone(), psi.clone()),
            rule: ModalInferenceRule::Assumption(ModalFormula::implies(phi.clone(), psi.clone())),
            dependencies: vec![0],
        });

        // 应用必然化规则
        proof.steps.push(ModalProofStep {
            formula: ModalFormula::necessity(ModalFormula::implies(phi.clone(), psi.clone())),
            rule: ModalInferenceRule::Necessitation(0),
            dependencies: vec![0],
        });

        // 应用K公理
        let k_axiom = ModalFormula::implies(
            ModalFormula::necessity(ModalFormula::implies(phi.clone(), psi.clone())),
            ModalFormula::implies(
                ModalFormula::necessity(phi.clone()),
                ModalFormula::necessity(psi.clone()),
            ),
        );
        proof.steps.push(ModalProofStep {
            formula: k_axiom.clone(),
            rule: ModalInferenceRule::Axiom(k_axiom),
            dependencies: vec![],
        });

        // 应用分离规则
        proof.steps.push(ModalProofStep {
            formula: ModalFormula::implies(
                ModalFormula::necessity(phi),
                ModalFormula::necessity(psi),
            ),
            rule: ModalInferenceRule::ModusPonens(1, 2),
            dependencies: vec![1, 2],
        });

        proof
    }

    pub fn prove_duality(formula: &ModalFormula) -> ModalProof {
        let dual = ModalFormula::dual(formula);
        let mut proof = ModalProof {
            system: ModalSystem::system_k(),
            premises: vec![formula.clone()],
            conclusion: dual.clone(),
            steps: Vec::new(),
        };

        // 添加前提
        proof.steps.push(ModalProofStep {
            formula: formula.clone(),
            rule: ModalInferenceRule::Assumption(formula.clone()),
            dependencies: vec![0],
        });

        // 证明对偶性
        match formula {
            ModalFormula::Necessity(phi) => {
                // □φ ≡ ¬◇¬φ
                let not_phi = ModalFormula::not(*phi.clone());
                let not_poss_not = ModalFormula::not(ModalFormula::possibility(not_phi));
                
                proof.steps.push(ModalProofStep {
                    formula: not_poss_not,
                    rule: ModalInferenceRule::Axiom(not_poss_not.clone()),
                    dependencies: vec![],
                });
            }
            ModalFormula::Possibility(phi) => {
                // ◇φ ≡ ¬□¬φ
                let not_phi = ModalFormula::not(*phi.clone());
                let not_nec_not = ModalFormula::not(ModalFormula::necessity(not_phi));
                
                proof.steps.push(ModalProofStep {
                    formula: not_nec_not,
                    rule: ModalInferenceRule::Axiom(not_nec_not.clone()),
                    dependencies: vec![],
                });
            }
            _ => {
                // 非模态公式，对偶性不适用
                proof.steps.push(ModalProofStep {
                    formula: formula.clone(),
                    rule: ModalInferenceRule::Axiom(formula.clone()),
                    dependencies: vec![],
                });
            }
        }

        proof
    }
}
```

## 5 形式化验证

### 5.1 框架对应性

**定理 10.3.1 (框架对应性)** 模态公式与框架性质之间的对应关系：

1. **T公理** $\Box \phi \rightarrow \phi$ 对应自反性
2. **4公理** $\Box \phi \rightarrow \Box \Box \phi$ 对应传递性
3. **B公理** $\phi \rightarrow \Box \Diamond \phi$ 对应对称性
4. **5公理** $\Diamond \phi \rightarrow \Box \Diamond \phi$ 对应欧几里得性
5. **D公理** $\Box \phi \rightarrow \Diamond \phi$ 对应序列性

**证明** 通过模型论方法，证明公式在满足特定性质的框架上有效。

### 5.2 完备性定理

**定理 10.3.2 (模态逻辑完备性)** 对于模态系统S和框架类F：
$$\vdash_S \phi \Leftrightarrow \models_F \phi$$

**证明** 通过典范模型构造和模型论方法。

### 5.3 紧致性定理

**定理 10.3.3 (模态紧致性)** 模态理论 $\Gamma$ 是可满足的当且仅当 $\Gamma$ 的每个有限子集都是可满足的。

**证明** 通过超积构造和模型论方法。

## 6 应用领域

### 6.1 认知逻辑

```rust
pub struct EpistemicLogic {
    pub agents: Vec<String>,
    pub knowledge_operators: HashMap<String, ModalFormula>,
}

impl EpistemicLogic {
    pub fn new(agents: Vec<String>) -> Self {
        Self {
            agents,
            knowledge_operators: HashMap::new(),
        }
    }

    pub fn knows(&self, agent: &str, formula: ModalFormula) -> ModalFormula {
        ModalFormula::necessity(formula)
    }

    pub fn common_knowledge(&self, formula: ModalFormula) -> ModalFormula {
        // 共同知识：所有智能体都知道，所有智能体都知道所有智能体都知道...
        let mut result = formula.clone();
        for agent in &self.agents {
            result = self.knows(agent, result);
        }
        result
    }

    pub fn distributed_knowledge(&self, formula: ModalFormula) -> ModalFormula {
        // 分布式知识：智能体联合起来知道
        ModalFormula::possibility(formula)
    }
}
```

### 6.2 时态逻辑

```rust
pub struct TemporalLogic {
    pub time_points: Vec<String>,
    pub temporal_operators: HashMap<String, ModalFormula>,
}

impl TemporalLogic {
    pub fn new(time_points: Vec<String>) -> Self {
        Self {
            time_points,
            temporal_operators: HashMap::new(),
        }
    }

    pub fn always(&self, formula: ModalFormula) -> ModalFormula {
        ModalFormula::necessity(formula)
    }

    pub fn eventually(&self, formula: ModalFormula) -> ModalFormula {
        ModalFormula::possibility(formula)
    }

    pub fn next(&self, formula: ModalFormula) -> ModalFormula {
        // 下一个时刻
        ModalFormula::possibility(formula)
    }

    pub fn until(&self, phi: ModalFormula, psi: ModalFormula) -> ModalFormula {
        // φ直到ψ
        ModalFormula::and(
            phi.clone(),
            ModalFormula::possibility(psi),
        )
    }
}
```

### 6.3 道义逻辑

```rust
pub struct DeonticLogic {
    pub obligations: HashMap<String, ModalFormula>,
    pub permissions: HashMap<String, ModalFormula>,
}

impl DeonticLogic {
    pub fn new() -> Self {
        Self {
            obligations: HashMap::new(),
            permissions: HashMap::new(),
        }
    }

    pub fn obligatory(&self, formula: ModalFormula) -> ModalFormula {
        ModalFormula::necessity(formula)
    }

    pub fn permitted(&self, formula: ModalFormula) -> ModalFormula {
        ModalFormula::possibility(formula)
    }

    pub fn forbidden(&self, formula: ModalFormula) -> ModalFormula {
        ModalFormula::not(ModalFormula::possibility(formula))
    }
}
```

## 7 总结

模态逻辑为必然性和可能性概念提供了严格的数学基础。通过可能世界语义、克里普克模型和各种模态系统，模态逻辑能够处理复杂的哲学和计算机科学问题。本文档提供的实现为计算机辅助逻辑推理和形式化验证提供了实用工具。

## 参考文献

1. Blackburn, P., de Rijke, M., & Venema, Y. (2001). Modal Logic.
2. Hughes, G. E., & Cresswell, M. J. (1996). A New Introduction to Modal Logic.
3. Chellas, B. F. (1980). Modal Logic: An Introduction.

## 8 相关链接

- [逻辑理论主文档](README.md)
- [命题逻辑](README.md)
- [谓词逻辑](README.md)

## 9 批判性分析

- 多元理论视角：
  - 哲学—数学—计算：从必然/可能的形而上学语义，到 Kripke 可达关系的模型论，再到验证/类型系统/程序逻辑中的工程语义。
  - 系统化族群：K, T, S4, S5, KD, KD45 等通过帧条件刻画知识/信念/义务等不同语义域。
- 局限性分析：
  - 语义选择敏感：帧条件变化导致推理差异，跨场景迁移需谨慎；高表达力系统的判定/复杂度成本高。
  - 与时态/概率/动态扩展耦合后，工具与教材生态分裂，互操作难。
- 争议与分歧：
  - 直觉主义/模态/动态/描述逻辑的边界与互译；常需通过翻译到一阶/μ-演算来统一。
- 应用前景：
  - 知识/信念/义务/能动的规范化建模，在安全、协议、合规与多智能体推理中持续增长。
- 改进建议：
  - 语义对照表：维持系统族与帧条件、可达性公设、完备性关系的对照与证据。
  - 组合指引：与时态/概率/动态逻辑的组合基线与可判定边界说明。
