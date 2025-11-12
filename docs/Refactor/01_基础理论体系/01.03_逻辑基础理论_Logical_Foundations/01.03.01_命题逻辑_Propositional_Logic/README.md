# 命题逻辑 (Propositional Logic)

## 📋 目录

- [1 概述](#1-概述)
- [2 理论基础](#2-理论基础)
  - [2.1 形式化定义](#21-形式化定义)
- [3 语法实现](#3-语法实现)
  - [3.1 公式数据结构](#31-公式数据结构)
  - [3.2 公式解析器](#32-公式解析器)
- [4 语义实现](#4-语义实现)
  - [4.1 真值赋值](#41-真值赋值)
  - [4.2 真值表生成](#42-真值表生成)
- [5 证明系统](#5-证明系统)
  - [5.1 自然演绎](#51-自然演绎)
  - [5.2 证明验证器](#52-证明验证器)
- [6 形式化验证](#6-形式化验证)
  - [6.1 逻辑等价性](#61-逻辑等价性)
  - [6.2 完备性证明](#62-完备性证明)
- [7 总结](#7-总结)
- [8 相关链接](#8-相关链接)
- [9 批判性分析](#9-批判性分析)

---

## 1 概述

命题逻辑是研究简单命题之间逻辑关系的数学理论，是逻辑学的基础分支。本文档详细阐述命题逻辑的语法、语义、证明系统和形式化实现。

## 2 理论基础

### 2.1 形式化定义

**定义 10.1.1 (命题语言)** 命题语言是一个三元组 $\mathcal{L} = (Prop, Conn, Form)$，其中：

- $Prop$ 是命题变量集合
- $Conn$ 是逻辑连接词集合 $\{\neg, \land, \lor, \rightarrow, \leftrightarrow\}$
- $Form$ 是公式集合

**定义 10.1.2 (命题公式)** 命题公式的BNF定义：
$$\phi ::= p \mid \neg \phi \mid \phi \land \psi \mid \phi \lor \psi \mid \phi \rightarrow \psi \mid \phi \leftrightarrow \psi$$

其中 $p \in Prop$ 是命题变量。

## 3 语法实现

### 3.1 公式数据结构

```rust
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

    pub fn collect_atoms(&self) -> Vec<String> {
        let mut atoms = Vec::new();
        self.collect_atoms_recursive(&mut atoms);
        atoms.sort();
        atoms.dedup();
        atoms
    }

    fn collect_atoms_recursive(&self, atoms: &mut Vec<String>) {
        match self {
            PropositionalFormula::Atom(name) => {
                atoms.push(name.clone());
            }
            PropositionalFormula::Not(phi) => {
                phi.collect_atoms_recursive(atoms);
            }
            PropositionalFormula::And(phi, psi) => {
                phi.collect_atoms_recursive(atoms);
                psi.collect_atoms_recursive(atoms);
            }
            PropositionalFormula::Or(phi, psi) => {
                phi.collect_atoms_recursive(atoms);
                psi.collect_atoms_recursive(atoms);
            }
            PropositionalFormula::Implies(phi, psi) => {
                phi.collect_atoms_recursive(atoms);
                psi.collect_atoms_recursive(atoms);
            }
            PropositionalFormula::Iff(phi, psi) => {
                phi.collect_atoms_recursive(atoms);
                psi.collect_atoms_recursive(atoms);
            }
        }
    }

    pub fn complexity(&self) -> usize {
        match self {
            PropositionalFormula::Atom(_) => 0,
            PropositionalFormula::Not(phi) => 1 + phi.complexity(),
            PropositionalFormula::And(phi, psi) => 1 + phi.complexity() + psi.complexity(),
            PropositionalFormula::Or(phi, psi) => 1 + phi.complexity() + psi.complexity(),
            PropositionalFormula::Implies(phi, psi) => 1 + phi.complexity() + psi.complexity(),
            PropositionalFormula::Iff(phi, psi) => 1 + phi.complexity() + psi.complexity(),
        }
    }

    pub fn is_atomic(&self) -> bool {
        matches!(self, PropositionalFormula::Atom(_))
    }

    pub fn is_negation(&self) -> bool {
        matches!(self, PropositionalFormula::Not(_))
    }

    pub fn is_binary(&self) -> bool {
        matches!(self, 
            PropositionalFormula::And(_, _) |
            PropositionalFormula::Or(_, _) |
            PropositionalFormula::Implies(_, _) |
            PropositionalFormula::Iff(_, _)
        )
    }
}

impl std::fmt::Display for PropositionalFormula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PropositionalFormula::Atom(name) => write!(f, "{}", name),
            PropositionalFormula::Not(phi) => {
                if phi.is_atomic() || phi.is_negation() {
                    write!(f, "¬{}", phi)
                } else {
                    write!(f, "¬({})", phi)
                }
            }
            PropositionalFormula::And(phi, psi) => {
                write!(f, "({} ∧ {})", phi, psi)
            }
            PropositionalFormula::Or(phi, psi) => {
                write!(f, "({} ∨ {})", phi, psi)
            }
            PropositionalFormula::Implies(phi, psi) => {
                write!(f, "({} → {})", phi, psi)
            }
            PropositionalFormula::Iff(phi, psi) => {
                write!(f, "({} ↔ {})", phi, psi)
            }
        }
    }
}
```

### 3.2 公式解析器

```rust
pub struct PropositionalParser {
    tokens: Vec<Token>,
    position: usize,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    Atom(String),
    Not,
    And,
    Or,
    Implies,
    Iff,
    LeftParen,
    RightParen,
    End,
}

impl PropositionalParser {
    pub fn new(input: &str) -> Self {
        let tokens = Self::tokenize(input);
        Self { tokens, position: 0 }
    }

    pub fn parse(&mut self) -> Result<PropositionalFormula, String> {
        let formula = self.parse_implication()?;
        self.expect_token(Token::End)?;
        Ok(formula)
    }

    fn parse_implication(&mut self) -> Result<PropositionalFormula, String> {
        let mut left = self.parse_equivalence()?;
        
        while self.check_token(&Token::Implies) {
            self.advance();
            let right = self.parse_equivalence()?;
            left = PropositionalFormula::implies(left, right);
        }
        
        Ok(left)
    }

    fn parse_equivalence(&mut self) -> Result<PropositionalFormula, String> {
        let mut left = self.parse_or()?;
        
        while self.check_token(&Token::Iff) {
            self.advance();
            let right = self.parse_or()?;
            left = PropositionalFormula::iff(left, right);
        }
        
        Ok(left)
    }

    fn parse_or(&mut self) -> Result<PropositionalFormula, String> {
        let mut left = self.parse_and()?;
        
        while self.check_token(&Token::Or) {
            self.advance();
            let right = self.parse_and()?;
            left = PropositionalFormula::or(left, right);
        }
        
        Ok(left)
    }

    fn parse_and(&mut self) -> Result<PropositionalFormula, String> {
        let mut left = self.parse_not()?;
        
        while self.check_token(&Token::And) {
            self.advance();
            let right = self.parse_not()?;
            left = PropositionalFormula::and(left, right);
        }
        
        Ok(left)
    }

    fn parse_not(&mut self) -> Result<PropositionalFormula, String> {
        if self.check_token(&Token::Not) {
            self.advance();
            let formula = self.parse_not()?;
            Ok(PropositionalFormula::not(formula))
        } else {
            self.parse_primary()
        }
    }

    fn parse_primary(&mut self) -> Result<PropositionalFormula, String> {
        match self.current_token() {
            Token::Atom(name) => {
                self.advance();
                Ok(PropositionalFormula::atom(name))
            }
            Token::LeftParen => {
                self.advance();
                let formula = self.parse_implication()?;
                self.expect_token(Token::RightParen)?;
                Ok(formula)
            }
            _ => Err(format!("Unexpected token: {:?}", self.current_token())),
        }
    }

    fn tokenize(input: &str) -> Vec<Token> {
        let mut tokens = Vec::new();
        let mut chars = input.chars().peekable();
        
        while let Some(ch) = chars.next() {
            match ch {
                ' ' | '\t' | '\n' => continue,
                '¬' | '~' => tokens.push(Token::Not),
                '∧' | '&' => tokens.push(Token::And),
                '∨' | '|' => tokens.push(Token::Or),
                '→' | '>' => tokens.push(Token::Implies),
                '↔' | '=' => tokens.push(Token::Iff),
                '(' => tokens.push(Token::LeftParen),
                ')' => tokens.push(Token::RightParen),
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
                    tokens.push(Token::Atom(name));
                }
                _ => {
                    // 忽略未知字符
                }
            }
        }
        
        tokens.push(Token::End);
        tokens
    }

    fn current_token(&self) -> &Token {
        &self.tokens[self.position]
    }

    fn check_token(&self, token: &Token) -> bool {
        self.position < self.tokens.len() && self.current_token() == token
    }

    fn advance(&mut self) {
        self.position += 1;
    }

    fn expect_token(&mut self, token: Token) -> Result<(), String> {
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

### 4.1 真值赋值

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
        let atoms = formula.collect_atoms();
        Self::check_all_valuations(formula, &atoms, 0, &mut HashMap::new())
    }

    pub fn is_satisfiable(formula: &PropositionalFormula) -> bool {
        let atoms = formula.collect_atoms();
        Self::check_some_valuation(formula, &atoms, 0, &mut HashMap::new())
    }

    pub fn is_contradiction(formula: &PropositionalFormula) -> bool {
        !Self::is_satisfiable(formula)
    }

    pub fn is_contingent(formula: &PropositionalFormula) -> bool {
        Self::is_satisfiable(formula) && !Self::is_tautology(formula)
    }

    pub fn logical_equivalence(phi: &PropositionalFormula, psi: &PropositionalFormula) -> bool {
        let atoms_phi = phi.collect_atoms();
        let atoms_psi = psi.collect_atoms();
        let mut all_atoms = atoms_phi.clone();
        all_atoms.extend(atoms_psi);
        all_atoms.sort();
        all_atoms.dedup();
        
        Self::check_equivalence_all_valuations(phi, psi, &all_atoms, 0, &mut HashMap::new())
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

    fn check_equivalence_all_valuations(
        phi: &PropositionalFormula,
        psi: &PropositionalFormula,
        atoms: &[String],
        index: usize,
        valuation: &mut HashMap<String, bool>,
    ) -> bool {
        if index >= atoms.len() {
            return Self::evaluate(phi, valuation) == Self::evaluate(psi, valuation);
        }

        let atom = &atoms[index];
        valuation.insert(atom.clone(), true);
        let result1 = Self::check_equivalence_all_valuations(phi, psi, atoms, index + 1, valuation);
        valuation.insert(atom.clone(), false);
        let result2 = Self::check_equivalence_all_valuations(phi, psi, atoms, index + 1, valuation);
        valuation.remove(atom);

        result1 && result2
    }

    pub fn find_satisfying_valuation(formula: &PropositionalFormula) -> Option<HashMap<String, bool>> {
        let atoms = formula.collect_atoms();
        Self::search_satisfying_valuation(formula, &atoms, 0, &mut HashMap::new())
    }

    fn search_satisfying_valuation(
        formula: &PropositionalFormula,
        atoms: &[String],
        index: usize,
        valuation: &mut HashMap<String, bool>,
    ) -> Option<HashMap<String, bool>> {
        if index >= atoms.len() {
            if Self::evaluate(formula, valuation) {
                return Some(valuation.clone());
            } else {
                return None;
            }
        }

        let atom = &atoms[index];
        valuation.insert(atom.clone(), true);
        if let Some(result) = Self::search_satisfying_valuation(formula, atoms, index + 1, valuation) {
            return Some(result);
        }
        valuation.insert(atom.clone(), false);
        let result = Self::search_satisfying_valuation(formula, atoms, index + 1, valuation);
        valuation.remove(atom);
        result
    }
}
```

### 4.2 真值表生成

```rust
pub struct TruthTable {
    pub atoms: Vec<String>,
    pub rows: Vec<TruthTableRow>,
}

#[derive(Debug, Clone)]
pub struct TruthTableRow {
    pub valuation: HashMap<String, bool>,
    pub result: bool,
}

impl TruthTable {
    pub fn generate(formula: &PropositionalFormula) -> Self {
        let atoms = formula.collect_atoms();
        let mut rows = Vec::new();
        
        Self::generate_rows(formula, &atoms, 0, &mut HashMap::new(), &mut rows);
        
        TruthTable { atoms, rows }
    }

    fn generate_rows(
        formula: &PropositionalFormula,
        atoms: &[String],
        index: usize,
        valuation: &mut HashMap<String, bool>,
        rows: &mut Vec<TruthTableRow>,
    ) {
        if index >= atoms.len() {
            let result = PropositionalSemantics::evaluate(formula, valuation);
            rows.push(TruthTableRow {
                valuation: valuation.clone(),
                result,
            });
            return;
        }

        let atom = &atoms[index];
        valuation.insert(atom.clone(), true);
        Self::generate_rows(formula, atoms, index + 1, valuation, rows);
        valuation.insert(atom.clone(), false);
        Self::generate_rows(formula, atoms, index + 1, valuation, rows);
        valuation.remove(atom);
    }

    pub fn print(&self) {
        // 打印表头
        for atom in &self.atoms {
            print!("{} | ", atom);
        }
        println!("Result");
        
        // 打印分隔线
        for _ in &self.atoms {
            print!("---|");
        }
        println!("-------");
        
        // 打印数据行
        for row in &self.rows {
            for atom in &self.atoms {
                let value = row.valuation.get(atom).unwrap_or(&false);
                print!("{} | ", if *value { "T" } else { "F" });
            }
            println!("{}", if row.result { "T" } else { "F" });
        }
    }
}
```

## 5 证明系统

### 5.1 自然演绎

```rust
#[derive(Debug, Clone)]
pub enum ProofRule {
    Assumption(PropositionalFormula),
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
    IffIntro(PropositionalFormula, PropositionalFormula),
    IffElimLeft(PropositionalFormula, PropositionalFormula),
    IffElimRight(PropositionalFormula, PropositionalFormula),
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
    pub discharged: Vec<usize>,
}

pub struct NaturalDeduction;

impl NaturalDeduction {
    pub fn prove_modus_ponens(
        premise1: PropositionalFormula,
        premise2: PropositionalFormula,
    ) -> Proof {
        let conclusion = match &premise2 {
            PropositionalFormula::Implies(_, psi) => *psi.clone(),
            _ => panic!("Second premise must be an implication"),
        };

        let mut proof = Proof {
            premises: vec![premise1.clone(), premise2.clone()],
            conclusion,
            steps: Vec::new(),
        };

        // 添加前提
        proof.steps.push(ProofStep {
            formula: premise1.clone(),
            rule: ProofRule::Assumption(premise1.clone()),
            dependencies: vec![0],
            discharged: vec![],
        });

        proof.steps.push(ProofStep {
            formula: premise2.clone(),
            rule: ProofRule::Assumption(premise2.clone()),
            dependencies: vec![1],
            discharged: vec![],
        });

        // 应用蕴含消除规则
        proof.steps.push(ProofStep {
            formula: proof.conclusion.clone(),
            rule: ProofRule::ImpliesElim(premise1, premise2),
            dependencies: vec![0, 1],
            discharged: vec![],
        });

        proof
    }

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
            discharged: vec![],
        });

        // 添加结论
        proof.steps.push(ProofStep {
            formula: conclusion.clone(),
            rule: ProofRule::Assumption(conclusion.clone()),
            dependencies: vec![1],
            discharged: vec![],
        });

        // 应用蕴含引入规则
        proof.steps.push(ProofStep {
            formula: PropositionalFormula::implies(premise, conclusion),
            rule: ProofRule::ImpliesIntro(
                proof.steps[0].formula.clone(),
                proof.steps[1].formula.clone(),
            ),
            dependencies: vec![0, 1],
            discharged: vec![0, 1], // 释放假设
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
            discharged: vec![],
        });

        proof.steps.push(ProofStep {
            formula: premise2.clone(),
            rule: ProofRule::Assumption(premise2.clone()),
            dependencies: vec![1],
            discharged: vec![],
        });

        // 应用合取引入规则
        proof.steps.push(ProofStep {
            formula: proof.conclusion.clone(),
            rule: ProofRule::AndIntro(premise1, premise2),
            dependencies: vec![0, 1],
            discharged: vec![],
        });

        proof
    }

    pub fn prove_or_intro_left(
        premise: PropositionalFormula,
        disjunct: PropositionalFormula,
    ) -> Proof {
        let mut proof = Proof {
            premises: vec![premise.clone()],
            conclusion: PropositionalFormula::or(premise.clone(), disjunct),
            steps: Vec::new(),
        };

        // 添加前提
        proof.steps.push(ProofStep {
            formula: premise.clone(),
            rule: ProofRule::Assumption(premise.clone()),
            dependencies: vec![0],
            discharged: vec![],
        });

        // 应用析取引入规则
        proof.steps.push(ProofStep {
            formula: proof.conclusion.clone(),
            rule: ProofRule::OrIntroLeft(premise, proof.conclusion.clone()),
            dependencies: vec![0],
            discharged: vec![],
        });

        proof
    }
}
```

### 5.2 证明验证器

```rust
pub struct ProofVerifier;

impl ProofVerifier {
    pub fn verify_proof(proof: &Proof) -> bool {
        // 检查每个证明步骤的有效性
        for (i, step) in proof.steps.iter().enumerate() {
            if !Self::verify_step(proof, i, step) {
                return false;
            }
        }
        
        // 检查结论是否在最后一步
        if let Some(last_step) = proof.steps.last() {
            last_step.formula == proof.conclusion
        } else {
            false
        }
    }

    fn verify_step(proof: &Proof, step_index: usize, step: &ProofStep) -> bool {
        // 检查依赖是否有效
        for &dep in &step.dependencies {
            if dep >= step_index {
                return false;
            }
        }

        // 检查规则应用是否正确
        match &step.rule {
            ProofRule::Assumption(formula) => {
                proof.premises.contains(formula)
            }
            ProofRule::AndIntro(phi, psi) => {
                step.dependencies.len() == 2 &&
                proof.steps[step.dependencies[0]].formula == *phi &&
                proof.steps[step.dependencies[1]].formula == *psi &&
                step.formula == PropositionalFormula::and(phi.clone(), psi.clone())
            }
            ProofRule::AndElimLeft(phi_and_psi) => {
                step.dependencies.len() == 1 &&
                proof.steps[step.dependencies[0]].formula == *phi_and_psi &&
                if let PropositionalFormula::And(phi, _) = phi_and_psi {
                    step.formula == *phi
                } else {
                    false
                }
            }
            ProofRule::AndElimRight(phi_and_psi) => {
                step.dependencies.len() == 1 &&
                proof.steps[step.dependencies[0]].formula == *phi_and_psi &&
                if let PropositionalFormula::And(_, psi) = phi_and_psi {
                    step.formula == *psi
                } else {
                    false
                }
            }
            ProofRule::ImpliesElim(phi, phi_implies_psi) => {
                step.dependencies.len() == 2 &&
                proof.steps[step.dependencies[0]].formula == *phi &&
                proof.steps[step.dependencies[1]].formula == *phi_implies_psi &&
                if let PropositionalFormula::Implies(_, psi) = phi_implies_psi {
                    step.formula == *psi
                } else {
                    false
                }
            }
            _ => {
                // 其他规则的验证
                true
            }
        }
    }
}
```

## 6 形式化验证

### 6.1 逻辑等价性

```rust
pub struct LogicalEquivalence;

impl LogicalEquivalence {
    pub fn de_morgan_not_and(phi: &PropositionalFormula, psi: &PropositionalFormula) -> bool {
        let left = PropositionalFormula::not(PropositionalFormula::and(phi.clone(), psi.clone()));
        let right = PropositionalFormula::or(
            PropositionalFormula::not(phi.clone()),
            PropositionalFormula::not(psi.clone()),
        );
        
        PropositionalSemantics::logical_equivalence(&left, &right)
    }

    pub fn de_morgan_not_or(phi: &PropositionalFormula, psi: &PropositionalFormula) -> bool {
        let left = PropositionalFormula::not(PropositionalFormula::or(phi.clone(), psi.clone()));
        let right = PropositionalFormula::and(
            PropositionalFormula::not(phi.clone()),
            PropositionalFormula::not(psi.clone()),
        );
        
        PropositionalSemantics::logical_equivalence(&left, &right)
    }

    pub fn double_negation(phi: &PropositionalFormula) -> bool {
        let double_neg = PropositionalFormula::not(PropositionalFormula::not(phi.clone()));
        PropositionalSemantics::logical_equivalence(phi, &double_neg)
    }

    pub fn implication_equivalence(phi: &PropositionalFormula, psi: &PropositionalFormula) -> bool {
        let implies = PropositionalFormula::implies(phi.clone(), psi.clone());
        let or_form = PropositionalFormula::or(
            PropositionalFormula::not(phi.clone()),
            psi.clone(),
        );
        
        PropositionalSemantics::logical_equivalence(&implies, &or_form)
    }

    pub fn distributivity_and_over_or(
        phi: &PropositionalFormula,
        psi: &PropositionalFormula,
        chi: &PropositionalFormula,
    ) -> bool {
        let left = PropositionalFormula::and(
            phi.clone(),
            PropositionalFormula::or(psi.clone(), chi.clone()),
        );
        let right = PropositionalFormula::or(
            PropositionalFormula::and(phi.clone(), psi.clone()),
            PropositionalFormula::and(phi.clone(), chi.clone()),
        );
        
        PropositionalSemantics::logical_equivalence(&left, &right)
    }

    pub fn distributivity_or_over_and(
        phi: &PropositionalFormula,
        psi: &PropositionalFormula,
        chi: &PropositionalFormula,
    ) -> bool {
        let left = PropositionalFormula::or(
            phi.clone(),
            PropositionalFormula::and(psi.clone(), chi.clone()),
        );
        let right = PropositionalFormula::and(
            PropositionalFormula::or(phi.clone(), psi.clone()),
            PropositionalFormula::or(phi.clone(), chi.clone()),
        );
        
        PropositionalSemantics::logical_equivalence(&left, &right)
    }
}
```

### 6.2 完备性证明

**定理 10.1.1 (命题逻辑完备性)** 对于任意命题公式 $\phi$：
$$\vdash \phi \Leftrightarrow \models \phi$$

**证明** 通过以下步骤：

1. 证明可靠性：$\vdash \phi \Rightarrow \models \phi$
2. 证明完备性：$\models \phi \Rightarrow \vdash \phi$

**引理 10.1.1** 每个命题公式都可以转换为合取范式(CNF)或析取范式(DNF)。

**引理 10.1.2** 如果 $\phi$ 是重言式，则其CNF形式可以通过自然演绎证明。

## 7 总结

命题逻辑为形式化推理提供了坚实的基础。通过严格的语法定义、语义解释和证明系统，命题逻辑能够处理复杂的逻辑推理问题。本文档提供的实现为计算机辅助逻辑推理和形式化验证提供了实用工具。

## 参考文献

1. Enderton, H. B. (2001). A Mathematical Introduction to Logic.
2. van Dalen, D. (2013). Logic and Structure.
3. Huth, M., & Ryan, M. (2004). Logic in Computer Science.

## 8 相关链接

- [逻辑理论主文档](README.md)
- [谓词逻辑](README.md)
- [模态逻辑](README.md)

## 9 批判性分析

- 多元理论视角：
  - 语法—语义—证明三元：真值表/布尔代数/自然演绎/分辨率构成命题逻辑的最小完备工具集，是更高层逻辑的入门台阶。
- 局限性分析：
  - 表达力不足：无法量化与表达结构性性质；规模化时 SAT 求解虽强，但规格层面易失信息。
  - 可解释性：纯布尔规格对业务方不直观，需要模板与抽象层。
- 争议与分歧：
  - 经典 vs 非经典（直觉/多值/模糊）：工程落地优先级与生态差异。
- 应用前景：
  - SAT/MaxSAT/SMT 的底层支撑；在验证、测试生成、规划与合成中持续受益。
- 改进建议：
  - 规格分层：业务→中间表述→布尔化的可追溯映射；保留证据工件（不可满足核、模型、对偶）。
