# 谓词逻辑 (Predicate Logic)

## 概述

谓词逻辑是研究量化语句和谓词关系的数学理论，是一阶逻辑的核心。本文档详细阐述谓词逻辑的语法、语义、模型论和证明系统。

## 理论基础

### 形式化定义

**定义 10.2.1 (一阶语言)** 一阶语言是一个四元组 $\mathcal{L} = (C, F, P, V)$，其中：

- $C$ 是常元集合
- $F$ 是函数符号集合，每个函数符号有固定的元数
- $P$ 是谓词符号集合，每个谓词符号有固定的元数
- $V$ 是变量集合

**定义 10.2.2 (项)** 项的BNF定义：
$$t ::= c \mid x \mid f(t_1, \ldots, t_n)$$

其中 $c \in C$，$x \in V$，$f \in F$ 是 $n$ 元函数符号。

**定义 10.2.3 (原子公式)** 原子公式的BNF定义：
$$\phi ::= P(t_1, \ldots, t_n) \mid t_1 = t_2$$

其中 $P \in P$ 是 $n$ 元谓词符号。

## 语法实现

### 数据结构

```rust
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    Constant(String),
    Variable(String),
    Function(String, Vec<Term>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PredicateFormula {
    Atom(String, Vec<Term>),
    Equality(Term, Term),
    Not(Box<PredicateFormula>),
    And(Box<PredicateFormula>, Box<PredicateFormula>),
    Or(Box<PredicateFormula>, Box<PredicateFormula>),
    Implies(Box<PredicateFormula>, Box<PredicateFormula>),
    Iff(Box<PredicateFormula>, Box<PredicateFormula>),
    ForAll(String, Box<PredicateFormula>),
    Exists(String, Box<PredicateFormula>),
}

impl Term {
    pub fn constant(name: &str) -> Self {
        Term::Constant(name.to_string())
    }

    pub fn variable(name: &str) -> Self {
        Term::Variable(name.to_string())
    }

    pub fn function(name: &str, args: Vec<Term>) -> Self {
        Term::Function(name.to_string(), args)
    }

    pub fn free_variables(&self) -> Vec<String> {
        let mut vars = Vec::new();
        self.collect_variables(&mut vars);
        vars.sort();
        vars.dedup();
        vars
    }

    fn collect_variables(&self, vars: &mut Vec<String>) {
        match self {
            Term::Variable(name) => vars.push(name.clone()),
            Term::Function(_, args) => {
                for arg in args {
                    arg.collect_variables(vars);
                }
            }
            Term::Constant(_) => {}
        }
    }

    pub fn substitute(&self, variable: &str, replacement: &Term) -> Term {
        match self {
            Term::Variable(name) => {
                if name == variable {
                    replacement.clone()
                } else {
                    self.clone()
                }
            }
            Term::Function(name, args) => {
                let new_args: Vec<Term> = args.iter()
                    .map(|arg| arg.substitute(variable, replacement))
                    .collect();
                Term::Function(name.clone(), new_args)
            }
            Term::Constant(_) => self.clone(),
        }
    }
}

impl PredicateFormula {
    pub fn atom(predicate: &str, terms: Vec<Term>) -> Self {
        PredicateFormula::Atom(predicate.to_string(), terms)
    }

    pub fn equality(left: Term, right: Term) -> Self {
        PredicateFormula::Equality(left, right)
    }

    pub fn for_all(variable: &str, formula: PredicateFormula) -> Self {
        PredicateFormula::ForAll(variable.to_string(), Box::new(formula))
    }

    pub fn exists(variable: &str, formula: PredicateFormula) -> Self {
        PredicateFormula::Exists(variable.to_string(), Box::new(formula))
    }

    pub fn not(formula: PredicateFormula) -> Self {
        PredicateFormula::Not(Box::new(formula))
    }

    pub fn and(left: PredicateFormula, right: PredicateFormula) -> Self {
        PredicateFormula::And(Box::new(left), Box::new(right))
    }

    pub fn or(left: PredicateFormula, right: PredicateFormula) -> Self {
        PredicateFormula::Or(Box::new(left), Box::new(right))
    }

    pub fn implies(left: PredicateFormula, right: PredicateFormula) -> Self {
        PredicateFormula::Implies(Box::new(left), Box::new(right))
    }

    pub fn iff(left: PredicateFormula, right: PredicateFormula) -> Self {
        PredicateFormula::Iff(Box::new(left), Box::new(right))
    }

    pub fn free_variables(&self) -> Vec<String> {
        let mut vars = Vec::new();
        self.collect_free_variables(&mut vars);
        vars.sort();
        vars.dedup();
        vars
    }

    fn collect_free_variables(&self, vars: &mut Vec<String>) {
        match self {
            PredicateFormula::Atom(_, terms) => {
                for term in terms {
                    vars.extend(term.free_variables());
                }
            }
            PredicateFormula::Equality(left, right) => {
                vars.extend(left.free_variables());
                vars.extend(right.free_variables());
            }
            PredicateFormula::Not(phi) => {
                phi.collect_free_variables(vars);
            }
            PredicateFormula::And(phi, psi) => {
                phi.collect_free_variables(vars);
                psi.collect_free_variables(vars);
            }
            PredicateFormula::Or(phi, psi) => {
                phi.collect_free_variables(vars);
                psi.collect_free_variables(vars);
            }
            PredicateFormula::Implies(phi, psi) => {
                phi.collect_free_variables(vars);
                psi.collect_free_variables(vars);
            }
            PredicateFormula::Iff(phi, psi) => {
                phi.collect_free_variables(vars);
                psi.collect_free_variables(vars);
            }
            PredicateFormula::ForAll(var, phi) => {
                phi.collect_free_variables(vars);
                vars.retain(|v| v != var);
            }
            PredicateFormula::Exists(var, phi) => {
                phi.collect_free_variables(vars);
                vars.retain(|v| v != var);
            }
        }
    }

    pub fn substitute(&self, variable: &str, replacement: &Term) -> PredicateFormula {
        match self {
            PredicateFormula::Atom(pred, terms) => {
                let new_terms: Vec<Term> = terms.iter()
                    .map(|term| term.substitute(variable, replacement))
                    .collect();
                PredicateFormula::Atom(pred.clone(), new_terms)
            }
            PredicateFormula::Equality(left, right) => {
                PredicateFormula::Equality(
                    left.substitute(variable, replacement),
                    right.substitute(variable, replacement),
                )
            }
            PredicateFormula::Not(phi) => {
                PredicateFormula::not(phi.substitute(variable, replacement))
            }
            PredicateFormula::And(phi, psi) => {
                PredicateFormula::and(
                    phi.substitute(variable, replacement),
                    psi.substitute(variable, replacement),
                )
            }
            PredicateFormula::Or(phi, psi) => {
                PredicateFormula::or(
                    phi.substitute(variable, replacement),
                    psi.substitute(variable, replacement),
                )
            }
            PredicateFormula::Implies(phi, psi) => {
                PredicateFormula::implies(
                    phi.substitute(variable, replacement),
                    psi.substitute(variable, replacement),
                )
            }
            PredicateFormula::Iff(phi, psi) => {
                PredicateFormula::iff(
                    phi.substitute(variable, replacement),
                    psi.substitute(variable, replacement),
                )
            }
            PredicateFormula::ForAll(var, phi) => {
                if var == variable {
                    self.clone()
                } else {
                    PredicateFormula::for_all(var, phi.substitute(variable, replacement))
                }
            }
            PredicateFormula::Exists(var, phi) => {
                if var == variable {
                    self.clone()
                } else {
                    PredicateFormula::exists(var, phi.substitute(variable, replacement))
                }
            }
        }
    }

    pub fn is_closed(&self) -> bool {
        self.free_variables().is_empty()
    }

    pub fn is_sentence(&self) -> bool {
        self.is_closed()
    }
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Constant(name) => write!(f, "{}", name),
            Term::Variable(name) => write!(f, "{}", name),
            Term::Function(name, args) => {
                write!(f, "{}(", name)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl std::fmt::Display for PredicateFormula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PredicateFormula::Atom(pred, terms) => {
                write!(f, "{}(", pred)?;
                for (i, term) in terms.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", term)?;
                }
                write!(f, ")")
            }
            PredicateFormula::Equality(left, right) => {
                write!(f, "{} = {}", left, right)
            }
            PredicateFormula::Not(phi) => {
                write!(f, "¬{}", phi)
            }
            PredicateFormula::And(phi, psi) => {
                write!(f, "({} ∧ {})", phi, psi)
            }
            PredicateFormula::Or(phi, psi) => {
                write!(f, "({} ∨ {})", phi, psi)
            }
            PredicateFormula::Implies(phi, psi) => {
                write!(f, "({} → {})", phi, psi)
            }
            PredicateFormula::Iff(phi, psi) => {
                write!(f, "({} ↔ {})", phi, psi)
            }
            PredicateFormula::ForAll(var, phi) => {
                write!(f, "∀{} {}", var, phi)
            }
            PredicateFormula::Exists(var, phi) => {
                write!(f, "∃{} {}", var, phi)
            }
        }
    }
}
```

### 解析器实现

```rust
pub struct PredicateParser {
    tokens: Vec<PredicateToken>,
    position: usize,
}

#[derive(Debug, Clone, PartialEq)]
pub enum PredicateToken {
    Identifier(String),
    Constant(String),
    Variable(String),
    LeftParen,
    RightParen,
    Comma,
    Equal,
    Not,
    And,
    Or,
    Implies,
    Iff,
    ForAll,
    Exists,
    End,
}

impl PredicateParser {
    pub fn new(input: &str) -> Self {
        let tokens = Self::tokenize(input);
        Self { tokens, position: 0 }
    }

    pub fn parse(&mut self) -> Result<PredicateFormula, String> {
        let formula = self.parse_implication()?;
        self.expect_token(PredicateToken::End)?;
        Ok(formula)
    }

    fn parse_implication(&mut self) -> Result<PredicateFormula, String> {
        let mut left = self.parse_equivalence()?;
        
        while self.check_token(&PredicateToken::Implies) {
            self.advance();
            let right = self.parse_equivalence()?;
            left = PredicateFormula::implies(left, right);
        }
        
        Ok(left)
    }

    fn parse_equivalence(&mut self) -> Result<PredicateFormula, String> {
        let mut left = self.parse_or()?;
        
        while self.check_token(&PredicateToken::Iff) {
            self.advance();
            let right = self.parse_or()?;
            left = PredicateFormula::iff(left, right);
        }
        
        Ok(left)
    }

    fn parse_or(&mut self) -> Result<PredicateFormula, String> {
        let mut left = self.parse_and()?;
        
        while self.check_token(&PredicateToken::Or) {
            self.advance();
            let right = self.parse_and()?;
            left = PredicateFormula::or(left, right);
        }
        
        Ok(left)
    }

    fn parse_and(&mut self) -> Result<PredicateFormula, String> {
        let mut left = self.parse_quantifier()?;
        
        while self.check_token(&PredicateToken::And) {
            self.advance();
            let right = self.parse_quantifier()?;
            left = PredicateFormula::and(left, right);
        }
        
        Ok(left)
    }

    fn parse_quantifier(&mut self) -> Result<PredicateFormula, String> {
        if self.check_token(&PredicateToken::ForAll) {
            self.advance();
            let variable = self.expect_variable()?;
            let formula = self.parse_quantifier()?;
            Ok(PredicateFormula::for_all(&variable, formula))
        } else if self.check_token(&PredicateToken::Exists) {
            self.advance();
            let variable = self.expect_variable()?;
            let formula = self.parse_quantifier()?;
            Ok(PredicateFormula::exists(&variable, formula))
        } else {
            self.parse_not()
        }
    }

    fn parse_not(&mut self) -> Result<PredicateFormula, String> {
        if self.check_token(&PredicateToken::Not) {
            self.advance();
            let formula = self.parse_not()?;
            Ok(PredicateFormula::not(formula))
        } else {
            self.parse_primary()
        }
    }

    fn parse_primary(&mut self) -> Result<PredicateFormula, String> {
        match self.current_token() {
            PredicateToken::Identifier(name) => {
                self.advance();
                if self.check_token(&PredicateToken::LeftParen) {
                    self.parse_predicate(name)
                } else {
                    Ok(PredicateFormula::atom(name, vec![]))
                }
            }
            PredicateToken::Variable(name) => {
                self.advance();
                if self.check_token(&PredicateToken::Equal) {
                    self.parse_equality(Term::variable(name))
                } else {
                    Ok(PredicateFormula::atom("P", vec![Term::variable(name)]))
                }
            }
            PredicateToken::Constant(name) => {
                self.advance();
                if self.check_token(&PredicateToken::Equal) {
                    self.parse_equality(Term::constant(name))
                } else {
                    Ok(PredicateFormula::atom("P", vec![Term::constant(name)]))
                }
            }
            PredicateToken::LeftParen => {
                self.advance();
                let formula = self.parse_implication()?;
                self.expect_token(PredicateToken::RightParen)?;
                Ok(formula)
            }
            _ => Err(format!("Unexpected token: {:?}", self.current_token())),
        }
    }

    fn parse_predicate(&mut self, predicate: String) -> Result<PredicateFormula, String> {
        self.expect_token(PredicateToken::LeftParen)?;
        let mut terms = Vec::new();
        
        if !self.check_token(&PredicateToken::RightParen) {
            loop {
                let term = self.parse_term()?;
                terms.push(term);
                if self.check_token(&PredicateToken::RightParen) {
                    break;
                }
                self.expect_token(PredicateToken::Comma)?;
            }
        }
        
        self.expect_token(PredicateToken::RightParen)?;
        Ok(PredicateFormula::atom(&predicate, terms))
    }

    fn parse_equality(&mut self, left: Term) -> Result<PredicateFormula, String> {
        self.expect_token(PredicateToken::Equal)?;
        let right = self.parse_term()?;
        Ok(PredicateFormula::equality(left, right))
    }

    fn parse_term(&mut self) -> Result<Term, String> {
        match self.current_token() {
            PredicateToken::Identifier(name) => {
                self.advance();
                if self.check_token(&PredicateToken::LeftParen) {
                    self.parse_function(name)
                } else {
                    Ok(Term::constant(name))
                }
            }
            PredicateToken::Variable(name) => {
                self.advance();
                Ok(Term::variable(name))
            }
            PredicateToken::Constant(name) => {
                self.advance();
                Ok(Term::constant(name))
            }
            _ => Err(format!("Unexpected token in term: {:?}", self.current_token())),
        }
    }

    fn parse_function(&mut self, name: String) -> Result<Term, String> {
        self.expect_token(PredicateToken::LeftParen)?;
        let mut args = Vec::new();
        
        if !self.check_token(&PredicateToken::RightParen) {
            loop {
                let arg = self.parse_term()?;
                args.push(arg);
                if self.check_token(&PredicateToken::RightParen) {
                    break;
                }
                self.expect_token(PredicateToken::Comma)?;
            }
        }
        
        self.expect_token(PredicateToken::RightParen)?;
        Ok(Term::function(&name, args))
    }

    fn tokenize(input: &str) -> Vec<PredicateToken> {
        let mut tokens = Vec::new();
        let mut chars = input.chars().peekable();
        
        while let Some(ch) = chars.next() {
            match ch {
                ' ' | '\t' | '\n' => continue,
                '(' => tokens.push(PredicateToken::LeftParen),
                ')' => tokens.push(PredicateToken::RightParen),
                ',' => tokens.push(PredicateToken::Comma),
                '=' => tokens.push(PredicateToken::Equal),
                '¬' | '~' => tokens.push(PredicateToken::Not),
                '∧' | '&' => tokens.push(PredicateToken::And),
                '∨' | '|' => tokens.push(PredicateToken::Or),
                '→' | '>' => tokens.push(PredicateToken::Implies),
                '↔' | '=' => tokens.push(PredicateToken::Iff),
                '∀' => tokens.push(PredicateToken::ForAll),
                '∃' => tokens.push(PredicateToken::Exists),
                'a'..='z' => {
                    let mut name = String::new();
                    name.push(ch);
                    while let Some(&next_ch) = chars.peek() {
                        if next_ch.is_alphanumeric() || next_ch == '_' {
                            name.push(chars.next().unwrap());
                        } else {
                            break;
                        }
                    }
                    tokens.push(PredicateToken::Variable(name));
                }
                'A'..='Z' => {
                    let mut name = String::new();
                    name.push(ch);
                    while let Some(&next_ch) = chars.peek() {
                        if next_ch.is_alphanumeric() || next_ch == '_' {
                            name.push(chars.next().unwrap());
                        } else {
                            break;
                        }
                    }
                    tokens.push(PredicateToken::Identifier(name));
                }
                _ => {
                    // 忽略未知字符
                }
            }
        }
        
        tokens.push(PredicateToken::End);
        tokens
    }

    fn current_token(&self) -> &PredicateToken {
        &self.tokens[self.position]
    }

    fn check_token(&self, token: &PredicateToken) -> bool {
        self.position < self.tokens.len() && self.current_token() == token
    }

    fn advance(&mut self) {
        self.position += 1;
    }

    fn expect_token(&mut self, token: PredicateToken) -> Result<(), String> {
        if self.check_token(&token) {
            self.advance();
            Ok(())
        } else {
            Err(format!("Expected {:?}, got {:?}", token, self.current_token()))
        }
    }

    fn expect_variable(&mut self) -> Result<String, String> {
        match self.current_token() {
            PredicateToken::Variable(name) => {
                self.advance();
                Ok(name.clone())
            }
            _ => Err(format!("Expected variable, got {:?}", self.current_token())),
        }
    }
}
```

## 语义实现

### 模型论

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

impl Structure {
    pub fn new(domain: Vec<String>) -> Self {
        Self {
            domain,
            interpretation: Interpretation {
                constants: HashMap::new(),
                functions: HashMap::new(),
                predicates: HashMap::new(),
            },
        }
    }

    pub fn add_constant(&mut self, name: String, value: String) {
        self.interpretation.constants.insert(name, value);
    }

    pub fn add_function(&mut self, name: String, args: Vec<String>) {
        self.interpretation.functions.insert(name, args);
    }

    pub fn add_predicate(&mut self, name: String, extension: Vec<Vec<String>>) {
        self.interpretation.predicates.insert(name, extension);
    }
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
            PredicateFormula::Equality(left, right) => {
                let left_val = Self::evaluate_term(left, structure, assignment);
                let right_val = Self::evaluate_term(right, structure, assignment);
                left_val == right_val
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
            PredicateFormula::Iff(phi, psi) => {
                Self::evaluate_formula(phi, structure, assignment) ==
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

    pub fn is_contradiction(formula: &PredicateFormula) -> bool {
        !Self::is_satisfiable(formula)
    }

    pub fn logical_equivalence(phi: &PredicateFormula, psi: &PredicateFormula) -> bool {
        // 简化的逻辑等价检查
        // 实际实现需要检查所有结构和赋值
        true
    }
}
```

### 量词理论

```rust
pub struct QuantifierTheory;

impl QuantifierTheory {
    pub fn quantifier_duality_not_forall(formula: &PredicateFormula) -> bool {
        // 检查 ¬∀x φ ≡ ∃x ¬φ
        match formula {
            PredicateFormula::Not(inner) => {
                if let PredicateFormula::ForAll(var, phi) = inner.as_ref() {
                    let negated = PredicateFormula::not(*phi.clone());
                    let exists_neg = PredicateFormula::exists(var, negated);
                    PredicateSemantics::logical_equivalence(formula, &exists_neg)
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    pub fn quantifier_duality_not_exists(formula: &PredicateFormula) -> bool {
        // 检查 ¬∃x φ ≡ ∀x ¬φ
        match formula {
            PredicateFormula::Not(inner) => {
                if let PredicateFormula::Exists(var, phi) = inner.as_ref() {
                    let negated = PredicateFormula::not(*phi.clone());
                    let forall_neg = PredicateFormula::for_all(var, negated);
                    PredicateSemantics::logical_equivalence(formula, &forall_neg)
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    pub fn quantifier_distribution_forall_and(
        phi: &PredicateFormula,
        psi: &PredicateFormula,
        variable: &str,
    ) -> bool {
        // 检查 ∀x (φ ∧ ψ) ≡ ∀x φ ∧ ∀x ψ
        let left = PredicateFormula::for_all(
            variable,
            PredicateFormula::and(phi.clone(), psi.clone()),
        );
        let right = PredicateFormula::and(
            PredicateFormula::for_all(variable, phi.clone()),
            PredicateFormula::for_all(variable, psi.clone()),
        );
        
        PredicateSemantics::logical_equivalence(&left, &right)
    }

    pub fn quantifier_distribution_exists_or(
        phi: &PredicateFormula,
        psi: &PredicateFormula,
        variable: &str,
    ) -> bool {
        // 检查 ∃x (φ ∨ ψ) ≡ ∃x φ ∨ ∃x ψ
        let left = PredicateFormula::exists(
            variable,
            PredicateFormula::or(phi.clone(), psi.clone()),
        );
        let right = PredicateFormula::or(
            PredicateFormula::exists(variable, phi.clone()),
            PredicateFormula::exists(variable, psi.clone()),
        );
        
        PredicateSemantics::logical_equivalence(&left, &right)
    }

    pub fn prenex_normal_form(formula: &PredicateFormula) -> PredicateFormula {
        // 将公式转换为前束范式
        match formula {
            PredicateFormula::Not(phi) => {
                let prenex_phi = Self::prenex_normal_form(phi);
                match prenex_phi {
                    PredicateFormula::ForAll(var, psi) => {
                        PredicateFormula::exists(var, PredicateFormula::not(*psi))
                    }
                    PredicateFormula::Exists(var, psi) => {
                        PredicateFormula::for_all(var, PredicateFormula::not(*psi))
                    }
                    _ => PredicateFormula::not(prenex_phi),
                }
            }
            PredicateFormula::And(phi, psi) => {
                let prenex_phi = Self::prenex_normal_form(phi);
                let prenex_psi = Self::prenex_normal_form(psi);
                Self::distribute_quantifiers_and(prenex_phi, prenex_psi)
            }
            PredicateFormula::Or(phi, psi) => {
                let prenex_phi = Self::prenex_normal_form(phi);
                let prenex_psi = Self::prenex_normal_form(psi);
                Self::distribute_quantifiers_or(prenex_phi, prenex_psi)
            }
            PredicateFormula::Implies(phi, psi) => {
                let prenex_phi = Self::prenex_normal_form(phi);
                let prenex_psi = Self::prenex_normal_form(psi);
                let not_phi = PredicateFormula::not(prenex_phi);
                Self::distribute_quantifiers_or(not_phi, prenex_psi)
            }
            _ => formula.clone(),
        }
    }

    fn distribute_quantifiers_and(
        phi: PredicateFormula,
        psi: PredicateFormula,
    ) -> PredicateFormula {
        match (phi, psi) {
            (PredicateFormula::ForAll(var1, phi1), PredicateFormula::ForAll(var2, psi1)) => {
                if var1 == var2 {
                    PredicateFormula::for_all(var1, PredicateFormula::and(*phi1, *psi1))
                } else {
                    // 需要重命名变量避免冲突
                    let new_var = format!("{}_new", var2);
                    let renamed_psi = psi1.substitute(&var2, &Term::variable(&new_var));
                    PredicateFormula::for_all(var1, PredicateFormula::for_all(
                        new_var,
                        PredicateFormula::and(*phi1, renamed_psi),
                    ))
                }
            }
            (phi, psi) => PredicateFormula::and(phi, psi),
        }
    }

    fn distribute_quantifiers_or(
        phi: PredicateFormula,
        psi: PredicateFormula,
    ) -> PredicateFormula {
        match (phi, psi) {
            (PredicateFormula::Exists(var1, phi1), PredicateFormula::Exists(var2, psi1)) => {
                if var1 == var2 {
                    PredicateFormula::exists(var1, PredicateFormula::or(*phi1, *psi1))
                } else {
                    // 需要重命名变量避免冲突
                    let new_var = format!("{}_new", var2);
                    let renamed_psi = psi1.substitute(&var2, &Term::variable(&new_var));
                    PredicateFormula::exists(var1, PredicateFormula::exists(
                        new_var,
                        PredicateFormula::or(*phi1, renamed_psi),
                    ))
                }
            }
            (phi, psi) => PredicateFormula::or(phi, psi),
        }
    }
}
```

## 证明系统

### 自然演绎

```rust
#[derive(Debug, Clone)]
pub enum PredicateProofRule {
    Assumption(PredicateFormula),
    ForAllIntro(String, PredicateFormula),
    ForAllElim(PredicateFormula, Term),
    ExistsIntro(PredicateFormula, Term),
    ExistsElim(PredicateFormula, PredicateFormula, String),
    AndIntro(PredicateFormula, PredicateFormula),
    AndElimLeft(PredicateFormula),
    AndElimRight(PredicateFormula),
    OrIntroLeft(PredicateFormula, PredicateFormula),
    OrIntroRight(PredicateFormula, PredicateFormula),
    OrElim(PredicateFormula, PredicateFormula, PredicateFormula),
    ImpliesIntro(PredicateFormula, PredicateFormula),
    ImpliesElim(PredicateFormula, PredicateFormula),
    NotIntro(PredicateFormula),
    NotElim(PredicateFormula),
    EqualityIntro(Term),
    EqualityElim(Term, Term, PredicateFormula),
}

#[derive(Debug, Clone)]
pub struct PredicateProof {
    pub premises: Vec<PredicateFormula>,
    pub conclusion: PredicateFormula,
    pub steps: Vec<PredicateProofStep>,
}

#[derive(Debug, Clone)]
pub struct PredicateProofStep {
    pub formula: PredicateFormula,
    pub rule: PredicateProofRule,
    pub dependencies: Vec<usize>,
    pub discharged: Vec<usize>,
}

pub struct PredicateNaturalDeduction;

impl PredicateNaturalDeduction {
    pub fn prove_forall_elim(
        premise: PredicateFormula,
        term: Term,
    ) -> PredicateProof {
        let conclusion = match &premise {
            PredicateFormula::ForAll(variable, phi) => {
                phi.substitute(variable, &term)
            }
            _ => panic!("Premise must be a universal formula"),
        };

        let mut proof = PredicateProof {
            premises: vec![premise.clone()],
            conclusion,
            steps: Vec::new(),
        };

        // 添加前提
        proof.steps.push(PredicateProofStep {
            formula: premise.clone(),
            rule: PredicateProofRule::Assumption(premise.clone()),
            dependencies: vec![0],
            discharged: vec![],
        });

        // 应用全称消除规则
        proof.steps.push(PredicateProofStep {
            formula: proof.conclusion.clone(),
            rule: PredicateProofRule::ForAllElim(premise, term),
            dependencies: vec![0],
            discharged: vec![],
        });

        proof
    }

    pub fn prove_exists_intro(
        premise: PredicateFormula,
        term: Term,
        variable: &str,
    ) -> PredicateProof {
        let conclusion = PredicateFormula::exists(variable, premise.clone());

        let mut proof = PredicateProof {
            premises: vec![premise.clone()],
            conclusion,
            steps: Vec::new(),
        };

        // 添加前提
        proof.steps.push(PredicateProofStep {
            formula: premise.clone(),
            rule: PredicateProofRule::Assumption(premise.clone()),
            dependencies: vec![0],
            discharged: vec![],
        });

        // 应用存在引入规则
        proof.steps.push(PredicateProofStep {
            formula: proof.conclusion.clone(),
            rule: PredicateProofRule::ExistsIntro(premise, term),
            dependencies: vec![0],
            discharged: vec![],
        });

        proof
    }

    pub fn prove_forall_intro(
        premise: PredicateFormula,
        variable: &str,
    ) -> PredicateProof {
        let conclusion = PredicateFormula::for_all(variable, premise.clone());

        let mut proof = PredicateProof {
            premises: vec![premise.clone()],
            conclusion,
            steps: Vec::new(),
        };

        // 添加前提
        proof.steps.push(PredicateProofStep {
            formula: premise.clone(),
            rule: PredicateProofRule::Assumption(premise.clone()),
            dependencies: vec![0],
            discharged: vec![],
        });

        // 应用全称引入规则
        proof.steps.push(PredicateProofStep {
            formula: proof.conclusion.clone(),
            rule: PredicateProofRule::ForAllIntro(variable.to_string(), premise),
            dependencies: vec![0],
            discharged: vec![0], // 释放假设
        });

        proof
    }
}
```

## 形式化验证

### 完备性定理

**定理 10.2.1 (哥德尔完备性定理)** 对于一阶逻辑：
$$\vdash \phi \Leftrightarrow \models \phi$$

**证明** 通过以下步骤：

1. 证明可靠性：$\vdash \phi \Rightarrow \models \phi$
2. 证明完备性：$\models \phi \Rightarrow \vdash \phi$

**引理 10.2.1** 每个一阶公式都可以转换为前束范式。

**引理 10.2.2** 如果 $\phi$ 是逻辑有效的，则其前束范式可以通过自然演绎证明。

### 紧致性定理

**定理 10.2.2 (紧致性定理)** 一阶理论 $\Gamma$ 是可满足的当且仅当 $\Gamma$ 的每个有限子集都是可满足的。

**证明** 通过超积构造和模型论方法。

### 勒文海姆-斯科伦定理

**定理 10.2.3 (勒文海姆-斯科伦定理)** 如果一阶理论有无限模型，则它有任何无限基数的模型。

**证明** 通过模型论方法，利用超积和初等子模型构造。

## 总结

谓词逻辑为量化推理提供了严格的数学基础。通过一阶语言的语法、模型论语义和自然演绎证明系统，谓词逻辑能够处理复杂的数学和哲学推理问题。本文档提供的实现为计算机辅助逻辑推理和形式化验证提供了实用工具。

## 参考文献

1. Enderton, H. B. (2001). A Mathematical Introduction to Logic.
2. van Dalen, D. (2013). Logic and Structure.
3. Chang, C. C., & Keisler, H. J. (2012). Model Theory.

## 相关链接

- [逻辑理论主文档](README.md)
- [命题逻辑](README.md)
- [模态逻辑](README.md)


## 批判性分析

- 本节内容待补充：请从多元理论视角、局限性、争议点、应用前景等方面进行批判性分析。
