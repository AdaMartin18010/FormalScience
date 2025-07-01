# 语义理论 (Semantics Theory)

## 概述

语义理论研究编程语言的形式化语义，为程序行为提供精确的数学描述。本文档系统化阐述操作语义、指称语义和公理语义三大语义学方法。

## 理论基础

### 形式化定义

**定义 9.4.1 (语义函数)** 语义函数是一个映射 $\llbracket \cdot \rrbracket: Prog \rightarrow D$，其中：

- $Prog$ 是程序集合
- $D$ 是语义域
- $\llbracket P \rrbracket$ 表示程序 $P$ 的语义

**定义 9.4.2 (语义等价)** 两个程序 $P_1$ 和 $P_2$ 语义等价当且仅当：
$$\llbracket P_1 \rrbracket = \llbracket P_2 \rrbracket$$

## 操作语义 (Operational Semantics)

### 小步语义 (Small-Step Semantics)

**定义 9.4.3 (小步语义)** 小步语义是一个关系 $\rightarrow \subseteq Conf \times Conf$，其中：

- $Conf$ 是配置集合
- 配置是程序状态和环境的对偶

**定理 9.4.1 (确定性)** 如果 $\rightarrow$ 是确定性的，则：
$$\forall c, c_1, c_2: c \rightarrow c_1 \land c \rightarrow c_2 \Rightarrow c_1 = c_2$$

```rust
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(i64),
    Bool(bool),
    String(String),
    Closure {
        params: Vec<String>,
        body: Box<Expr>,
        env: Environment,
    },
}

#[derive(Debug, Clone)]
pub struct Environment {
    bindings: HashMap<String, Value>,
    parent: Option<Box<Environment>>,
}

impl Environment {
    pub fn new() -> Self {
        Self {
            bindings: HashMap::new(),
            parent: None,
        }
    }

    pub fn extend(&self, bindings: HashMap<String, Value>) -> Self {
        Self {
            bindings,
            parent: Some(Box::new(self.clone())),
        }
    }

    pub fn get(&self, name: &str) -> Option<Value> {
        self.bindings.get(name).cloned().or_else(|| {
            self.parent.as_ref().and_then(|p| p.get(name))
        })
    }

    pub fn set(&mut self, name: String, value: Value) {
        self.bindings.insert(name, value);
    }
}

#[derive(Debug, Clone)]
pub enum Expr {
    Literal(Value),
    Variable(String),
    BinaryOp {
        op: String,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    If {
        condition: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Box<Expr>,
    },
    Let {
        name: String,
        value: Box<Expr>,
        body: Box<Expr>,
    },
    Lambda {
        params: Vec<String>,
        body: Box<Expr>,
    },
    Apply {
        func: Box<Expr>,
        args: Vec<Expr>,
    },
}

pub struct SmallStepSemantics;

impl SmallStepSemantics {
    pub fn step(expr: &Expr, env: &Environment) -> Result<Option<(Expr, Environment)>, String> {
        match expr {
            Expr::Literal(_) => Ok(None), // 值无法继续求值
            Expr::Variable(name) => {
                match env.get(name) {
                    Some(value) => Ok(Some((Expr::Literal(value), env.clone()))),
                    None => Err(format!("Undefined variable: {}", name)),
                }
            }
            Expr::BinaryOp { op, left, right } => {
                match (left.as_ref(), right.as_ref()) {
                    (Expr::Literal(Value::Int(l)), Expr::Literal(Value::Int(r))) => {
                        let result = match op.as_str() {
                            "+" => Value::Int(l + r),
                            "-" => Value::Int(l - r),
                            "*" => Value::Int(l * r),
                            "/" => {
                                if *r == 0 {
                                    return Err("Division by zero".to_string());
                                }
                                Value::Int(l / r)
                            }
                            "==" => Value::Bool(l == r),
                            "!=" => Value::Bool(l != r),
                            "<" => Value::Bool(l < r),
                            ">" => Value::Bool(l > r),
                            "<=" => Value::Bool(l <= r),
                            ">=" => Value::Bool(l >= r),
                            _ => return Err(format!("Unknown operator: {}", op)),
                        };
                        Ok(Some((Expr::Literal(result), env.clone())))
                    }
                    (Expr::Literal(Value::Bool(l)), Expr::Literal(Value::Bool(r))) => {
                        let result = match op.as_str() {
                            "&&" => Value::Bool(*l && *r),
                            "||" => Value::Bool(*l || *r),
                            _ => return Err(format!("Invalid boolean operator: {}", op)),
                        };
                        Ok(Some((Expr::Literal(result), env.clone())))
                    }
                    _ => {
                        // 先求值左操作数
                        if let Some((new_left, _)) = Self::step(left, env)? {
                            let new_expr = Expr::BinaryOp {
                                op: op.clone(),
                                left: Box::new(new_left),
                                right: right.clone(),
                            };
                            Ok(Some((new_expr, env.clone())))
                        } else {
                            // 再求值右操作数
                            if let Some((new_right, _)) = Self::step(right, env)? {
                                let new_expr = Expr::BinaryOp {
                                    op: op.clone(),
                                    left: left.clone(),
                                    right: Box::new(new_right),
                                };
                                Ok(Some((new_expr, env.clone())))
                            } else {
                                Ok(None)
                            }
                        }
                    }
                }
            }
            Expr::If { condition, then_branch, else_branch } => {
                match condition.as_ref() {
                    Expr::Literal(Value::Bool(true)) => {
                        Ok(Some((*then_branch.clone(), env.clone())))
                    }
                    Expr::Literal(Value::Bool(false)) => {
                        Ok(Some((*else_branch.clone(), env.clone())))
                    }
                    _ => {
                        if let Some((new_condition, _)) = Self::step(condition, env)? {
                            let new_expr = Expr::If {
                                condition: Box::new(new_condition),
                                then_branch: then_branch.clone(),
                                else_branch: else_branch.clone(),
                            };
                            Ok(Some((new_expr, env.clone())))
                        } else {
                            Ok(None)
                        }
                    }
                }
            }
            Expr::Let { name, value, body } => {
                match value.as_ref() {
                    Expr::Literal(val) => {
                        let mut new_env = env.clone();
                        new_env.set(name.clone(), val.clone());
                        Ok(Some((*body.clone(), new_env)))
                    }
                    _ => {
                        if let Some((new_value, _)) = Self::step(value, env)? {
                            let new_expr = Expr::Let {
                                name: name.clone(),
                                value: Box::new(new_value),
                                body: body.clone(),
                            };
                            Ok(Some((new_expr, env.clone())))
                        } else {
                            Ok(None)
                        }
                    }
                }
            }
            Expr::Lambda { params, body } => {
                let closure = Value::Closure {
                    params: params.clone(),
                    body: body.clone(),
                    env: env.clone(),
                };
                Ok(Some((Expr::Literal(closure), env.clone())))
            }
            Expr::Apply { func, args } => {
                match func.as_ref() {
                    Expr::Literal(Value::Closure { params, body, env: closure_env }) => {
                        if args.len() != params.len() {
                            return Err("Argument count mismatch".to_string());
                        }
                        
                        // 检查所有参数是否已求值
                        let mut evaluated_args = Vec::new();
                        let mut all_evaluated = true;
                        
                        for arg in args {
                            match arg {
                                Expr::Literal(val) => evaluated_args.push(val.clone()),
                                _ => {
                                    all_evaluated = false;
                                    break;
                                }
                            }
                        }
                        
                        if all_evaluated {
                            // 创建新的环境
                            let mut bindings = HashMap::new();
                            for (param, arg) in params.iter().zip(evaluated_args.iter()) {
                                bindings.insert(param.clone(), arg.clone());
                            }
                            let new_env = closure_env.extend(bindings);
                            Ok(Some((*body.clone(), new_env)))
                        } else {
                            // 求值参数
                            for (i, arg) in args.iter().enumerate() {
                                if let Some((new_arg, _)) = Self::step(arg, env)? {
                                    let mut new_args = args.clone();
                                    new_args[i] = new_arg;
                                    let new_expr = Expr::Apply {
                                        func: func.clone(),
                                        args: new_args,
                                    };
                                    return Ok(Some((new_expr, env.clone())));
                                }
                            }
                            Ok(None)
                        }
                    }
                    _ => {
                        if let Some((new_func, _)) = Self::step(func, env)? {
                            let new_expr = Expr::Apply {
                                func: Box::new(new_func),
                                args: args.clone(),
                            };
                            Ok(Some((new_expr, env.clone())))
                        } else {
                            Ok(None)
                        }
                    }
                }
            }
        }
    }

    pub fn evaluate(expr: &Expr, env: &Environment) -> Result<Value, String> {
        let mut current_expr = expr.clone();
        let mut current_env = env.clone();
        
        loop {
            match Self::step(&current_expr, &current_env)? {
                Some((new_expr, new_env)) => {
                    current_expr = new_expr;
                    current_env = new_env;
                }
                None => {
                    if let Expr::Literal(value) = current_expr {
                        return Ok(value);
                    } else {
                        return Err("Evaluation stuck".to_string());
                    }
                }
            }
        }
    }
}
```

### 大步语义 (Big-Step Semantics)

**定义 9.4.4 (大步语义)** 大步语义是一个关系 $\Downarrow \subseteq Conf \times Value$，直接描述配置到值的求值。

**定理 9.4.2 (大步小步等价)** 对于所有表达式 $e$ 和环境 $\rho$：
$$e, \rho \Downarrow v \Leftrightarrow e, \rho \rightarrow^* v$$

```rust
pub struct BigStepSemantics;

impl BigStepSemantics {
    pub fn evaluate(expr: &Expr, env: &Environment) -> Result<Value, String> {
        match expr {
            Expr::Literal(value) => Ok(value.clone()),
            Expr::Variable(name) => {
                env.get(name).ok_or_else(|| format!("Undefined variable: {}", name))
            }
            Expr::BinaryOp { op, left, right } => {
                let left_val = Self::evaluate(left, env)?;
                let right_val = Self::evaluate(right, env)?;
                
                match (left_val, right_val) {
                    (Value::Int(l), Value::Int(r)) => {
                        let result = match op.as_str() {
                            "+" => Value::Int(l + r),
                            "-" => Value::Int(l - r),
                            "*" => Value::Int(l * r),
                            "/" => {
                                if r == 0 {
                                    return Err("Division by zero".to_string());
                                }
                                Value::Int(l / r)
                            }
                            "==" => Value::Bool(l == r),
                            "!=" => Value::Bool(l != r),
                            "<" => Value::Bool(l < r),
                            ">" => Value::Bool(l > r),
                            "<=" => Value::Bool(l <= r),
                            ">=" => Value::Bool(l >= r),
                            _ => return Err(format!("Unknown operator: {}", op)),
                        };
                        Ok(result)
                    }
                    (Value::Bool(l), Value::Bool(r)) => {
                        let result = match op.as_str() {
                            "&&" => Value::Bool(l && r),
                            "||" => Value::Bool(l || r),
                            _ => return Err(format!("Invalid boolean operator: {}", op)),
                        };
                        Ok(result)
                    }
                    _ => Err("Type mismatch in binary operation".to_string()),
                }
            }
            Expr::If { condition, then_branch, else_branch } => {
                let condition_val = Self::evaluate(condition, env)?;
                match condition_val {
                    Value::Bool(true) => Self::evaluate(then_branch, env),
                    Value::Bool(false) => Self::evaluate(else_branch, env),
                    _ => Err("Condition must be boolean".to_string()),
                }
            }
            Expr::Let { name, value, body } => {
                let value_val = Self::evaluate(value, env)?;
                let mut new_env = env.clone();
                new_env.set(name.clone(), value_val);
                Self::evaluate(body, &new_env)
            }
            Expr::Lambda { params, body } => {
                let closure = Value::Closure {
                    params: params.clone(),
                    body: body.clone(),
                    env: env.clone(),
                };
                Ok(closure)
            }
            Expr::Apply { func, args } => {
                let func_val = Self::evaluate(func, env)?;
                match func_val {
                    Value::Closure { params, body, env: closure_env } => {
                        if args.len() != params.len() {
                            return Err("Argument count mismatch".to_string());
                        }
                        
                        let mut arg_vals = Vec::new();
                        for arg in args {
                            arg_vals.push(Self::evaluate(arg, env)?);
                        }
                        
                        let mut bindings = HashMap::new();
                        for (param, arg) in params.iter().zip(arg_vals.iter()) {
                            bindings.insert(param.clone(), arg.clone());
                        }
                        let new_env = closure_env.extend(bindings);
                        Self::evaluate(&body, &new_env)
                    }
                    _ => Err("Cannot apply non-function value".to_string()),
                }
            }
        }
    }
}
```

## 指称语义 (Denotational Semantics)

### 语义域理论

**定义 9.4.5 (语义域)** 语义域是一个完全偏序集 $(D, \sqsubseteq)$，其中：

- $\sqsubseteq$ 是偏序关系
- 每个有向集都有最小上界

**定义 9.4.6 (连续函数)** 函数 $f: D \rightarrow E$ 是连续的当且仅当：
$$\forall X \subseteq D: f(\bigsqcup X) = \bigsqcup \{f(x) | x \in X\}$$

```rust
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub enum SemanticValue {
    Bottom,
    Int(i64),
    Bool(bool),
    String(String),
    Function(Box<dyn Fn(SemanticValue) -> SemanticValue>),
    Tuple(Vec<SemanticValue>),
}

impl PartialOrd for SemanticValue {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (SemanticValue::Bottom, _) => Some(std::cmp::Ordering::Less),
            (_, SemanticValue::Bottom) => Some(std::cmp::Ordering::Greater),
            (SemanticValue::Int(a), SemanticValue::Int(b)) => a.partial_cmp(b),
            (SemanticValue::Bool(a), SemanticValue::Bool(b)) => a.partial_cmp(b),
            (SemanticValue::String(a), SemanticValue::String(b)) => a.partial_cmp(b),
            _ => None,
        }
    }
}

pub struct DenotationalSemantics;

impl DenotationalSemantics {
    pub fn meaning(expr: &Expr, env: &HashMap<String, SemanticValue>) -> SemanticValue {
        match expr {
            Expr::Literal(value) => Self::value_to_semantic(value),
            Expr::Variable(name) => {
                env.get(name).cloned().unwrap_or(SemanticValue::Bottom)
            }
            Expr::BinaryOp { op, left, right } => {
                let left_val = Self::meaning(left, env);
                let right_val = Self::meaning(right, env);
                Self::apply_binary_op(op, left_val, right_val)
            }
            Expr::If { condition, then_branch, else_branch } => {
                let condition_val = Self::meaning(condition, env);
                match condition_val {
                    SemanticValue::Bool(true) => Self::meaning(then_branch, env),
                    SemanticValue::Bool(false) => Self::meaning(else_branch, env),
                    _ => SemanticValue::Bottom,
                }
            }
            Expr::Let { name, value, body } => {
                let value_val = Self::meaning(value, env);
                let mut new_env = env.clone();
                new_env.insert(name.clone(), value_val);
                Self::meaning(body, &new_env)
            }
            Expr::Lambda { params, body } => {
                let env_clone = env.clone();
                let body_clone = body.clone();
                let params_clone = params.clone();
                
                let func = move |arg: SemanticValue| {
                    let mut new_env = env_clone.clone();
                    if params_clone.len() == 1 {
                        new_env.insert(params_clone[0].clone(), arg);
                    } else {
                        // 处理多参数情况
                        if let SemanticValue::Tuple(args) = arg {
                            for (param, arg_val) in params_clone.iter().zip(args.iter()) {
                                new_env.insert(param.clone(), arg_val.clone());
                            }
                        }
                    }
                    Self::meaning(&body_clone, &new_env)
                };
                
                SemanticValue::Function(Box::new(func))
            }
            Expr::Apply { func, args } => {
                let func_val = Self::meaning(func, env);
                match func_val {
                    SemanticValue::Function(f) => {
                        if args.len() == 1 {
                            let arg_val = Self::meaning(&args[0], env);
                            f(arg_val)
                        } else {
                            let arg_vals: Vec<SemanticValue> = args.iter()
                                .map(|arg| Self::meaning(arg, env))
                                .collect();
                            f(SemanticValue::Tuple(arg_vals))
                        }
                    }
                    _ => SemanticValue::Bottom,
                }
            }
        }
    }

    fn value_to_semantic(value: &Value) -> SemanticValue {
        match value {
            Value::Int(n) => SemanticValue::Int(*n),
            Value::Bool(b) => SemanticValue::Bool(*b),
            Value::String(s) => SemanticValue::String(s.clone()),
            Value::Closure { .. } => SemanticValue::Bottom, // 简化处理
        }
    }

    fn apply_binary_op(op: &str, left: SemanticValue, right: SemanticValue) -> SemanticValue {
        match (left, right) {
            (SemanticValue::Int(l), SemanticValue::Int(r)) => {
                match op {
                    "+" => SemanticValue::Int(l + r),
                    "-" => SemanticValue::Int(l - r),
                    "*" => SemanticValue::Int(l * r),
                    "/" => {
                        if r == 0 {
                            SemanticValue::Bottom
                        } else {
                            SemanticValue::Int(l / r)
                        }
                    }
                    "==" => SemanticValue::Bool(l == r),
                    "!=" => SemanticValue::Bool(l != r),
                    "<" => SemanticValue::Bool(l < r),
                    ">" => SemanticValue::Bool(l > r),
                    "<=" => SemanticValue::Bool(l <= r),
                    ">=" => SemanticValue::Bool(l >= r),
                    _ => SemanticValue::Bottom,
                }
            }
            (SemanticValue::Bool(l), SemanticValue::Bool(r)) => {
                match op {
                    "&&" => SemanticValue::Bool(l && r),
                    "||" => SemanticValue::Bool(l || r),
                    _ => SemanticValue::Bottom,
                }
            }
            _ => SemanticValue::Bottom,
        }
    }
}
```

## 公理语义 (Axiomatic Semantics)

### Hoare逻辑

**定义 9.4.7 (Hoare三元组)** Hoare三元组 $\{P\} C \{Q\}$ 表示：

- 如果前置条件 $P$ 在程序 $C$ 执行前成立
- 且 $C$ 终止
- 则后置条件 $Q$ 在 $C$ 执行后成立

**定理 9.4.3 (赋值公理)** 对于赋值语句 $x := e$：
$$\{P[e/x]\} x := e \{P\}$$

```rust
#[derive(Debug, Clone)]
pub struct HoareTriple {
    pub precondition: String,
    pub program: String,
    pub postcondition: String,
}

pub struct AxiomaticSemantics;

impl AxiomaticSemantics {
    pub fn assignment_axiom(variable: &str, expression: &str, postcondition: &str) -> HoareTriple {
        let precondition = Self::substitute(postcondition, variable, expression);
        HoareTriple {
            precondition,
            program: format!("{} := {}", variable, expression),
            postcondition: postcondition.to_string(),
        }
    }

    pub fn sequence_rule(triple1: &HoareTriple, triple2: &HoareTriple) -> HoareTriple {
        HoareTriple {
            precondition: triple1.precondition.clone(),
            program: format!("{}; {}", triple1.program, triple2.program),
            postcondition: triple2.postcondition.clone(),
        }
    }

    pub fn conditional_rule(
        condition: &str,
        then_triple: &HoareTriple,
        else_triple: &HoareTriple,
    ) -> HoareTriple {
        let precondition = format!("({} ∧ {}) ∨ (¬{} ∧ {})", 
            condition, then_triple.precondition, 
            condition, else_triple.precondition);
        
        HoareTriple {
            precondition,
            program: format!("if {} then {} else {} fi", 
                condition, then_triple.program, else_triple.program),
            postcondition: then_triple.postcondition.clone(),
        }
    }

    pub fn while_rule(condition: &str, invariant: &str, body_triple: &HoareTriple) -> HoareTriple {
        HoareTriple {
            precondition: invariant.to_string(),
            program: format!("while {} do {} od", condition, body_triple.program),
            postcondition: format!("{} ∧ ¬{}", invariant, condition),
        }
    }

    pub fn consequence_rule(
        triple: &HoareTriple,
        stronger_pre: &str,
        weaker_post: &str,
    ) -> HoareTriple {
        HoareTriple {
            precondition: stronger_pre.to_string(),
            program: triple.program.clone(),
            postcondition: weaker_post.to_string(),
        }
    }

    fn substitute(formula: &str, variable: &str, expression: &str) -> String {
        // 简化的替换实现
        formula.replace(&format!("{{{}}}", variable), expression)
    }
}

// 验证器实现
pub struct HoareVerifier;

impl HoareVerifier {
    pub fn verify_triple(triple: &HoareTriple) -> bool {
        // 简化的验证实现
        // 实际实现需要更复杂的逻辑推理
        true
    }

    pub fn verify_program(program: &str, precondition: &str, postcondition: &str) -> bool {
        // 程序验证的简化实现
        match program {
            "x := 5" => {
                precondition.contains("x") && postcondition.contains("x = 5")
            }
            "x := x + 1" => {
                precondition.contains("x") && postcondition.contains("x")
            }
            _ => true,
        }
    }
}
```

## 语义等价性

### 等价性证明

**定义 9.4.8 (语义等价)** 两个表达式 $e_1$ 和 $e_2$ 语义等价当且仅当：
$$\forall \rho: \llbracket e_1 \rrbracket \rho = \llbracket e_2 \rrbracket \rho$$

**定理 9.4.4 (β等价)** 对于λ表达式：
$$(\lambda x. e_1) e_2 \equiv e_1[e_2/x]$$

**定理 9.4.5 (η等价)** 对于λ表达式：
$$\lambda x. (e x) \equiv e \quad \text{if } x \notin FV(e)$$

```rust
pub struct SemanticEquivalence;

impl SemanticEquivalence {
    pub fn beta_equivalent(expr1: &Expr, expr2: &Expr) -> bool {
        // 检查β等价
        match (expr1, expr2) {
            (
                Expr::Apply {
                    func: Box::new(Expr::Lambda { params, body }),
                    args,
                },
                expected,
            ) => {
                if args.len() == params.len() {
                    let mut substitutions = HashMap::new();
                    for (param, arg) in params.iter().zip(args.iter()) {
                        if let Expr::Literal(value) = arg {
                            substitutions.insert(param.clone(), value.clone());
                        }
                    }
                    let substituted = Self::substitute(body, &substitutions);
                    Self::alpha_equivalent(&substituted, expected)
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    pub fn eta_equivalent(expr1: &Expr, expr2: &Expr) -> bool {
        // 检查η等价
        match (expr1, expr2) {
            (
                Expr::Lambda {
                    params: vec![param],
                    body: Box::new(Expr::Apply { func, args }),
                },
                expected,
            ) => {
                if args.len() == 1 && args[0] == Expr::Variable(param.clone()) {
                    Self::alpha_equivalent(func, expected)
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    fn substitute(expr: &Expr, substitutions: &HashMap<String, Value>) -> Expr {
        match expr {
            Expr::Variable(name) => {
                if let Some(value) = substitutions.get(name) {
                    Expr::Literal(value.clone())
                } else {
                    Expr::Variable(name.clone())
                }
            }
            Expr::BinaryOp { op, left, right } => {
                Expr::BinaryOp {
                    op: op.clone(),
                    left: Box::new(Self::substitute(left, substitutions)),
                    right: Box::new(Self::substitute(right, substitutions)),
                }
            }
            Expr::If { condition, then_branch, else_branch } => {
                Expr::If {
                    condition: Box::new(Self::substitute(condition, substitutions)),
                    then_branch: Box::new(Self::substitute(then_branch, substitutions)),
                    else_branch: Box::new(Self::substitute(else_branch, substitutions)),
                }
            }
            Expr::Let { name, value, body } => {
                Expr::Let {
                    name: name.clone(),
                    value: Box::new(Self::substitute(value, substitutions)),
                    body: Box::new(Self::substitute(body, substitutions)),
                }
            }
            Expr::Lambda { params, body } => {
                Expr::Lambda {
                    params: params.clone(),
                    body: Box::new(Self::substitute(body, substitutions)),
                }
            }
            Expr::Apply { func, args } => {
                Expr::Apply {
                    func: Box::new(Self::substitute(func, substitutions)),
                    args: args.iter().map(|arg| Self::substitute(arg, substitutions)).collect(),
                }
            }
            Expr::Literal(value) => Expr::Literal(value.clone()),
        }
    }

    fn alpha_equivalent(expr1: &Expr, expr2: &Expr) -> bool {
        // 简化的α等价检查
        format!("{:?}", expr1) == format!("{:?}", expr2)
    }
}
```

## 形式化验证

### 语义保持性证明

**引理 9.4.1** 对于所有表达式 $e$ 和环境 $\rho$：
$$\llbracket e \rrbracket \rho = \llbracket e \rrbracket \rho$$

**证明** 通过语义函数的定义直接得出。

**定理 9.4.6 (语义保持性)** 如果 $e_1 \rightarrow e_2$，则：
$$\llbracket e_1 \rrbracket = \llbracket e_2 \rrbracket$$

**证明** 通过结构归纳法证明每个求值规则保持语义。

## 总结

语义理论为编程语言提供了精确的数学基础。操作语义描述程序执行过程，指称语义提供抽象数学解释，公理语义支持程序验证。三种语义学方法相互补充，为语言设计和程序分析提供理论基础。

## 参考文献

1. Winskel, G. (1993). The Formal Semantics of Programming Languages.
2. Plotkin, G. D. (1981). A Structural Approach to Operational Semantics.
3. Hoare, C. A. R. (1969). An Axiomatic Basis for Computer Programming.

## 相关链接

- [语言设计理论](README.md)
- [类型系统理论](README.md)
- [编译理论](README.md)


## 批判性分析

- 本节内容待补充：请从多元理论视角、局限性、争议点、应用前景等方面进行批判性分析。
