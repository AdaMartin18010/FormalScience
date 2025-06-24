# 01. 简单类型λ演算 (Simply Typed Lambda Calculus)

## 目录

1. [基本概念](#基本概念)
2. [类型系统](#类型系统)
3. [类型推导](#类型推导)
4. [类型安全](#类型安全)
5. [形式化表示](#形式化表示)
6. [证明系统](#证明系统)
7. [与其他学科的关联](#与其他学科的关联)

## 基本概念

### 1.1 类型定义

**定义 1.1.1 (类型)**
简单类型由以下规则定义：

```latex
τ ::= α | τ → τ
```

其中：

- α 是基本类型
- τ → τ 是函数类型

### 1.2 项定义

**定义 1.1.2 (项)**
λ项由以下规则定义：

```latex
t ::= x | λx:τ.t | t t
```

其中：

- x 是变量
- λx:τ.t 是抽象（函数定义）
- t t 是应用（函数调用）

### 1.3 上下文

**定义 1.1.3 (上下文)**
上下文是类型假设的有限序列：

```latex
Γ ::= ∅ | Γ, x:τ
```

## 类型系统

### 2.1 类型推导规则

**公理 (变量)：**

```latex
Γ, x:τ ⊢ x : τ
```

**规则 (抽象)：**

```latex
Γ, x:τ₁ ⊢ t : τ₂
----------------
Γ ⊢ λx:τ₁.t : τ₁ → τ₂
```

**规则 (应用)：**

```latex
Γ ⊢ t₁ : τ₁ → τ₂    Γ ⊢ t₂ : τ₁
--------------------------------
Γ ⊢ t₁ t₂ : τ₂
```

### 2.2 类型推导示例

**示例 2.1.1 (恒等函数)**:

```latex
x:τ ⊢ x : τ
----------------
⊢ λx:τ.x : τ → τ
```

**示例 2.1.2 (函数组合)**:

```latex
f:τ₂→τ₃, g:τ₁→τ₂, x:τ₁ ⊢ f : τ₂→τ₃
f:τ₂→τ₃, g:τ₁→τ₂, x:τ₁ ⊢ g : τ₁→τ₂
f:τ₂→τ₃, g:τ₁→τ₂, x:τ₁ ⊢ x : τ₁
f:τ₂→τ₃, g:τ₁→τ₂, x:τ₁ ⊢ g x : τ₂
f:τ₂→τ₃, g:τ₁→τ₂, x:τ₁ ⊢ f (g x) : τ₃
f:τ₂→τ₃, g:τ₁→τ₂ ⊢ λx:τ₁.f (g x) : τ₁→τ₃
f:τ₂→τ₃ ⊢ λg:τ₁→τ₂.λx:τ₁.f (g x) : (τ₁→τ₂)→(τ₁→τ₃)
⊢ λf:τ₂→τ₃.λg:τ₁→τ₂.λx:τ₁.f (g x) : (τ₂→τ₃)→((τ₁→τ₂)→(τ₁→τ₃))
```

## 类型推导

### 3.1 类型推导算法

**算法 3.1.1 (类型推导)**:

```latex
W(Γ, x) = (τ, ∅) 其中 Γ(x) = τ
W(Γ, λx.t) = (τ₁ → τ₂, S) 其中
  (τ₂, S₁) = W(Γ ∪ {x:τ₁}, t)
  S = S₁
W(Γ, t₁ t₂) = (S₂(τ₂), S₂ ∘ S₁) 其中
  (τ₁, S₁) = W(Γ, t₁)
  (τ₂, S₂) = W(S₁(Γ), t₂)
  τ₁ = τ₂ → τ₃ (通过合一)
```

### 3.2 合一算法

**算法 3.1.2 (合一)**:

```latex
unify(τ, τ) = ∅
unify(α, τ) = [α ↦ τ] 如果 α ∉ FV(τ)
unify(τ, α) = [α ↦ τ] 如果 α ∉ FV(τ)
unify(τ₁ → τ₂, τ₃ → τ₄) = S₂ ∘ S₁ 其中
  S₁ = unify(τ₁, τ₃)
  S₂ = unify(S₁(τ₂), S₁(τ₄))
```

## 类型安全

### 4.1 进展定理

**定理 4.1.1 (进展)**
如果 ⊢ t : τ，则要么 t 是值，要么存在 t' 使得 t → t'。

**证明：**
对项的结构进行归纳：

1. 变量：不可能，因为 ⊢ x : τ 需要 x:τ ∈ Γ
2. 抽象：λx:τ.t 是值
3. 应用：t₁ t₂，根据归纳假设，t₁ 要么是值要么可以规约
   - 如果 t₁ 可以规约，使用应用规则
   - 如果 t₁ 是值，必须是 λx:τ.t，t₂ 要么是值要么可以规约

### 4.2 保持定理

**定理 4.1.2 (保持)**
如果 Γ ⊢ t : τ 且 t → t'，则 Γ ⊢ t' : τ。

**证明：**
对规约规则进行归纳：

1. β规约：(λx:τ.t) v → t[x ↦ v]
   - 如果 Γ ⊢ (λx:τ.t) v : τ₂
   - 则 Γ ⊢ λx:τ.t : τ → τ₂ 且 Γ ⊢ v : τ
   - 因此 Γ, x:τ ⊢ t : τ₂
   - 通过替换引理，Γ ⊢ t[x ↦ v] : τ₂

## 形式化表示

### 5.1 一阶逻辑表示

**语言 L：**

- 个体变元：t, t', t₁, t₂, ..., τ, τ', τ₁, τ₂, ..., x, y, z, ...
- 谓词符号：⊢ (推导), → (规约), : (类型)
- 函数符号：λ (抽象), · (应用)
- 逻辑连接词：¬, ∧, ∨, →, ↔
- 量词：∀, ∃

**公理系统：**

```latex
A1: Γ, x:τ ⊢ x : τ  // 变量公理
A2: (Γ, x:τ₁ ⊢ t : τ₂) → (Γ ⊢ λx:τ₁.t : τ₁ → τ₂)  // 抽象规则
A3: (Γ ⊢ t₁ : τ₁ → τ₂) ∧ (Γ ⊢ t₂ : τ₁) → (Γ ⊢ t₁ t₂ : τ₂)  // 应用规则
A4: (λx:τ.t) v → t[x ↦ v]  // β规约
```

### 5.2 类型论表示

**类型定义：**

```rust
// 类型定义
#[derive(Debug, Clone, PartialEq)]
enum Type {
    Base(String),
    Function(Box<Type>, Box<Type>),
}

// 项定义
#[derive(Debug, Clone)]
enum Term {
    Variable(String),
    Abstraction(String, Type, Box<Term>),
    Application(Box<Term>, Box<Term>),
}

// 上下文定义
#[derive(Debug, Clone)]
struct Context {
    bindings: HashMap<String, Type>,
}

impl Context {
    fn new() -> Self {
        Context {
            bindings: HashMap::new(),
        }
    }
    
    fn extend(&self, x: String, tau: Type) -> Context {
        let mut new_bindings = self.bindings.clone();
        new_bindings.insert(x, tau);
        Context { bindings: new_bindings }
    }
    
    fn lookup(&self, x: &str) -> Option<&Type> {
        self.bindings.get(x)
    }
}

// 类型推导
struct TypeChecker;

impl TypeChecker {
    fn type_of(&self, ctx: &Context, term: &Term) -> Result<Type, String> {
        match term {
            Term::Variable(x) => {
                ctx.lookup(x)
                    .cloned()
                    .ok_or_else(|| format!("Unbound variable: {}", x))
            }
            
            Term::Abstraction(x, tau, body) => {
                let new_ctx = ctx.extend(x.clone(), tau.clone());
                let body_type = self.type_of(&new_ctx, body)?;
                Ok(Type::Function(Box::new(tau.clone()), Box::new(body_type)))
            }
            
            Term::Application(func, arg) => {
                let func_type = self.type_of(ctx, func)?;
                let arg_type = self.type_of(ctx, arg)?;
                
                match func_type {
                    Type::Function(input_type, output_type) => {
                        if *input_type == arg_type {
                            Ok(*output_type)
                        } else {
                            Err(format!(
                                "Type mismatch: expected {:?}, got {:?}",
                                input_type, arg_type
                            ))
                        }
                    }
                    _ => Err("Non-function type in application".to_string()),
                }
            }
        }
    }
}

// 求值器
struct Evaluator;

impl Evaluator {
    fn eval(&self, term: &Term) -> Term {
        match term {
            Term::Variable(_) => term.clone(),
            
            Term::Abstraction(_, _, _) => term.clone(),
            
            Term::Application(func, arg) => {
                let func_val = self.eval(func);
                let arg_val = self.eval(arg);
                
                match func_val {
                    Term::Abstraction(x, _, body) => {
                        // β规约
                        self.substitute(&body, &x, &arg_val)
                    }
                    _ => Term::Application(Box::new(func_val), Box::new(arg_val)),
                }
            }
        }
    }
    
    fn substitute(&self, term: &Term, x: &str, value: &Term) -> Term {
        match term {
            Term::Variable(y) => {
                if x == y {
                    value.clone()
                } else {
                    term.clone()
                }
            }
            
            Term::Abstraction(y, tau, body) => {
                if x == y {
                    Term::Abstraction(y.clone(), tau.clone(), body.clone())
                } else {
                    Term::Abstraction(
                        y.clone(),
                        tau.clone(),
                        Box::new(self.substitute(body, x, value)),
                    )
                }
            }
            
            Term::Application(func, arg) => Term::Application(
                Box::new(self.substitute(func, x, value)),
                Box::new(self.substitute(arg, x, value)),
            ),
        }
    }
}
```

## 证明系统

### 6.1 自然演绎系统

**类型推导规则：**

```latex
Γ, x:τ ⊢ x : τ  // 变量
Γ, x:τ₁ ⊢ t : τ₂
----------------  // 抽象
Γ ⊢ λx:τ₁.t : τ₁ → τ₂
Γ ⊢ t₁ : τ₁ → τ₂    Γ ⊢ t₂ : τ₁
--------------------------------  // 应用
Γ ⊢ t₁ t₂ : τ₂
```

### 6.2 证明示例

**证明：类型推导的唯一性**:

```latex
定理：如果 Γ ⊢ t : τ₁ 且 Γ ⊢ t : τ₂，则 τ₁ = τ₂

证明：对项的结构进行归纳
1. 变量：t = x，则 τ₁ = Γ(x) = τ₂
2. 抽象：t = λx:τ.t'，则 τ₁ = τ → τ₁' 且 τ₂ = τ → τ₂'
   根据归纳假设，τ₁' = τ₂'，因此 τ₁ = τ₂
3. 应用：t = t₁ t₂，则 τ₁ = τ₁' 且 τ₂ = τ₂'
   根据归纳假设，τ₁' = τ₂'，因此 τ₁ = τ₂
```

## 与其他学科的关联

### 7.1 与哲学的关联

**本体论：**

- 类型与实体
- 函数与关系
- 计算与变化

**认识论：**

- 类型推导与推理
- 类型检查与验证
- 类型安全与确定性

### 7.2 与数学的关联

**集合论：**

- 类型与集合
- 函数类型与函数集合
- 类型推导与集合运算

**范畴论：**

- 类型与对象
- 函数类型与态射
- 类型系统与范畴

### 7.3 与计算机科学的关联

**编程语言：**

- 类型系统设计
- 类型检查器实现
- 类型安全保证

**编译器：**

- 类型推导算法
- 类型检查优化
- 类型信息传播

## 应用示例

### 8.1 类型检查器

```rust
// 完整的类型检查器实现
#[derive(Debug, Clone)]
struct TypeChecker {
    type_errors: Vec<String>,
}

impl TypeChecker {
    fn new() -> Self {
        TypeChecker {
            type_errors: Vec::new(),
        }
    }
    
    fn check_program(&mut self, program: &Term) -> Result<Type, Vec<String>> {
        let ctx = Context::new();
        match self.type_of(&ctx, program) {
            Ok(typ) => Ok(typ),
            Err(e) => {
                self.type_errors.push(e);
                Err(self.type_errors.clone())
            }
        }
    }
    
    fn type_of(&self, ctx: &Context, term: &Term) -> Result<Type, String> {
        // 实现类型推导
        match term {
            Term::Variable(x) => {
                ctx.lookup(x)
                    .cloned()
                    .ok_or_else(|| format!("Unbound variable: {}", x))
            }
            
            Term::Abstraction(x, tau, body) => {
                let new_ctx = ctx.extend(x.clone(), tau.clone());
                let body_type = self.type_of(&new_ctx, body)?;
                Ok(Type::Function(Box::new(tau.clone()), Box::new(body_type)))
            }
            
            Term::Application(func, arg) => {
                let func_type = self.type_of(ctx, func)?;
                let arg_type = self.type_of(ctx, arg)?;
                
                match func_type {
                    Type::Function(input_type, output_type) => {
                        if *input_type == arg_type {
                            Ok(*output_type)
                        } else {
                            Err(format!(
                                "Type mismatch: expected {:?}, got {:?}",
                                input_type, arg_type
                            ))
                        }
                    }
                    _ => Err("Non-function type in application".to_string()),
                }
            }
        }
    }
}
```

### 8.2 类型推导算法

```rust
// Hindley-Milner类型推导算法
#[derive(Debug, Clone)]
struct TypeInference {
    fresh_counter: usize,
}

impl TypeInference {
    fn new() -> Self {
        TypeInference { fresh_counter: 0 }
    }
    
    fn fresh_type(&mut self) -> Type {
        let name = format!("α{}", self.fresh_counter);
        self.fresh_counter += 1;
        Type::Base(name)
    }
    
    fn infer(&mut self, ctx: &Context, term: &Term) -> Result<(Type, Substitution), String> {
        match term {
            Term::Variable(x) => {
                if let Some(typ) = ctx.lookup(x) {
                    Ok((typ.clone(), Substitution::empty()))
                } else {
                    Err(format!("Unbound variable: {}", x))
                }
            }
            
            Term::Abstraction(x, tau, body) => {
                let new_ctx = ctx.extend(x.clone(), tau.clone());
                let (body_type, s) = self.infer(&new_ctx, body)?;
                let function_type = Type::Function(Box::new(tau.clone()), Box::new(body_type));
                Ok((function_type, s))
            }
            
            Term::Application(func, arg) => {
                let (func_type, s₁) = self.infer(ctx, func)?;
                let (arg_type, s₂) = self.infer(&s₁.apply_context(ctx), arg)?;
                let result_type = self.fresh_type();
                
                let s₃ = self.unify(
                    &s₂.apply_type(&func_type),
                    &Type::Function(Box::new(arg_type), Box::new(result_type.clone())),
                )?;
                
                let final_substitution = s₃.compose(&s₂).compose(&s₁);
                Ok((final_substitution.apply_type(&result_type), final_substitution))
            }
        }
    }
    
    fn unify(&self, tau₁: &Type, tau₂: &Type) -> Result<Substitution, String> {
        match (tau₁, tau₂) {
            (Type::Base(a), Type::Base(b)) if a == b => Ok(Substitution::empty()),
            
            (Type::Base(a), tau) => {
                if self.occurs_in(a, tau) {
                    Err("Circular type".to_string())
                } else {
                    Ok(Substitution::singleton(a.clone(), tau.clone()))
                }
            }
            
            (tau, Type::Base(a)) => self.unify(tau₂, tau₁),
            
            (Type::Function(arg₁, res₁), Type::Function(arg₂, res₂)) => {
                let s₁ = self.unify(arg₁, arg₂)?;
                let s₂ = self.unify(&s₁.apply_type(res₁), &s₁.apply_type(res₂))?;
                Ok(s₂.compose(&s₁))
            }
            
            _ => Err("Cannot unify types".to_string()),
        }
    }
    
    fn occurs_in(&self, var: &str, tau: &Type) -> bool {
        match tau {
            Type::Base(a) => a == var,
            Type::Function(arg, res) => self.occurs_in(var, arg) || self.occurs_in(var, res),
        }
    }
}

#[derive(Debug, Clone)]
struct Substitution {
    mappings: HashMap<String, Type>,
}

impl Substitution {
    fn empty() -> Self {
        Substitution {
            mappings: HashMap::new(),
        }
    }
    
    fn singleton(var: String, typ: Type) -> Self {
        let mut mappings = HashMap::new();
        mappings.insert(var, typ);
        Substitution { mappings }
    }
    
    fn apply_type(&self, tau: &Type) -> Type {
        match tau {
            Type::Base(a) => self.mappings.get(a).cloned().unwrap_or(tau.clone()),
            Type::Function(arg, res) => Type::Function(
                Box::new(self.apply_type(arg)),
                Box::new(self.apply_type(res)),
            ),
        }
    }
    
    fn apply_context(&self, ctx: &Context) -> Context {
        let mut new_bindings = HashMap::new();
        for (var, typ) in &ctx.bindings {
            new_bindings.insert(var.clone(), self.apply_type(typ));
        }
        Context { bindings: new_bindings }
    }
    
    fn compose(&self, other: &Substitution) -> Substitution {
        let mut mappings = HashMap::new();
        
        // 应用other到self的映射
        for (var, typ) in &self.mappings {
            mappings.insert(var.clone(), other.apply_type(typ));
        }
        
        // 添加other中的映射
        for (var, typ) in &other.mappings {
            if !self.mappings.contains_key(var) {
                mappings.insert(var.clone(), typ.clone());
            }
        }
        
        Substitution { mappings }
    }
}
```

## 总结

简单类型λ演算是类型理论的基础，通过形式化表示和严格的证明系统，我们可以：

1. 建立类型系统的基本理论
2. 定义类型推导规则
3. 证明类型安全性质
4. 实现类型检查算法

这些理论为后续的依赖类型理论、线性类型理论等提供了重要的基础。
