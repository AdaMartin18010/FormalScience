# 02. 类型理论基础 (Type Theory Foundation)

## 目录

1. [基础定义与公理](#1-基础定义与公理)
2. [类型系统语义](#2-类型系统语义)
3. [类型推断算法](#3-类型推断算法)
4. [高级类型系统](#4-高级类型系统)
5. [元理论性质](#5-元理论性质)
6. [实际应用](#6-实际应用)
7. [形式化证明](#7-形式化证明)
8. [代码实现](#8-代码实现)

---

## 1. 基础定义与公理

### 1.1 类型系统基础

**定义 1.1 (类型上下文)**
设 $\Gamma$ 为类型上下文，定义为变量到类型的映射：
$$\Gamma : \text{Var} \rightarrow \text{Type}$$

**定义 1.2 (类型判断)**
类型判断形如 $\Gamma \vdash e : \tau$，表示在上下文 $\Gamma$ 中，表达式 $e$ 具有类型 $\tau$。

**公理 1.1 (变量规则)**
$$\frac{x : \tau \in \Gamma}{\Gamma \vdash x : \tau} \quad \text{(Var)}$$

**公理 1.2 (函数类型引入)**
$$\frac{\Gamma, x : \tau_1 \vdash e : \tau_2}{\Gamma \vdash \lambda x.e : \tau_1 \rightarrow \tau_2} \quad \text{(Abs)}$$

**公理 1.3 (函数类型消除)**
$$\frac{\Gamma \vdash e_1 : \tau_1 \rightarrow \tau_2 \quad \Gamma \vdash e_2 : \tau_1}{\Gamma \vdash e_1 e_2 : \tau_2} \quad \text{(App)}$$

**公理 1.4 (单位类型)**
$$\frac{}{\Gamma \vdash () : \text{Unit}} \quad \text{(Unit)}$$

**公理 1.5 (布尔类型)**
$$\frac{}{\Gamma \vdash \text{true} : \text{Bool}} \quad \text{(True)}$$
$$\frac{}{\Gamma \vdash \text{false} : \text{Bool}} \quad \text{(False)}$$

### 1.2 类型安全性

**定理 1.1 (类型保持性 - Type Preservation)**
如果 $\Gamma \vdash e : \tau$ 且 $e \rightarrow e'$，则 $\Gamma \vdash e' : \tau$。

**证明：** 通过结构归纳法证明。对于每个归约规则：

1. **Beta归约**：$(\lambda x.e) v \rightarrow e[v/x]$
   - 假设：$\Gamma \vdash (\lambda x.e) v : \tau_2$
   - 根据App规则：$\Gamma \vdash \lambda x.e : \tau_1 \rightarrow \tau_2$ 且 $\Gamma \vdash v : \tau_1$
   - 根据Abs规则：$\Gamma, x : \tau_1 \vdash e : \tau_2$
   - 通过替换引理：$\Gamma \vdash e[v/x] : \tau_2$

2. **其他归约规则**：类似证明

**定理 1.2 (进展性 - Progress)**
如果 $\emptyset \vdash e : \tau$，则要么 $e$ 是值，要么存在 $e'$ 使得 $e \rightarrow e'$。

**证明：** 通过结构归纳法证明。对于每个语法构造：

1. **变量**：$\emptyset \vdash x : \tau$ 不可能，因为 $x \notin \emptyset$
2. **抽象**：$\lambda x.e$ 总是值
3. **应用**：$e_1 e_2$，根据归纳假设，$e_1$ 要么是值要么可归约
   - 如果 $e_1$ 可归约，则 $e_1 e_2$ 可归约
   - 如果 $e_1$ 是值，则 $e_1 = \lambda x.e$，$e_1 e_2$ 可进行beta归约

---

## 2. 类型系统语义

### 2.1 指称语义

**定义 2.1 (类型解释)**
$$\llbracket \text{Unit} \rrbracket = \{()\}$$
$$\llbracket \text{Bool} \rrbracket = \{\text{true}, \text{false}\}$$
$$\llbracket \tau_1 \rightarrow \tau_2 \rrbracket = \llbracket \tau_1 \rrbracket \rightarrow \llbracket \tau_2 \rrbracket$$

**定义 2.2 (表达式解释)**
$$\llbracket x \rrbracket_{\rho,\sigma} = \rho(x)$$
$$\llbracket \lambda x.e \rrbracket_{\rho,\sigma} = \lambda v.\llbracket e \rrbracket_{\rho[x \mapsto v],\sigma}$$
$$\llbracket e_1 e_2 \rrbracket_{\rho,\sigma} = \llbracket e_1 \rrbracket_{\rho,\sigma}(\llbracket e_2 \rrbracket_{\rho,\sigma})$$

### 2.2 操作语义

**定义 2.3 (小步语义)**
$$(\lambda x.e) v \rightarrow e[v/x] \quad \text{(Beta)}$$
$$\frac{e_1 \rightarrow e_1'}{e_1 e_2 \rightarrow e_1' e_2} \quad \text{(App1)}$$
$$\frac{e_2 \rightarrow e_2'}{v e_2 \rightarrow v e_2'} \quad \text{(App2)}$$

**定义 2.4 (大步语义)**
$$v \Downarrow v \quad \text{(Value)}$$
$$\frac{e_1 \Downarrow \lambda x.e \quad e_2 \Downarrow v \quad e[v/x] \Downarrow v'}{e_1 e_2 \Downarrow v'} \quad \text{(App)}$$

---

## 3. 类型推断算法

### 3.1 Hindley-Milner 类型系统

**算法 W (Robinson's Unification)**

```haskell
-- 类型定义
data Type = TVar String
          | TArrow Type Type
          | TCon String
          | TUnit
          | TBool

-- 替换
type Substitution = [(String, Type)]

-- 统一算法
unify :: Type -> Type -> Either String Substitution
unify (TVar a) t = 
  if a `elem` ftv t 
  then Left "Occurs check failed"
  else Right [(a, t)]
unify t (TVar a) = unify (TVar a) t
unify (TArrow t1 t2) (TArrow t1' t2') = do
  s1 <- unify t1 t1'
  s2 <- unify (apply s1 t2) (apply s1 t2')
  return (compose s2 s1)
unify (TCon a) (TCon b) = 
  if a == b then Right [] else Left "Type mismatch"
unify TUnit TUnit = Right []
unify TBool TBool = Right []
unify _ _ = Left "Type mismatch"

-- 自由类型变量
ftv :: Type -> [String]
ftv (TVar a) = [a]
ftv (TArrow t1 t2) = ftv t1 ++ ftv t2
ftv (TCon _) = []
ftv TUnit = []
ftv TBool = []

-- 替换应用
apply :: Substitution -> Type -> Type
apply s (TVar a) = fromMaybe (TVar a) (lookup a s)
apply s (TArrow t1 t2) = TArrow (apply s t1) (apply s t2)
apply s t = t

-- 替换组合
compose :: Substitution -> Substitution -> Substitution
compose s1 s2 = [(a, apply s1 t) | (a, t) <- s2] ++ s1
```

**定理 3.1 (算法 W 的正确性)**
如果算法 W 成功，则返回的替换是最一般的一致替换。

**证明：**

1. **终止性**：每次递归调用减少类型的大小
2. **正确性**：通过结构归纳法证明
3. **最一般性**：通过反证法证明不存在更一般的替换

---

## 4. 高级类型系统

### 4.1 参数多态性

**定义 4.1 (全称类型)**
$$\frac{\Gamma, \alpha \vdash e : \tau}{\Gamma \vdash \Lambda \alpha.e : \forall \alpha.\tau} \quad \text{(Gen)}$$

**定义 4.2 (类型实例化)**
$$\frac{\Gamma \vdash e : \forall \alpha.\tau}{\Gamma \vdash e[\tau'] : \tau[\alpha \mapsto \tau']} \quad \text{(Inst)}$$

**示例 4.1 (多态恒等函数)**

```haskell
-- 类型：∀α.α → α
id :: forall a. a -> a
id = \x -> x

-- 使用
intId :: Int -> Int
intId = id @Int

boolId :: Bool -> Bool
boolId = id @Bool
```

### 4.2 存在类型

**定义 4.3 (存在类型引入)**
$$\frac{\Gamma \vdash e : \tau[\alpha \mapsto \tau']}{\Gamma \vdash \text{pack } \tau', e \text{ as } \exists \alpha.\tau : \exists \alpha.\tau} \quad \text{(Pack)}$$

**定义 4.4 (存在类型消除)**
$$\frac{\Gamma \vdash e_1 : \exists \alpha.\tau \quad \Gamma, \alpha, x : \tau \vdash e_2 : \tau'}{\Gamma \vdash \text{unpack } \alpha, x = e_1 \text{ in } e_2 : \tau'} \quad \text{(Unpack)}$$

**示例 4.2 (抽象数据类型)**

```haskell
-- 队列的抽象表示
type Queue a = exists s. (s, s -> a -> s, s -> (a, s))

-- 实现
emptyQueue :: Queue a
emptyQueue = pack ([], \s a -> a:s, \s -> (head s, tail s)) as Queue a
```

---

## 5. 元理论性质

### 5.1 强正规化

**定理 5.1 (强正规化)**
在强类型系统中，所有良类型的项都是强正规化的。

**证明：** 通过逻辑关系方法：

1. **定义逻辑关系**：$R_\tau(e)$ 表示 $e$ 在类型 $\tau$ 上的逻辑关系
2. **基本类型**：$R_{\text{Bool}}(e)$ 当且仅当 $e$ 强正规化且 $e \Downarrow \text{true}$ 或 $e \Downarrow \text{false}$
3. **函数类型**：$R_{\tau_1 \rightarrow \tau_2}(e)$ 当且仅当 $e$ 强正规化且对所有 $v_1$ 满足 $R_{\tau_1}(v_1)$，有 $R_{\tau_2}(e v_1)$
4. **基本引理**：如果 $\Gamma \vdash e : \tau$，则 $R_\tau(e)$

### 5.2 一致性

**定理 5.2 (类型系统一致性)**
如果 $\Gamma \vdash e : \tau$，则 $e$ 不会产生类型错误。

**证明：** 通过类型保持性和进展性：

1. 类型保持性确保归约过程中类型不变
2. 进展性确保良类型项要么是值要么可继续归约
3. 结合两者，良类型项不会产生运行时类型错误

---

## 6. 实际应用

### 6.1 编译器中的类型检查

**类型检查器实现**

```haskell
-- 表达式类型
data Expr = Var String
          | Abs String Expr
          | App Expr Expr
          | Unit
          | Bool Bool

-- 类型错误
data TypeError = UnboundVariable String
               | TypeMismatch Type Type
               | NotAFunction Type

-- 类型检查
typeCheck :: Context -> Expr -> Either TypeError Type
typeCheck ctx (Var x) = 
  case lookup x ctx of
    Just t -> Right t
    Nothing -> Left (UnboundVariable x)

typeCheck ctx (Abs x e) = do
  t <- typeCheck ((x, TVar "a") : ctx) e
  return (TArrow (TVar "a") t)

typeCheck ctx (App e1 e2) = do
  t1 <- typeCheck ctx e1
  t2 <- typeCheck ctx e2
  case t1 of
    TArrow t1' t2' | t1' == t2 -> Right t2'
    _ -> Left (TypeMismatch t1 (TArrow t2 (TVar "b")))

typeCheck ctx Unit = Right TUnit
typeCheck ctx (Bool _) = Right TBool
```

### 6.2 类型安全的编程实践

**示例 6.1 (类型安全的API设计)**

```rust
// Rust 实现
trait Monad<T> {
    fn bind<U, F>(self, f: F) -> impl Monad<U>
    where F: FnOnce(T) -> impl Monad<U>;
    
    fn return_(value: T) -> impl Monad<T>;
}

// 类型安全的错误处理
enum Result<T, E> {
    Ok(T),
    Err(E),
}

impl<T, E> Result<T, E> {
    fn map<U, F>(self, f: F) -> Result<U, E>
    where F: FnOnce(T) -> U {
        match self {
            Ok(t) => Ok(f(t)),
            Err(e) => Err(e),
        }
    }
    
    fn and_then<U, F>(self, f: F) -> Result<U, E>
    where F: FnOnce(T) -> Result<U, E> {
        match self {
            Ok(t) => f(t),
            Err(e) => Err(e),
        }
    }
}
```

---

## 7. 形式化证明

### 7.1 替换引理

**引理 7.1 (替换引理)**
如果 $\Gamma, x : \tau_1 \vdash e : \tau_2$ 且 $\Gamma \vdash v : \tau_1$，则 $\Gamma \vdash e[v/x] : \tau_2$。

**证明：** 通过结构归纳法：

1. **变量情况**：$e = x$
   - 如果 $x = y$，则 $e[v/x] = v$，根据假设 $\Gamma \vdash v : \tau_1 = \tau_2$
   - 如果 $x \neq y$，则 $e[v/x] = y$，根据变量规则 $\Gamma \vdash y : \tau_2$

2. **抽象情况**：$e = \lambda y.e'$
   - 根据抽象规则：$\Gamma, x : \tau_1, y : \tau_1' \vdash e' : \tau_2'$
   - 根据归纳假设：$\Gamma, y : \tau_1' \vdash e'[v/x] : \tau_2'$
   - 根据抽象规则：$\Gamma \vdash \lambda y.e'[v/x] : \tau_1' \rightarrow \tau_2'$

3. **应用情况**：$e = e_1 e_2$
   - 根据应用规则：$\Gamma, x : \tau_1 \vdash e_1 : \tau_2' \rightarrow \tau_2$ 且 $\Gamma, x : \tau_1 \vdash e_2 : \tau_2'$
   - 根据归纳假设：$\Gamma \vdash e_1[v/x] : \tau_2' \rightarrow \tau_2$ 且 $\Gamma \vdash e_2[v/x] : \tau_2'$
   - 根据应用规则：$\Gamma \vdash e_1[v/x] e_2[v/x] : \tau_2$

### 7.2 类型保持性证明

**定理 7.1 (类型保持性详细证明)**
如果 $\Gamma \vdash e : \tau$ 且 $e \rightarrow e'$，则 $\Gamma \vdash e' : \tau$。

**证明：** 通过结构归纳法，考虑所有归约规则：

1. **Beta归约**：$(\lambda x.e) v \rightarrow e[v/x]$
   - 假设：$\Gamma \vdash (\lambda x.e) v : \tau_2$
   - 根据App规则：$\Gamma \vdash \lambda x.e : \tau_1 \rightarrow \tau_2$ 且 $\Gamma \vdash v : \tau_1$
   - 根据Abs规则：$\Gamma, x : \tau_1 \vdash e : \tau_2$
   - 通过替换引理：$\Gamma \vdash e[v/x] : \tau_2$

2. **App1归约**：$\frac{e_1 \rightarrow e_1'}{e_1 e_2 \rightarrow e_1' e_2}$
   - 假设：$\Gamma \vdash e_1 e_2 : \tau_2$
   - 根据App规则：$\Gamma \vdash e_1 : \tau_1 \rightarrow \tau_2$ 且 $\Gamma \vdash e_2 : \tau_1$
   - 根据归纳假设：$\Gamma \vdash e_1' : \tau_1 \rightarrow \tau_2$
   - 根据App规则：$\Gamma \vdash e_1' e_2 : \tau_2$

3. **App2归约**：$\frac{e_2 \rightarrow e_2'}{v e_2 \rightarrow v e_2'}$
   - 类似证明

---

## 8. 代码实现

### 8.1 Haskell 实现

```haskell
-- 类型系统实现
module TypeSystem where

-- 表达式
data Expr = Var String
          | Abs String Expr
          | App Expr Expr
          | Unit
          | Bool Bool
          | If Expr Expr Expr

-- 类型
data Type = TVar String
          | TArrow Type Type
          | TUnit
          | TBool

-- 上下文
type Context = [(String, Type)]

-- 类型检查
typeCheck :: Context -> Expr -> Either String Type
typeCheck ctx (Var x) = 
  case lookup x ctx of
    Just t -> Right t
    Nothing -> Left $ "Unbound variable: " ++ x

typeCheck ctx (Abs x e) = do
  t <- typeCheck ((x, TVar "a") : ctx) e
  return (TArrow (TVar "a") t)

typeCheck ctx (App e1 e2) = do
  t1 <- typeCheck ctx e1
  t2 <- typeCheck ctx e2
  case t1 of
    TArrow t1' t2' | t1' == t2 -> Right t2'
    _ -> Left $ "Type mismatch: expected function, got " ++ show t1

typeCheck ctx Unit = Right TUnit
typeCheck ctx (Bool _) = Right TBool

typeCheck ctx (If cond thenExpr elseExpr) = do
  condType <- typeCheck ctx cond
  case condType of
    TBool -> do
      thenType <- typeCheck ctx thenExpr
      elseType <- typeCheck ctx elseExpr
      if thenType == elseType 
        then Right thenType
        else Left "Branches have different types"
    _ -> Left "Condition must be boolean"

-- 求值
data Value = VUnit
           | VBool Bool
           | VClosure String Expr Context

eval :: Context -> Expr -> Either String Value
eval ctx (Var x) = 
  case lookup x ctx of
    Just (VClosure _ _ _) -> Left "Cannot evaluate type"
    _ -> Left $ "Unbound variable: " ++ x

eval ctx (Abs x e) = Right (VClosure x e ctx)
eval ctx Unit = Right VUnit
eval ctx (Bool b) = Right (VBool b)

eval ctx (App e1 e2) = do
  v1 <- eval ctx e1
  v2 <- eval ctx e2
  case v1 of
    VClosure x body env -> eval ((x, v2) : env) body
    _ -> Left "Not a function"

eval ctx (If cond thenExpr elseExpr) = do
  condVal <- eval ctx cond
  case condVal of
    VBool True -> eval ctx thenExpr
    VBool False -> eval ctx elseExpr
    _ -> Left "Condition must be boolean"
```

### 8.2 Rust 实现

```rust
// Rust 类型系统实现
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
enum Type {
    TVar(String),
    TArrow(Box<Type>, Box<Type>),
    TUnit,
    TBool,
}

#[derive(Debug, Clone)]
enum Expr {
    Var(String),
    Abs(String, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    Unit,
    Bool(bool),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
}

#[derive(Debug, Clone)]
enum Value {
    VUnit,
    VBool(bool),
    VClosure(String, Box<Expr>, HashMap<String, Value>),
}

#[derive(Debug)]
enum TypeError {
    UnboundVariable(String),
    TypeMismatch(Type, Type),
    NotAFunction(Type),
}

struct TypeChecker;

impl TypeChecker {
    fn type_check(
        ctx: &HashMap<String, Type>, 
        expr: &Expr
    ) -> Result<Type, TypeError> {
        match expr {
            Expr::Var(x) => {
                ctx.get(x)
                    .cloned()
                    .ok_or(TypeError::UnboundVariable(x.clone()))
            }
            
            Expr::Abs(x, e) => {
                let mut new_ctx = ctx.clone();
                new_ctx.insert(x.clone(), Type::TVar("a".to_string()));
                let t = Self::type_check(&new_ctx, e)?;
                Ok(Type::TArrow(Box::new(Type::TVar("a".to_string())), Box::new(t)))
            }
            
            Expr::App(e1, e2) => {
                let t1 = Self::type_check(ctx, e1)?;
                let t2 = Self::type_check(ctx, e2)?;
                
                match t1 {
                    Type::TArrow(t1_in, t1_out) => {
                        if *t1_in == t2 {
                            Ok(*t1_out)
                        } else {
                            Err(TypeError::TypeMismatch(*t1_in, t2))
                        }
                    }
                    _ => Err(TypeError::NotAFunction(t1)),
                }
            }
            
            Expr::Unit => Ok(Type::TUnit),
            Expr::Bool(_) => Ok(Type::TBool),
            
            Expr::If(cond, then_expr, else_expr) => {
                let cond_type = Self::type_check(ctx, cond)?;
                if cond_type != Type::TBool {
                    return Err(TypeError::TypeMismatch(cond_type, Type::TBool));
                }
                
                let then_type = Self::type_check(ctx, then_expr)?;
                let else_type = Self::type_check(ctx, else_expr)?;
                
                if then_type == else_type {
                    Ok(then_type)
                } else {
                    Err(TypeError::TypeMismatch(then_type, else_type))
                }
            }
        }
    }
}

struct Evaluator;

impl Evaluator {
    fn eval(
        ctx: &HashMap<String, Value>, 
        expr: &Expr
    ) -> Result<Value, String> {
        match expr {
            Expr::Var(x) => {
                ctx.get(x)
                    .cloned()
                    .ok_or_else(|| format!("Unbound variable: {}", x))
            }
            
            Expr::Abs(x, e) => {
                Ok(Value::VClosure(x.clone(), e.clone(), ctx.clone()))
            }
            
            Expr::App(e1, e2) => {
                let v1 = Self::eval(ctx, e1)?;
                let v2 = Self::eval(ctx, e2)?;
                
                match v1 {
                    Value::VClosure(x, body, env) => {
                        let mut new_env = env;
                        new_env.insert(x, v2);
                        Self::eval(&new_env, &body)
                    }
                    _ => Err("Not a function".to_string()),
                }
            }
            
            Expr::Unit => Ok(Value::VUnit),
            Expr::Bool(b) => Ok(Value::VBool(*b)),
            
            Expr::If(cond, then_expr, else_expr) => {
                let cond_val = Self::eval(ctx, cond)?;
                match cond_val {
                    Value::VBool(true) => Self::eval(ctx, then_expr),
                    Value::VBool(false) => Self::eval(ctx, else_expr),
                    _ => Err("Condition must be boolean".to_string()),
                }
            }
        }
    }
}

// 使用示例
fn main() {
    // 类型检查示例
    let ctx: HashMap<String, Type> = HashMap::new();
    let expr = Expr::App(
        Box::new(Expr::Abs("x".to_string(), Box::new(Expr::Var("x".to_string())))),
        Box::new(Expr::Bool(true))
    );
    
    match TypeChecker::type_check(&ctx, &expr) {
        Ok(t) => println!("Type: {:?}", t),
        Err(e) => println!("Type error: {:?}", e),
    }
    
    // 求值示例
    let ctx: HashMap<String, Value> = HashMap::new();
    let expr = Expr::If(
        Box::new(Expr::Bool(true)),
        Box::new(Expr::Bool(false)),
        Box::new(Expr::Bool(true))
    );
    
    match Evaluator::eval(&ctx, &expr) {
        Ok(v) => println!("Value: {:?}", v),
        Err(e) => println!("Evaluation error: {}", e),
    }
}
```

---

## 参考文献

1. **Girard, J. Y.** (1987). Linear logic. *Theoretical computer science*, 50(1), 1-101.
2. **Reynolds, J. C.** (1983). Types, abstraction and parametric polymorphism. *Information processing*, 83, 513-523.
3. **Martin-Löf, P.** (1984). *Intuitionistic type theory*. Bibliopolis.
4. **Univalent Foundations Program.** (2013). *Homotopy type theory: Univalent foundations of mathematics*.
5. **Selinger, P.** (2004). Towards a quantum programming language. *Mathematical Structures in Computer Science*, 14(4), 527-586.
6. **Pierce, B. C.** (2002). *Types and programming languages*. MIT press.
7. **Cardelli, L., & Wegner, P.** (1985). On understanding types, data abstraction, and polymorphism. *ACM Computing Surveys (CSUR)*, 17(4), 471-523.
8. **Mitchell, J. C.** (1996). *Foundations for programming languages*. MIT press.

---

## 交叉引用

- [01. 综合理论框架](../01_Comprehensive_Theory_Framework.md)
- [03. 线性类型理论](../03_Linear_Type_Theory.md)
- [04. 仿射类型理论](../04_Affine_Type_Theory.md)
- [05. 依赖类型理论](../05_Dependent_Type_Theory.md)
- [06. 高阶类型理论](../06_Higher_Order_Type_Theory.md)
- [07. 量子类型理论](../07_Quantum_Type_Theory.md)
- [08. 时态类型理论](../08_Temporal_Type_Theory.md)
- [09. 分布式类型理论](../09_Distributed_Type_Theory.md)
- [10. 控制论类型理论](../10_Control_Theory_Type_Theory.md)
