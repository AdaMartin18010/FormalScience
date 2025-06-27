# 简单类型λ演算 (Simply Typed Lambda Calculus)

## 🎯 **概述**

简单类型λ演算是类型理论的基础，通过引入类型系统来避免无类型λ演算中的类型错误。本文档通过严格的形式化方法，建立了简单类型λ演算的完整理论体系。

## 📚 **目录结构**

### 1. 基础概念

- [1.1_Syntax](./1.1_Syntax/) - 语法定义
- [1.2_Types](./1.2_Types/) - 类型系统
- [1.3_Terms](./1.3_Terms/) - 项的定义
- [1.4_Contexts](./1.4_Contexts/) - 上下文

### 2. 类型规则

- [2.1_Type_Rules](./2.1_Type_Rules/) - 类型规则
- [2.2_Type_Checking](./2.2_Type_Checking/) - 类型检查
- [2.3_Type_Inference](./2.3_Type_Inference/) - 类型推断
- [2.4_Type_Safety](./2.4_Type_Safety/) - 类型安全

### 3. 归约系统

- [3.1_Beta_Reduction](./3.1_Beta_Reduction/) - β归约
- [3.2_Eta_Reduction](./3.2_Eta_Reduction/) - η归约
- [3.3_Reduction_Strategies](./3.3_Reduction_Strategies/) - 归约策略
- [3.4_Normal_Forms](./3.4_Normal_Forms/) - 范式

### 4. 语义理论

- [4.1_Operational_Semantics](./4.1_Operational_Semantics/) - 操作语义
- [4.2_Denotational_Semantics](./4.2_Denotational_Semantics/) - 指称语义
- [4.3_Equational_Theory](./4.3_Equational_Theory/) - 等式理论
- [4.4_Models](./4.4_Models/) - 模型理论

## 🔗 **快速导航**

### 基础概念

- [语法定义](./1.1_Syntax/README.md)
- [类型系统](./1.2_Types/README.md)
- [项的定义](./1.3_Terms/README.md)
- [上下文](./1.4_Contexts/README.md)

### 类型规则

- [类型规则](./2.1_Type_Rules/README.md)
- [类型检查](./2.2_Type_Checking/README.md)
- [类型推断](./2.3_Type_Inference/README.md)
- [类型安全](./2.4_Type_Safety/README.md)

## 📋 **核心理论**

### 1. 语法定义

**定义 1.1 (类型)**
简单类型由以下语法定义：
$$\tau ::= \alpha \mid \tau_1 \rightarrow \tau_2$$

其中 $\alpha$ 是基本类型，$\tau_1 \rightarrow \tau_2$ 是函数类型。

**定义 1.2 (项)**
简单类型λ演算的项由以下语法定义：
$$M ::= x \mid \lambda x:\tau.M \mid M_1 M_2$$

其中 $x$ 是变量，$\lambda x:\tau.M$ 是抽象，$M_1 M_2$ 是应用。

**定义 1.3 (上下文)**
类型上下文是变量到类型的映射：
$$\Gamma ::= \emptyset \mid \Gamma, x:\tau$$

### 2. 类型规则1

**定义 2.1 (类型判断)**
类型判断的形式为 $\Gamma \vdash M : \tau$，表示在上下文 $\Gamma$ 下，项 $M$ 具有类型 $\tau$。

**规则 2.1 (变量规则)**
$$\frac{x:\tau \in \Gamma}{\Gamma \vdash x : \tau} \text{ (Var)}$$

**规则 2.2 (抽象规则)**
$$\frac{\Gamma, x:\tau_1 \vdash M : \tau_2}{\Gamma \vdash \lambda x:\tau_1.M : \tau_1 \rightarrow \tau_2} \text{ (Abs)}$$

**规则 2.3 (应用规则)**
$$\frac{\Gamma \vdash M_1 : \tau_1 \rightarrow \tau_2 \quad \Gamma \vdash M_2 : \tau_1}{\Gamma \vdash M_1 M_2 : \tau_2} \text{ (App)}$$

### 3. 归约规则

**定义 3.1 (β归约)**
β归约规则：
$$(\lambda x:\tau.M) N \rightarrow_\beta M[x := N]$$

其中 $M[x := N]$ 表示在 $M$ 中将 $x$ 替换为 $N$。

**定义 3.2 (η归约)**
η归约规则：
$$\lambda x:\tau.(M x) \rightarrow_\eta M \quad \text{if } x \notin \text{FV}(M)$$

其中 $\text{FV}(M)$ 表示 $M$ 的自由变量集合。

### 4. 类型安全定理

**定理 4.1 (类型保持性)**
如果 $\Gamma \vdash M : \tau$ 且 $M \rightarrow M'$，则 $\Gamma \vdash M' : \tau$。

**证明：**
通过结构归纳证明：

1. **变量**：变量不能归约
2. **抽象**：如果 $M = \lambda x:\tau_1.N$ 且 $M \rightarrow M'$，则 $M' = \lambda x:\tau_1.N'$ 且 $N \rightarrow N'$
3. **应用**：如果 $M = M_1 M_2$ 且 $M \rightarrow M'$，则有两种情况：
   - β归约：$M_1 = \lambda x:\tau.N$，$M' = N[x := M_2]$
   - 应用归约：$M_1 \rightarrow M_1'$ 或 $M_2 \rightarrow M_2'$

**定理 4.2 (进展性)**
如果 $\emptyset \vdash M : \tau$，则 $M$ 要么是值，要么可以归约。

**证明：**
通过结构归纳证明：

1. **变量**：在空上下文中，变量没有类型
2. **抽象**：抽象是值
3. **应用**：如果 $M = M_1 M_2$，则：
   - 如果 $M_1$ 可以归约，则 $M$ 可以归约
   - 如果 $M_1$ 是值，则 $M_1 = \lambda x:\tau.N$，可以进行β归约

## 🔧 **形式化实现**

### 1. 简单类型λ演算类型系统

```rust
// 类型定义
#[derive(Debug, Clone, PartialEq)]
enum Type {
    Base(String),
    Arrow(Box<Type>, Box<Type>),
}

impl Type {
    fn arrow(domain: Type, codomain: Type) -> Self {
        Type::Arrow(Box::new(domain), Box::new(codomain))
    }
}

// 项定义
#[derive(Debug, Clone)]
enum Term {
    Var(String),
    Abs(String, Type, Box<Term>),
    App(Box<Term>, Box<Term>),
}

impl Term {
    fn var(name: &str) -> Self {
        Term::Var(name.to_string())
    }
    
    fn abs(name: &str, ty: Type, body: Term) -> Self {
        Term::Abs(name.to_string(), ty, Box::new(body))
    }
    
    fn app(fun: Term, arg: Term) -> Self {
        Term::App(Box::new(fun), Box::new(arg))
    }
}

// 上下文定义
#[derive(Debug, Clone)]
struct Context {
    bindings: std::collections::HashMap<String, Type>,
}

impl Context {
    fn new() -> Self {
        Context {
            bindings: std::collections::HashMap::new(),
        }
    }
    
    fn extend(&self, name: &str, ty: Type) -> Self {
        let mut new_ctx = self.clone();
        new_ctx.bindings.insert(name.to_string(), ty);
        new_ctx
    }
    
    fn lookup(&self, name: &str) -> Option<&Type> {
        self.bindings.get(name)
    }
}

// 类型检查器
struct TypeChecker;

impl TypeChecker {
    fn type_check(ctx: &Context, term: &Term) -> Result<Type, String> {
        match term {
            Term::Var(name) => {
                ctx.lookup(name)
                    .cloned()
                    .ok_or_else(|| format!("Unbound variable: {}", name))
            }
            
            Term::Abs(name, param_type, body) => {
                let new_ctx = ctx.extend(name, param_type.clone());
                let body_type = Self::type_check(&new_ctx, body)?;
                Ok(Type::arrow(param_type.clone(), body_type))
            }
            
            Term::App(fun, arg) => {
                let fun_type = Self::type_check(ctx, fun)?;
                let arg_type = Self::type_check(ctx, arg)?;
                
                match fun_type {
                    Type::Arrow(domain, codomain) => {
                        if *domain == arg_type {
                            Ok(*codomain)
                        } else {
                            Err(format!("Type mismatch: expected {:?}, got {:?}", domain, arg_type))
                        }
                    }
                    _ => Err("Expected function type".to_string()),
                }
            }
        }
    }
}

// 归约系统
struct Reducer;

impl Reducer {
    fn beta_reduce(term: &Term) -> Option<Term> {
        match term {
            Term::App(fun, arg) => {
                if let Term::Abs(name, _, body) = fun.as_ref() {
                    Some(Self::substitute(body, name, arg))
                } else {
                    None
                }
            }
            _ => None,
        }
    }
    
    fn substitute(term: &Term, name: &str, replacement: &Term) -> Term {
        match term {
            Term::Var(var_name) => {
                if var_name == name {
                    replacement.clone()
                } else {
                    term.clone()
                }
            }
            
            Term::Abs(abs_name, abs_type, body) => {
                if abs_name == name {
                    Term::Abs(abs_name.clone(), abs_type.clone(), body.clone())
                } else {
                    Term::Abs(
                        abs_name.clone(),
                        abs_type.clone(),
                        Box::new(Self::substitute(body, name, replacement)),
                    )
                }
            }
            
            Term::App(fun, arg) => Term::App(
                Box::new(Self::substitute(fun, name, replacement)),
                Box::new(Self::substitute(arg, name, replacement)),
            ),
        }
    }
    
    fn normalize(term: &Term) -> Term {
        let mut current = term.clone();
        while let Some(next) = Self::beta_reduce(&current) {
            current = next;
        }
        current
    }
}

// 示例和测试
fn example_identity_function() {
    // λx:Int.x
    let identity = Term::abs("x", Type::Base("Int".to_string()), Term::var("x"));
    let ctx = Context::new();
    
    match TypeChecker::type_check(&ctx, &identity) {
        Ok(ty) => println!("Identity function type: {:?}", ty),
        Err(e) => println!("Type error: {}", e),
    }
}

fn example_application() {
    // (λx:Int.x) 42
    let identity = Term::abs("x", Type::Base("Int".to_string()), Term::var("x"));
    let forty_two = Term::var("42");
    let app = Term::app(identity, forty_two);
    
    // 这里需要扩展上下文以包含常量
    let mut ctx = Context::new();
    ctx = ctx.extend("42", Type::Base("Int".to_string()));
    
    match TypeChecker::type_check(&ctx, &app) {
        Ok(ty) => println!("Application type: {:?}", ty),
        Err(e) => println!("Type error: {}", e),
    }
}
```

### 2. 类型推断算法

```haskell
-- 类型定义
data Type = Base String | Arrow Type Type deriving (Show, Eq)

-- 项定义
data Term = Var String | Abs String Type Term | App Term Term deriving (Show)

-- 上下文定义
type Context = [(String, Type)]

-- 类型变量
data TypeVar = TypeVar String deriving (Show, Eq)

-- 类型模式
data TypePattern = TypePattern Type | TypeVarPattern TypeVar deriving (Show)

-- 类型推断
typeInference :: Context -> Term -> Either String Type
typeInference ctx term = 
    case term of
        Var x -> 
            case lookup x ctx of
                Just t -> Right t
                Nothing -> Left ("Unbound variable: " ++ x)
        
        Abs x t body -> 
            let newCtx = (x, t) : ctx
                bodyType = typeInference newCtx body
            in case bodyType of
                 Right bt -> Right (Arrow t bt)
                 Left err -> Left err
        
        App fun arg -> 
            let funType = typeInference ctx fun
                argType = typeInference ctx arg
            in case (funType, argType) of
                 (Right (Arrow domain codomain), Right at) ->
                     if domain == at 
                     then Right codomain
                     else Left ("Type mismatch: expected " ++ show domain ++ ", got " ++ show at)
                 (Right ft, _) -> Left ("Expected function type, got " ++ show ft)
                 (Left err, _) -> Left err
                 (_, Left err) -> Left err

-- 归约系统
betaReduce :: Term -> Maybe Term
betaReduce (App (Abs x _ body) arg) = Just (substitute body x arg)
betaReduce _ = Nothing

substitute :: Term -> String -> Term -> Term
substitute term name replacement = 
    case term of
        Var x -> if x == name then replacement else term
        Abs x t body -> 
            if x == name 
            then Abs x t body
            else Abs x t (substitute body name replacement)
        App fun arg -> App (substitute fun name replacement) (substitute arg name replacement)

-- 范式化
normalize :: Term -> Term
normalize term = 
    case betaReduce term of
        Just reduced -> normalize reduced
        Nothing -> term

-- 类型安全验证
typeSafety :: Term -> Bool
typeSafety term = 
    case typeInference [] term of
        Right _ -> True
        Left _ -> False

-- 示例
example1 :: Term
example1 = Abs "x" (Base "Int") (Var "x")  -- λx:Int.x

example2 :: Term
example2 = App example1 (Var "42")  -- (λx:Int.x) 42

-- 测试函数
testTypeInference :: IO ()
testTypeInference = do
    putStrLn "Testing type inference..."
    
    -- 测试恒等函数
    case typeInference [] example1 of
        Right t -> putStrLn $ "Identity function type: " ++ show t
        Left err -> putStrLn $ "Error: " ++ err
    
    -- 测试应用（需要扩展上下文）
    let ctx = [("42", Base "Int")]
    case typeInference ctx example2 of
        Right t -> putStrLn $ "Application type: " ++ show t
        Left err -> putStrLn $ "Error: " ++ err
```

## 📊 **理论分析**

### 1. 类型系统特征

| 特征 | 描述 | 形式化表达 |
|------|------|------------|
| **类型安全** | 类型正确的程序不会产生运行时错误 | $\Gamma \vdash M : \tau \Rightarrow \text{Safe}(M)$ |
| **类型保持性** | 归约保持类型 | $\Gamma \vdash M : \tau \land M \rightarrow M' \Rightarrow \Gamma \vdash M' : \tau$ |
| **进展性** | 类型正确的程序要么是值，要么可以归约 | $\emptyset \vdash M : \tau \Rightarrow \text{Value}(M) \lor \exists M': M \rightarrow M'$ |
| **强标准化** | 所有归约序列都终止 | $\forall M: \text{SN}(M)$ |

### 2. 计算复杂度

| 操作 | 时间复杂度 | 空间复杂度 | 描述 |
|------|------------|------------|------|
| **类型检查** | $O(n^2)$ | $O(n)$ | 检查项的类型 |
| **类型推断** | $O(n^3)$ | $O(n^2)$ | 推断项的类型 |
| **β归约** | $O(n)$ | $O(n)$ | 单步β归约 |
| **范式化** | $O(2^n)$ | $O(n)$ | 计算范式 |

### 3. 表达能力

| 表达能力 | 描述 | 限制 |
|----------|------|------|
| **函数** | 支持高阶函数 | 无法表达递归 |
| **类型** | 支持函数类型 | 无法表达多态 |
| **计算** | 支持函数应用 | 无法表达副作用 |
| **证明** | 支持构造性证明 | 无法表达经典逻辑 |

## 🔄 **持续更新**

本简单类型λ演算体系将持续更新，确保：

- 理论的一致性和完整性
- 形式化的严格性和规范性
- 实现的正确性和效率
- 应用的实用性和有效性

## 📖 **使用指南**

1. **理论学习**：从语法和类型规则开始
2. **形式化学习**：通过代码示例理解实现
3. **性质验证**：验证类型安全和归约性质
4. **实践应用**：在实际编程中应用类型系统

---

**最后更新**：2024-12-20  
**版本**：v1.0.0  
**维护者**：简单类型λ演算重构团队
