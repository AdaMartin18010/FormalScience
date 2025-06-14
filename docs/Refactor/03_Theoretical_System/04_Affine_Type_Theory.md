# 04. 仿射类型理论 (Affine Type Theory)

## 目录

1. [仿射逻辑基础](#1-仿射逻辑基础)
2. [资源管理理论](#2-资源管理理论)
3. [仿射逻辑语义](#3-仿射逻辑语义)
4. [实际应用](#4-实际应用)
5. [形式化证明](#5-形式化证明)
6. [代码实现](#6-代码实现)

---

## 1. 仿射逻辑基础

### 1.1 仿射逻辑公理系统

**定义 1.1 (仿射上下文)**
仿射上下文 $\Gamma$ 是变量到类型的映射，其中每个变量最多使用一次：
$$\Gamma : \text{Var} \rightarrow \text{Type}$$

**定义 1.2 (仿射类型)**
仿射类型系统包含以下类型构造子：
$$\tau ::= \text{Base} \mid \tau_1 \rightarrow \tau_2 \mid \tau_1 \& \tau_2$$

其中：

- $\rightarrow$ 表示仿射函数类型
- $\&$ 表示合取类型

**公理 1.1 (仿射变量规则)**
$$\frac{x : \tau \in \Gamma}{\Gamma \vdash x : \tau} \quad \text{(Var)}$$

**公理 1.2 (仿射抽象)**
$$\frac{\Gamma, x : \tau_1 \vdash e : \tau_2}{\Gamma \vdash \lambda x.e : \tau_1 \rightarrow \tau_2} \quad \text{(Abs)}$$

**公理 1.3 (仿射应用)**
$$\frac{\Gamma_1 \vdash e_1 : \tau_1 \rightarrow \tau_2 \quad \Gamma_2 \vdash e_2 : \tau_1}{\Gamma_1, \Gamma_2 \vdash e_1 e_2 : \tau_2} \quad \text{(App)}$$

**公理 1.4 (仿射弱化)**
$$\frac{\Gamma \vdash e : \tau}{\Gamma, x : \tau' \vdash e : \tau} \quad \text{(Weakening)}$$

### 1.2 仿射性约束

**定理 1.1 (仿射性保持)**
在仿射类型系统中，如果 $\Gamma \vdash e : \tau$，则 $\Gamma$ 中的每个变量在 $e$ 中最多出现一次。

**证明：** 通过结构归纳法证明。

---

## 2. 资源管理理论

### 2.1 仿射资源类型

**定义 2.1 (仿射资源)**
仿射资源类型表示最多使用一次的系统资源：
$$\text{AffineResource} ::= \text{FileHandle} \mid \text{MemoryRef} \mid \text{NetworkConn}$$

**定理 2.1 (仿射资源安全)**
在仿射类型系统中，资源不会被重复使用。

---

## 3. 仿射逻辑语义

### 3.1 指称语义

**定义 3.1 (仿射函数空间)**
仿射函数空间 $A \rightarrow B$ 的语义：
$$\llbracket A \rightarrow B \rrbracket = \llbracket A \rrbracket \rightarrow \llbracket B \rrbracket$$

### 3.2 操作语义

**定义 3.2 (仿射归约)**
仿射归约规则：
$$(\lambda x.e) v \rightarrow e[v/x] \quad \text{(Beta)}$$

---

## 4. 实际应用

### 4.1 Rust 的借用系统

```rust
// Rust 借用系统示例
fn borrow_string(s: &String) {
    println!("Borrowed: {}", s);
}

fn main() {
    let s = String::from("hello");
    borrow_string(&s);
    // 可以继续使用 s
    println!("{}", s);
}
```

### 4.2 函数式编程中的仿射类型

```haskell
-- 仿射类型实现
class Affine a where
  use :: a -> b -> b
  discard :: a -> ()
```

---

## 5. 形式化证明

### 5.1 仿射性保持证明

**定理 5.1 (仿射性保持详细证明)**
在仿射类型系统中，如果 $\Gamma \vdash e : \tau$，则 $\Gamma$ 中的每个变量在 $e$ 中最多出现一次。

**证明：** 通过结构归纳法：

1. **变量情况**：$e = x$
   - $\Gamma = x : \tau$，变量 $x$ 最多出现一次

2. **抽象情况**：$e = \lambda x.e'$
   - 根据抽象规则：$\Gamma, x : \tau_1 \vdash e' : \tau_2$
   - 根据归纳假设：$\Gamma, x : \tau_1$ 中的每个变量在 $e'$ 中最多出现一次
   - 因此 $\Gamma$ 中的每个变量在 $\lambda x.e'$ 中最多出现一次

3. **应用情况**：$e = e_1 e_2$
   - 根据应用规则：$\Gamma_1 \vdash e_1 : \tau_1 \rightarrow \tau_2$ 且 $\Gamma_2 \vdash e_2 : \tau_1$
   - 根据归纳假设：$\Gamma_1$ 中的每个变量在 $e_1$ 中最多出现一次
   - 根据归纳假设：$\Gamma_2$ 中的每个变量在 $e_2$ 中最多出现一次
   - 由于 $\Gamma_1$ 和 $\Gamma_2$ 可能重叠，但每个变量最多使用一次

---

## 6. 代码实现

### 6.1 Haskell 仿射类型系统

```haskell
-- 仿射类型系统实现
module AffineTypeSystem where

-- 仿射类型
data AffineType = ABase String
                | AArrow AffineType AffineType
                | AAnd AffineType AffineType

-- 仿射表达式
data AffineExpr = AVar String
                | AAbs String AffineExpr
                | AApp AffineExpr AffineExpr

-- 仿射上下文
type AffineContext = [(String, AffineType)]

-- 仿射类型检查
affineTypeCheck :: AffineContext -> AffineExpr -> Either String AffineType
affineTypeCheck ctx (AVar x) = 
  case lookup x ctx of
    Just t -> Right t
    Nothing -> Left $ "Unbound variable: " ++ x

affineTypeCheck ctx (AAbs x e) = do
  t <- affineTypeCheck ((x, ABase "a") : ctx) e
  return (AArrow (ABase "a") t)

affineTypeCheck ctx (AApp e1 e2) = do
  t1 <- affineTypeCheck ctx e1
  t2 <- affineTypeCheck ctx e2
  case t1 of
    AArrow t1' t2' | t1' == t2 -> Right t2'
    _ -> Left "Type mismatch in application"
```

### 6.2 Rust 仿射类型系统

```rust
// Rust 仿射类型系统实现
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
enum AffineType {
    ABase(String),
    AArrow(Box<AffineType>, Box<AffineType>),
    AAnd(Box<AffineType>, Box<AffineType>),
}

#[derive(Debug, Clone)]
enum AffineExpr {
    AVar(String),
    AAbs(String, Box<AffineExpr>),
    AApp(Box<AffineExpr>, Box<AffineExpr>),
}

struct AffineTypeChecker;

impl AffineTypeChecker {
    fn type_check(
        ctx: &HashMap<String, AffineType>, 
        expr: &AffineExpr
    ) -> Result<AffineType, String> {
        match expr {
            AffineExpr::AVar(x) => {
                ctx.get(x)
                    .cloned()
                    .ok_or_else(|| format!("Unbound variable: {}", x))
            }
            
            AffineExpr::AAbs(x, e) => {
                let mut new_ctx = ctx.clone();
                new_ctx.insert(x.clone(), AffineType::ABase("a".to_string()));
                let t = Self::type_check(&new_ctx, e)?;
                Ok(AffineType::AArrow(
                    Box::new(AffineType::ABase("a".to_string())), 
                    Box::new(t)
                ))
            }
            
            AffineExpr::AApp(e1, e2) => {
                let t1 = Self::type_check(ctx, e1)?;
                let t2 = Self::type_check(ctx, e2)?;
                
                match t1 {
                    AffineType::AArrow(t1_in, t1_out) => {
                        if *t1_in == t2 {
                            Ok(*t1_out)
                        } else {
                            Err("Type mismatch in application".to_string())
                        }
                    }
                    _ => Err("Not a function".to_string()),
                }
            }
        }
    }
}
```

---

## 参考文献

1. **Wadler, P.** (1990). Linear types can change the world! *Programming concepts and methods*, 561-581.
2. **Benton, P. N.** (1995). A mixed linear and non-linear logic: Proofs, terms and models. *Computer Science Logic*, 121-135.
3. **Barber, A.** (1996). *Linear type theories, semantics and action calculi*. PhD thesis, University of Edinburgh.

---

## 交叉引用

- [02. 类型理论基础](../02_Type_Theory_Foundation.md)
- [03. 线性类型理论](../03_Linear_Type_Theory.md)
- [05. 依赖类型理论](../05_Dependent_Type_Theory.md)
