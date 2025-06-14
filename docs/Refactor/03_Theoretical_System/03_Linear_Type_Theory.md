# 03. 线性类型理论 (Linear Type Theory)

## 目录

1. [线性逻辑基础](#1-线性逻辑基础)
2. [资源管理理论](#2-资源管理理论)
3. [线性逻辑语义](#3-线性逻辑语义)
4. [指数类型系统](#4-指数类型系统)
5. [线性类型扩展](#5-线性类型扩展)
6. [实际应用](#6-实际应用)
7. [形式化证明](#7-形式化证明)
8. [代码实现](#8-代码实现)

---

## 1. 线性逻辑基础

### 1.1 线性逻辑公理系统

**定义 1.1 (线性上下文)**
线性上下文 $\Gamma$ 是变量到类型的映射，其中每个变量必须恰好使用一次：
$$\Gamma : \text{Var} \rightarrow \text{Type}$$

**定义 1.2 (线性类型)**
线性类型系统包含以下类型构造子：
$$\tau ::= \text{Base} \mid \tau_1 \multimap \tau_2 \mid \tau_1 \otimes \tau_2 \mid !\tau$$

其中：

- $\multimap$ 表示线性函数类型
- $\otimes$ 表示张量积类型
- $!$ 表示指数类型（可重复使用）

**公理 1.1 (线性变量规则)**
$$\frac{x : \tau \in \Gamma}{\Gamma \vdash x : \tau} \quad \text{(Var)}$$

**公理 1.2 (线性抽象)**
$$\frac{\Gamma, x : \tau_1 \vdash e : \tau_2}{\Gamma \vdash \lambda x.e : \tau_1 \multimap \tau_2} \quad \text{(Abs)}$$

**公理 1.3 (线性应用)**
$$\frac{\Gamma_1 \vdash e_1 : \tau_1 \multimap \tau_2 \quad \Gamma_2 \vdash e_2 : \tau_1}{\Gamma_1, \Gamma_2 \vdash e_1 e_2 : \tau_2} \quad \text{(App)}$$

**公理 1.4 (张量积引入)**
$$\frac{\Gamma_1 \vdash e_1 : \tau_1 \quad \Gamma_2 \vdash e_2 : \tau_2}{\Gamma_1, \Gamma_2 \vdash (e_1, e_2) : \tau_1 \otimes \tau_2} \quad \text{(Tensor)}$$

**公理 1.5 (张量积消除)**
$$\frac{\Gamma_1 \vdash e_1 : \tau_1 \otimes \tau_2 \quad \Gamma_2, x : \tau_1, y : \tau_2 \vdash e_2 : \tau}{\Gamma_1, \Gamma_2 \vdash \text{let } (x, y) = e_1 \text{ in } e_2 : \tau} \quad \text{(Let)}$$

### 1.2 线性性约束

**定理 1.1 (线性性保持)**
在线性类型系统中，如果 $\Gamma \vdash e : \tau$，则 $\Gamma$ 中的每个变量在 $e$ 中恰好出现一次。

**证明：** 通过结构归纳法证明。对于每个语法构造：

1. **变量**：直接满足线性性
2. **抽象**：通过归纳假设，变量在体中恰好出现一次
3. **应用**：通过上下文分离，确保变量不重复使用
4. **张量积**：通过上下文分离，确保变量不重复使用

**定理 1.2 (上下文分离)**
如果 $\Gamma_1, \Gamma_2 \vdash e : \tau$，则 $\Gamma_1$ 和 $\Gamma_2$ 中的变量集合不相交。

**证明：** 通过结构归纳法：

1. **变量**：$\Gamma = x : \tau$，满足分离
2. **抽象**：$\Gamma, x : \tau_1 \vdash \lambda y.e : \tau_1 \multimap \tau_2$
   - 根据归纳假设：$\Gamma, x : \tau_1, y : \tau_1'$ 分离
   - 因此 $\Gamma$ 和 $x : \tau_1$ 分离
3. **应用**：$\Gamma_1, \Gamma_2 \vdash e_1 e_2 : \tau_2$
   - 根据归纳假设：$\Gamma_1$ 和 $\Gamma_2$ 分离

---

## 2. 资源管理理论

### 2.1 资源类型系统

**定义 2.1 (资源类型)**
资源类型表示需要精确管理的系统资源：
$$\text{Resource} ::= \text{FileHandle} \mid \text{MemoryRef} \mid \text{NetworkConn} \mid \text{DatabaseConn}$$

**定义 2.2 (资源操作)**
资源操作包括创建、使用和销毁：

```haskell
data ResourceOp a where
  Create :: ResourceType -> ResourceOp Resource
  Use    :: Resource -> (a -> b) -> ResourceOp b
  Destroy :: Resource -> ResourceOp ()
```

**定理 2.1 (资源安全)**
在线性类型系统中，资源不会被重复释放或遗忘。

**证明：** 通过线性性约束：

1. 每个资源变量必须恰好使用一次
2. 资源销毁操作消耗资源变量
3. 无法重复访问已销毁的资源

### 2.2 内存管理

**定义 2.3 (线性引用)**
线性引用确保内存安全：

```haskell
data LinearRef a where
  NewRef :: a -> LinearRef a
  ReadRef :: LinearRef a -> (a, LinearRef a)
  WriteRef :: LinearRef a -> a -> LinearRef a
  FreeRef :: LinearRef a -> ()
```

**定理 2.2 (内存安全)**
线性引用系统保证：

1. 不会出现悬空指针
2. 不会重复释放内存
3. 不会出现数据竞争

**证明：** 通过线性类型系统的性质：

1. 每个引用最多使用一次
2. 读取操作返回新的引用
3. 释放操作消耗引用

### 2.3 文件系统安全

**定义 2.4 (线性文件句柄)**:

```haskell
data LinearFileHandle where
  OpenFile :: FilePath -> Mode -> LinearFileHandle
  ReadFile :: LinearFileHandle -> (ByteString, LinearFileHandle)
  WriteFile :: LinearFileHandle -> ByteString -> LinearFileHandle
  CloseFile :: LinearFileHandle -> ()
```

**定理 2.3 (文件系统安全)**
线性文件句柄系统保证：

1. 文件不会被重复关闭
2. 已关闭的文件无法访问
3. 文件操作是原子的

---

## 3. 线性逻辑语义

### 3.1 指称语义

**定义 3.1 (线性函数空间)**
线性函数空间 $A \multimap B$ 的语义：
$$\llbracket A \multimap B \rrbracket = \llbracket A \rrbracket \rightarrow \llbracket B \rrbracket$$

**定义 3.2 (张量积语义)**
张量积 $A \otimes B$ 的语义：
$$\llbracket A \otimes B \rrbracket = \llbracket A \rrbracket \times \llbracket B \rrbracket$$

**定义 3.3 (指数类型语义)**
指数类型 $!A$ 的语义：
$$\llbracket !A \rrbracket = \text{Comonad}(\llbracket A \rrbracket)$$

### 3.2 操作语义

**定义 3.4 (线性归约)**
线性归约规则：
$$(\lambda x.e) v \rightarrow e[v/x] \quad \text{(Beta)}$$
$$\text{let } (x, y) = (e_1, e_2) \text{ in } e \rightarrow e[e_1/x, e_2/y] \quad \text{(Let)}$$

**定理 3.1 (线性归约保持类型)**
如果 $\Gamma \vdash e : \tau$ 且 $e \rightarrow e'$，则 $\Gamma \vdash e' : \tau$。

**证明：** 通过结构归纳法：

1. **Beta归约**：$(\lambda x.e) v \rightarrow e[v/x]$
   - 假设：$\Gamma_1, \Gamma_2 \vdash (\lambda x.e) v : \tau_2$
   - 根据App规则：$\Gamma_1 \vdash \lambda x.e : \tau_1 \multimap \tau_2$ 且 $\Gamma_2 \vdash v : \tau_1$
   - 根据Abs规则：$\Gamma_1, x : \tau_1 \vdash e : \tau_2$
   - 通过替换引理：$\Gamma_1, \Gamma_2 \vdash e[v/x] : \tau_2$

2. **Let归约**：$\text{let } (x, y) = (e_1, e_2) \text{ in } e \rightarrow e[e_1/x, e_2/y]$
   - 类似证明

---

## 4. 指数类型系统

### 4.1 指数类型规则

**公理 4.1 (弱化)**
$$\frac{\Gamma \vdash e : \tau}{\Gamma, x : !\tau \vdash e : \tau} \quad \text{(Weakening)}$$

**公理 4.2 (收缩)**
$$\frac{\Gamma, x : !\tau, y : !\tau \vdash e : \sigma}{\Gamma, z : !\tau \vdash e[z/x, z/y] : \sigma} \quad \text{(Contraction)}$$

**公理 4.3 (提升)**
$$\frac{!\Gamma \vdash e : \tau}{!\Gamma \vdash !e : !\tau} \quad \text{(Promotion)}$$

**公理 4.4 (去提升)**
$$\frac{\Gamma \vdash e : !\tau}{\Gamma \vdash \text{derelict}(e) : \tau} \quad \text{(Dereliction)}$$

### 4.2 指数类型的语义

**定义 4.1 (指数类型语义)**
指数类型 $!A$ 的语义：
$$\llbracket !A \rrbracket = \text{Comonad}(\llbracket A \rrbracket)$$

**定理 4.1 (指数类型性质)**
指数类型满足：

1. 可重复使用
2. 支持弱化和收缩
3. 形成余单子结构

**证明：** 通过余单子公理：

1. **余单位**：$\text{derelict} : !A \rightarrow A$
2. **余乘法**：$\text{dig} : !A \rightarrow !!A$
3. **自然性**：对于 $f : A \rightarrow B$，有 $!f : !A \rightarrow !B$

### 4.3 指数类型的实现

```haskell
-- 指数类型实现
class Comonad w where
  extract :: w a -> a
  duplicate :: w a -> w (w a)
  extend :: (w a -> b) -> w a -> w b

-- 指数类型包装器
newtype Bang a = Bang { unBang :: a }

instance Comonad Bang where
  extract (Bang a) = a
  duplicate (Bang a) = Bang (Bang a)
  extend f (Bang a) = Bang (f (Bang a))

-- 指数类型操作
derelict :: Bang a -> a
derelict = extract

promote :: a -> Bang a
promote = Bang

dig :: Bang a -> Bang (Bang a)
dig = duplicate
```

---

## 5. 线性类型扩展

### 5.1 仿射类型

**定义 5.1 (仿射类型)**
仿射类型允许变量最多使用一次：
$$\tau ::= \text{Base} \mid \tau_1 \rightarrow \tau_2 \mid \tau_1 \& \tau_2$$

**公理 5.1 (仿射弱化)**
$$\frac{\Gamma \vdash e : \tau}{\Gamma, x : \tau' \vdash e : \tau} \quad \text{(AffineWeakening)}$$

**公理 5.2 (仿射应用)**
$$\frac{\Gamma_1 \vdash e_1 : \tau_1 \rightarrow \tau_2 \quad \Gamma_2 \vdash e_2 : \tau_1}{\Gamma_1, \Gamma_2 \vdash e_1 e_2 : \tau_2} \quad \text{(AffineApp)}$$

### 5.2 相关类型

**定义 5.2 (相关类型)**
相关类型允许变量至少使用一次：
$$\tau ::= \text{Base} \mid \tau_1 \rightarrow \tau_2 \mid \tau_1 \oplus \tau_2$$

**公理 5.3 (相关抽象)**
$$\frac{\Gamma, x : \tau_1 \vdash e : \tau_2 \quad x \in \text{FV}(e)}{\Gamma \vdash \lambda x.e : \tau_1 \rightarrow \tau_2} \quad \text{(RelevantAbs)}$$

### 5.3 混合类型系统

**定义 5.3 (混合类型)**
混合类型系统结合线性、仿射和相关类型：
$$\tau ::= \text{Base} \mid \tau_1 \multimap \tau_2 \mid \tau_1 \rightarrow \tau_2 \mid \tau_1 \rightarrow \tau_2 \mid \tau_1 \otimes \tau_2 \mid \tau_1 \& \tau_2 \mid \tau_1 \oplus \tau_2 \mid !\tau$$

---

## 6. 实际应用

### 6.1 Rust 的所有权系统

Rust 的所有权系统基于线性类型理论：

```rust
// Rust 所有权系统示例
fn consume_string(s: String) {
    // s 被消费，无法再次使用
    println!("Consumed: {}", s);
}

fn main() {
    let s = String::from("hello");
    consume_string(s);
    // 这里无法使用 s，因为它已经被消费
    // println!("{}", s); // 编译错误
}

// 借用系统
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

**定理 6.1 (Rust 内存安全)**
Rust 的所有权系统保证内存安全。

**证明：** 通过线性类型系统的性质：

1. 每个值最多有一个所有者
2. 移动操作转移所有权
3. 借用检查防止数据竞争

### 6.2 函数式编程中的线性类型

**定义 6.1 (线性函数)**

```haskell
class Linear a where
  consume :: a -> ()
  duplicate :: a -> (a, a)  -- 仅对非线性类型可用

-- 线性类型实例
instance Linear (LinearRef a) where
  consume ref = freeRef ref
  duplicate _ = error "Cannot duplicate linear reference"

-- 非线性类型实例
instance Linear Int where
  consume _ = ()
  duplicate x = (x, x)
```

**定理 6.2 (线性函数性质)**
线性函数满足：

1. 每个参数恰好使用一次
2. 不支持重复使用
3. 支持资源管理

### 6.3 并发编程中的线性类型

```haskell
-- 线性通道
data LinearChannel a where
  NewChannel :: LinearChannel a
  Send :: LinearChannel a -> a -> ()
  Receive :: LinearChannel a -> (a, LinearChannel a)

-- 线性线程
data LinearThread a where
  Spawn :: (() -> a) -> LinearThread a
  Join :: LinearThread a -> a

-- 使用示例
example :: IO ()
example = do
  let ch = newChannel
  let t1 = spawn $ do
        send ch "hello"
  let t2 = spawn $ do
        (msg, ch') = receive ch
        return msg
  msg <- join t2
  print msg
```

---

## 7. 形式化证明

### 7.1 线性性保持证明

**定理 7.1 (线性性保持详细证明)**
在线性类型系统中，如果 $\Gamma \vdash e : \tau$，则 $\Gamma$ 中的每个变量在 $e$ 中恰好出现一次。

**证明：** 通过结构归纳法：

1. **变量情况**：$e = x$
   - $\Gamma = x : \tau$，变量 $x$ 恰好出现一次

2. **抽象情况**：$e = \lambda x.e'$
   - 根据抽象规则：$\Gamma, x : \tau_1 \vdash e' : \tau_2$
   - 根据归纳假设：$\Gamma, x : \tau_1$ 中的每个变量在 $e'$ 中恰好出现一次
   - 因此 $\Gamma$ 中的每个变量在 $\lambda x.e'$ 中恰好出现一次

3. **应用情况**：$e = e_1 e_2$
   - 根据应用规则：$\Gamma_1 \vdash e_1 : \tau_1 \multimap \tau_2$ 且 $\Gamma_2 \vdash e_2 : \tau_1$
   - 根据归纳假设：$\Gamma_1$ 中的每个变量在 $e_1$ 中恰好出现一次
   - 根据归纳假设：$\Gamma_2$ 中的每个变量在 $e_2$ 中恰好出现一次
   - 由于 $\Gamma_1$ 和 $\Gamma_2$ 分离，每个变量在 $e_1 e_2$ 中恰好出现一次

4. **张量积情况**：$e = (e_1, e_2)$
   - 类似证明

### 7.2 资源安全证明

**定理 7.2 (资源安全详细证明)**
在线性类型系统中，资源不会被重复释放或遗忘。

**证明：** 通过线性性约束和资源操作规则：

1. **资源创建**：$\vdash \text{create} : \text{Resource}$
   - 创建的资源必须被使用

2. **资源使用**：$\text{Resource} \multimap (\text{Resource} \multimap \tau) \multimap \tau$
   - 使用操作消耗资源

3. **资源销毁**：$\text{Resource} \multimap \text{Unit}$
   - 销毁操作消耗资源

4. **线性性保证**：每个资源变量恰好使用一次
   - 无法重复访问已销毁的资源
   - 无法遗忘未销毁的资源

---

## 8. 代码实现

### 8.1 Haskell 线性类型系统

```haskell
-- 线性类型系统实现
module LinearTypeSystem where

-- 线性类型
data LinearType = LBase String
                | LArrow LinearType LinearType
                | LTensor LinearType LinearType
                | LBang LinearType

-- 线性表达式
data LinearExpr = LVar String
                | LAbs String LinearExpr
                | LApp LinearExpr LinearExpr
                | LTensor LinearExpr LinearExpr
                | LLet String String LinearExpr LinearExpr
                | LBang LinearExpr
                | LDerelict LinearExpr

-- 线性上下文
type LinearContext = [(String, LinearType)]

-- 线性类型检查
linearTypeCheck :: LinearContext -> LinearExpr -> Either String LinearType
linearTypeCheck ctx (LVar x) = 
  case lookup x ctx of
    Just t -> Right t
    Nothing -> Left $ "Unbound variable: " ++ x

linearTypeCheck ctx (LAbs x e) = do
  t <- linearTypeCheck ((x, LBase "a") : ctx) e
  return (LArrow (LBase "a") t)

linearTypeCheck ctx (LApp e1 e2) = do
  t1 <- linearTypeCheck ctx e1
  t2 <- linearTypeCheck ctx e2
  case t1 of
    LArrow t1' t2' | t1' == t2 -> Right t2'
    _ -> Left "Type mismatch in application"

linearTypeCheck ctx (LTensor e1 e2) = do
  t1 <- linearTypeCheck ctx e1
  t2 <- linearTypeCheck ctx e2
  return (LTensor t1 t2)

linearTypeCheck ctx (LLet x y e1 e2) = do
  t1 <- linearTypeCheck ctx e1
  case t1 of
    LTensor t1' t2' -> do
      t <- linearTypeCheck ((x, t1') : (y, t2') : ctx) e2
      return t
    _ -> Left "Expected tensor type in let"

linearTypeCheck ctx (LBang e) = do
  t <- linearTypeCheck ctx e
  return (LBang t)

linearTypeCheck ctx (LDerelict e) = do
  t <- linearTypeCheck ctx e
  case t of
    LBang t' -> Right t'
    _ -> Left "Expected bang type in derelict"

-- 线性求值
data LinearValue = LClosure String LinearExpr LinearContext
                | LTensorVal LinearValue LinearValue
                | LBangVal LinearValue

linearEval :: LinearContext -> LinearExpr -> Either String LinearValue
linearEval ctx (LVar x) = 
  case lookup x ctx of
    Just (LClosure _ _ _) -> Left "Cannot evaluate type"
    _ -> Left $ "Unbound variable: " ++ x

linearEval ctx (LAbs x e) = Right (LClosure x e ctx)
linearEval ctx (LApp e1 e2) = do
  v1 <- linearEval ctx e1
  v2 <- linearEval ctx e2
  case v1 of
    LClosure x body env -> linearEval ((x, v2) : env) body
    _ -> Left "Not a function"

linearEval ctx (LTensor e1 e2) = do
  v1 <- linearEval ctx e1
  v2 <- linearEval ctx e2
  return (LTensorVal v1 v2)

linearEval ctx (LLet x y e1 e2) = do
  v1 <- linearEval ctx e1
  case v1 of
    LTensorVal v1' v2' -> linearEval ((x, v1') : (y, v2') : ctx) e2
    _ -> Left "Expected tensor value in let"

linearEval ctx (LBang e) = do
  v <- linearEval ctx e
  return (LBangVal v)

linearEval ctx (LDerelict e) = do
  v <- linearEval ctx e
  case v of
    LBangVal v' -> return v'
    _ -> Left "Expected bang value in derelict"
```

### 8.2 Rust 线性类型系统

```rust
// Rust 线性类型系统实现
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
enum LinearType {
    LBase(String),
    LArrow(Box<LinearType>, Box<LinearType>),
    LTensor(Box<LinearType>, Box<LinearType>),
    LBang(Box<LinearType>),
}

#[derive(Debug, Clone)]
enum LinearExpr {
    LVar(String),
    LAbs(String, Box<LinearExpr>),
    LApp(Box<LinearExpr>, Box<LinearExpr>),
    LTensor(Box<LinearExpr>, Box<LinearExpr>),
    LLet(String, String, Box<LinearExpr>, Box<LinearExpr>),
    LBang(Box<LinearExpr>),
    LDerelict(Box<LinearExpr>),
}

#[derive(Debug, Clone)]
enum LinearValue {
    LClosure(String, Box<LinearExpr>, HashMap<String, LinearValue>),
    LTensorVal(Box<LinearValue>, Box<LinearValue>),
    LBangVal(Box<LinearValue>),
}

#[derive(Debug)]
enum LinearTypeError {
    UnboundVariable(String),
    TypeMismatch(LinearType, LinearType),
    NotAFunction(LinearType),
    ExpectedTensor(LinearType),
    ExpectedBang(LinearType),
}

struct LinearTypeChecker;

impl LinearTypeChecker {
    fn type_check(
        ctx: &HashMap<String, LinearType>, 
        expr: &LinearExpr
    ) -> Result<LinearType, LinearTypeError> {
        match expr {
            LinearExpr::LVar(x) => {
                ctx.get(x)
                    .cloned()
                    .ok_or(LinearTypeError::UnboundVariable(x.clone()))
            }
            
            LinearExpr::LAbs(x, e) => {
                let mut new_ctx = ctx.clone();
                new_ctx.insert(x.clone(), LinearType::LBase("a".to_string()));
                let t = Self::type_check(&new_ctx, e)?;
                Ok(LinearType::LArrow(
                    Box::new(LinearType::LBase("a".to_string())), 
                    Box::new(t)
                ))
            }
            
            LinearExpr::LApp(e1, e2) => {
                let t1 = Self::type_check(ctx, e1)?;
                let t2 = Self::type_check(ctx, e2)?;
                
                match t1 {
                    LinearType::LArrow(t1_in, t1_out) => {
                        if *t1_in == t2 {
                            Ok(*t1_out)
                        } else {
                            Err(LinearTypeError::TypeMismatch(*t1_in, t2))
                        }
                    }
                    _ => Err(LinearTypeError::NotAFunction(t1)),
                }
            }
            
            LinearExpr::LTensor(e1, e2) => {
                let t1 = Self::type_check(ctx, e1)?;
                let t2 = Self::type_check(ctx, e2)?;
                Ok(LinearType::LTensor(Box::new(t1), Box::new(t2)))
            }
            
            LinearExpr::LLet(x, y, e1, e2) => {
                let t1 = Self::type_check(ctx, e1)?;
                match t1 {
                    LinearType::LTensor(t1', t2') => {
                        let mut new_ctx = ctx.clone();
                        new_ctx.insert(x.clone(), *t1');
                        new_ctx.insert(y.clone(), *t2');
                        Self::type_check(&new_ctx, e2)
                    }
                    _ => Err(LinearTypeError::ExpectedTensor(t1)),
                }
            }
            
            LinearExpr::LBang(e) => {
                let t = Self::type_check(ctx, e)?;
                Ok(LinearType::LBang(Box::new(t)))
            }
            
            LinearExpr::LDerelict(e) => {
                let t = Self::type_check(ctx, e)?;
                match t {
                    LinearType::LBang(t') => Ok(*t'),
                    _ => Err(LinearTypeError::ExpectedBang(t)),
                }
            }
        }
    }
}

struct LinearEvaluator;

impl LinearEvaluator {
    fn eval(
        ctx: &HashMap<String, LinearValue>, 
        expr: &LinearExpr
    ) -> Result<LinearValue, String> {
        match expr {
            LinearExpr::LVar(x) => {
                ctx.get(x)
                    .cloned()
                    .ok_or_else(|| format!("Unbound variable: {}", x))
            }
            
            LinearExpr::LAbs(x, e) => {
                Ok(LinearValue::LClosure(x.clone(), e.clone(), ctx.clone()))
            }
            
            LinearExpr::LApp(e1, e2) => {
                let v1 = Self::eval(ctx, e1)?;
                let v2 = Self::eval(ctx, e2)?;
                
                match v1 {
                    LinearValue::LClosure(x, body, env) => {
                        let mut new_env = env;
                        new_env.insert(x, v2);
                        Self::eval(&new_env, &body)
                    }
                    _ => Err("Not a function".to_string()),
                }
            }
            
            LinearExpr::LTensor(e1, e2) => {
                let v1 = Self::eval(ctx, e1)?;
                let v2 = Self::eval(ctx, e2)?;
                Ok(LinearValue::LTensorVal(Box::new(v1), Box::new(v2)))
            }
            
            LinearExpr::LLet(x, y, e1, e2) => {
                let v1 = Self::eval(ctx, e1)?;
                match v1 {
                    LinearValue::LTensorVal(v1', v2') => {
                        let mut new_ctx = ctx.clone();
                        new_ctx.insert(x.clone(), *v1');
                        new_ctx.insert(y.clone(), *v2');
                        Self::eval(&new_ctx, e2)
                    }
                    _ => Err("Expected tensor value in let".to_string()),
                }
            }
            
            LinearExpr::LBang(e) => {
                let v = Self::eval(ctx, e)?;
                Ok(LinearValue::LBangVal(Box::new(v)))
            }
            
            LinearExpr::LDerelict(e) => {
                let v = Self::eval(ctx, e)?;
                match v {
                    LinearValue::LBangVal(v') => Ok(*v'),
                    _ => Err("Expected bang value in derelict".to_string()),
                }
            }
        }
    }
}

// 使用示例
fn main() {
    // 线性类型检查示例
    let ctx: HashMap<String, LinearType> = HashMap::new();
    let expr = LinearExpr::LApp(
        Box::new(LinearExpr::LAbs("x".to_string(), Box::new(LinearExpr::LVar("x".to_string())))),
        Box::new(LinearExpr::LVar("y".to_string()))
    );
    
    match LinearTypeChecker::type_check(&ctx, &expr) {
        Ok(t) => println!("Type: {:?}", t),
        Err(e) => println!("Type error: {:?}", e),
    }
    
    // 线性求值示例
    let ctx: HashMap<String, LinearValue> = HashMap::new();
    let expr = LinearExpr::LTensor(
        Box::new(LinearExpr::LVar("x".to_string())),
        Box::new(LinearExpr::LVar("y".to_string()))
    );
    
    match LinearEvaluator::eval(&ctx, &expr) {
        Ok(v) => println!("Value: {:?}", v),
        Err(e) => println!("Evaluation error: {}", e),
    }
}
```

---

## 参考文献

1. **Girard, J. Y.** (1987). Linear logic. *Theoretical computer science*, 50(1), 1-101.
2. **Wadler, P.** (1990). Linear types can change the world! *Programming concepts and methods*, 561-581.
3. **Abramsky, S.** (1993). Computational interpretations of linear logic. *Theoretical Computer Science*, 111(1-2), 3-57.
4. **Benton, P. N.** (1995). A mixed linear and non-linear logic: Proofs, terms and models. *Computer Science Logic*, 121-135.
5. **Barber, A.** (1996). *Linear type theories, semantics and action calculi*. PhD thesis, University of Edinburgh.
6. **Mazurak, K., & Zdancewic, S.** (2010). Fable: A language for enforcing user-defined security policies. *IEEE Symposium on Security and Privacy*, 369-383.
7. **Morris, J. G.** (2016). *The best of both worlds: linear functional programming without compromise*. PhD thesis, University of Edinburgh.
8. **Bernardy, J. P., Boespflug, M., Newton, R. R., Jones, S. P., & Spiwack, A.** (2018). Linear haskell: practical linearity in a higher-order polymorphic language. *ACM SIGPLAN Notices*, 53(10), 5-29.

---

## 交叉引用

- [02. 类型理论基础](../02_Type_Theory_Foundation.md)
- [04. 仿射类型理论](../04_Affine_Type_Theory.md)
- [05. 依赖类型理论](../05_Dependent_Type_Theory.md)
- [06. 高阶类型理论](../06_Higher_Order_Type_Theory.md)
- [07. 量子类型理论](../07_Quantum_Type_Theory.md)
- [08. 时态类型理论](../08_Temporal_Type_Theory.md)
- [09. 分布式类型理论](../09_Distributed_Type_Theory.md)
- [10. 控制论类型理论](../10_Control_Theory_Type_Theory.md)
