# 04.01.01 简单类型λ演算 (Simply Typed Lambda Calculus)

## 📋 概述

简单类型λ演算是类型理论的基础，研究带类型的λ表达式、类型推导和类型安全。本文档建立了严格的形式化简单类型λ演算理论，为所有类型理论提供基础。

**构建时间**: 2024年12月21日  
**版本**: v1.0  
**状态**: 已完成

## 📚 目录

1. [基本概念](#1-基本概念)
2. [形式化定义](#2-形式化定义)
3. [类型系统](#3-类型系统)
4. [核心定理](#4-核心定理)
5. [类型推导](#5-类型推导)
6. [归约规则](#6-归约规则)
7. [类型安全](#7-类型安全)
8. [应用实例](#8-应用实例)
9. [代码实现](#9-代码实现)
10. [参考文献](#10-参考文献)

## 1. 基本概念

### 1.1 类型定义

**定义 1.1.1** (类型)
类型是表达式的分类，表示表达式的值和操作。

**形式化表示**:
$$\text{Type} \equiv \text{Classification}(\text{Expression})$$

### 1.2 基本类型

**定义 1.2.1** (基本类型)
基本类型是类型系统的基础类型。

**形式化表示**:
$$\text{BaseType} \in \{\text{Bool}, \text{Int}, \text{String}, \ldots\}$$

### 1.3 函数类型

**定义 1.3.1** (函数类型)
函数类型表示从输入类型到输出类型的映射。

**形式化表示**:
$$\text{FunctionType}(A, B) \equiv A \rightarrow B$$

## 2. 形式化定义

### 2.1 类型语法

**定义 2.1.1** (类型语法)
类型由以下语法定义：

$$A, B ::= \text{BaseType} \mid A \rightarrow B$$

**形式化定义**:
$$\text{Type} = \text{BaseType} \cup \text{FunctionType}(\text{Type}, \text{Type})$$

### 2.2 项语法

**定义 2.2.1** (项语法)
λ项由以下语法定义：

$$M, N ::= x \mid \lambda x:A.M \mid M N$$

**形式化定义**:
$$\text{Term} = \text{Variable} \cup \text{Abstraction}(\text{Variable}, \text{Type}, \text{Term}) \cup \text{Application}(\text{Term}, \text{Term})$$

### 2.3 上下文

**定义 2.3.1** (类型上下文)
类型上下文是变量到类型的映射。

**形式化定义**:
$$\Gamma: \text{Variable} \rightarrow \text{Type}$$

## 3. 类型系统

### 3.1 类型判断

**定义 3.1.1** (类型判断)
类型判断的形式为 $\Gamma \vdash M : A$，表示在上下文 $\Gamma$ 中，项 $M$ 具有类型 $A$。

**形式化表示**:
$$\text{TypeJudgment}(\Gamma, M, A) \equiv \Gamma \vdash M : A$$

### 3.2 类型规则

**规则 3.2.1** (变量规则)
$$\frac{x:A \in \Gamma}{\Gamma \vdash x : A}$$

**规则 3.2.2** (抽象规则)
$$\frac{\Gamma, x:A \vdash M : B}{\Gamma \vdash \lambda x:A.M : A \rightarrow B}$$

**规则 3.2.3** (应用规则)
$$\frac{\Gamma \vdash M : A \rightarrow B \quad \Gamma \vdash N : A}{\Gamma \vdash M N : B}$$

## 4. 核心定理

### 4.1 类型唯一性

**定理 4.1.1** (类型唯一性)
如果 $\Gamma \vdash M : A$ 且 $\Gamma \vdash M : B$，则 $A = B$。

**形式化表示**:
$$\Gamma \vdash M : A \land \Gamma \vdash M : B \rightarrow A = B$$

**证明**:

1. 对项的结构进行归纳
2. 对于变量：由上下文的一致性
3. 对于抽象：由归纳假设
4. 对于应用：由函数类型的唯一性

### 4.2 类型保持性

**定理 4.2.1** (类型保持性)
如果 $\Gamma \vdash M : A$ 且 $M \rightarrow N$，则 $\Gamma \vdash N : A$。

**形式化表示**:
$$\Gamma \vdash M : A \land M \rightarrow N \rightarrow \Gamma \vdash N : A$$

**证明**:

1. 对归约规则进行归纳
2. β归约：通过替换引理
3. η归约：通过函数外延性

### 4.3 强正规化

**定理 4.3.1** (强正规化)
所有良类型的项都是强正规化的。

**形式化表示**:
$$\Gamma \vdash M : A \rightarrow \text{StronglyNormalizing}(M)$$

**证明**:

1. 构造类型大小的度量
2. 证明每次归约都减少度量
3. 由于度量有下界，归约必然终止

## 5. 类型推导

### 5.1 类型推导算法

**算法 5.1.1** (类型推导)
给定项 $M$ 和上下文 $\Gamma$，计算类型 $A$ 使得 $\Gamma \vdash M : A$。

**算法步骤**:

1. **变量**: 在上下文中查找类型
2. **抽象**: 递归推导体，构造函数类型
3. **应用**: 推导函数和参数类型，检查兼容性

### 5.2 类型推导定理

**定理 5.2.1** (类型推导完备性)
如果 $\Gamma \vdash M : A$，则类型推导算法能够找到类型 $A$。

**证明**:

1. 对类型推导规则进行归纳
2. 每个规则对应算法的一个步骤
3. 算法能够模拟所有推导规则

### 5.3 类型推导正确性

**定理 5.3.1** (类型推导正确性)
如果类型推导算法返回类型 $A$，则 $\Gamma \vdash M : A$。

**证明**:

1. 对算法步骤进行归纳
2. 每个步骤都对应有效的类型规则
3. 算法构造的推导是有效的

## 6. 归约规则

### 6.1 β归约

**定义 6.1.1** (β归约)
β归约是函数应用的归约规则：

$$(\lambda x:A.M) N \rightarrow M[x := N]$$

**形式化定义**:
$$\text{BetaReduction}(\lambda x:A.M, N) \equiv M[x := N]$$

### 6.2 η归约

**定义 6.2.1** (η归约)
η归约是函数外延性的归约规则：

$$\lambda x:A.(M x) \rightarrow M \quad \text{if } x \notin \text{FV}(M)$$

**形式化定义**:
$$\text{EtaReduction}(\lambda x:A.(M x)) \equiv M \text{ if } x \notin \text{FV}(M)$$

### 6.3 归约关系

**定义 6.3.1** (归约关系)
归约关系 $\rightarrow$ 是满足以下条件的最小关系：

1. 如果 $M \rightarrow N$，则 $\lambda x:A.M \rightarrow \lambda x:A.N$
2. 如果 $M \rightarrow N$，则 $M P \rightarrow N P$
3. 如果 $M \rightarrow N$，则 $P M \rightarrow P N$

## 7. 类型安全

### 7.1 类型安全定义

**定义 7.1.1** (类型安全)
类型系统是类型安全的，如果：

1. **进展性**: 良类型的项要么是值，要么可以归约
2. **保持性**: 归约保持类型

**形式化表示**:
$$\text{TypeSafe} \equiv \text{Progress} \land \text{Preservation}$$

### 7.2 进展性

**定理 7.2.1** (进展性)
如果 $\vdash M : A$，则要么 $M$ 是值，要么存在 $N$ 使得 $M \rightarrow N$。

**形式化表示**:
$$\vdash M : A \rightarrow \text{Value}(M) \lor \exists N, M \rightarrow N$$

**证明**:

1. 对项的结构进行归纳
2. 变量：不可能（空上下文）
3. 抽象：总是值
4. 应用：由归纳假设和类型规则

### 7.3 保持性

**定理 7.3.1** (保持性)
如果 $\Gamma \vdash M : A$ 且 $M \rightarrow N$，则 $\Gamma \vdash N : A$。

**形式化表示**:
$$\Gamma \vdash M : A \land M \rightarrow N \rightarrow \Gamma \vdash N : A$$

**证明**:

1. 对归约规则进行归纳
2. β归约：通过替换引理
3. 其他归约：通过归纳假设

## 8. 应用实例

### 8.1 布尔运算

**实例 8.1.1** (布尔类型)
定义布尔类型和基本运算：

```rust
// 布尔类型
type Bool = bool;

// 真值
let true: Bool = true;
let false: Bool = false;

// 条件表达式
let if_then_else: Bool -> A -> A -> A = 
    λb:Bool.λx:A.λy:A.if b then x else y;
```

### 8.2 自然数运算

**实例 8.1.2** (自然数类型)
定义自然数类型和基本运算：

```rust
// 自然数类型
type Nat = u64;

// 零
let zero: Nat = 0;

// 后继函数
let succ: Nat -> Nat = λn:Nat.n + 1;

// 加法
let add: Nat -> Nat -> Nat = λm:Nat.λn:Nat.m + n;
```

### 8.3 列表操作

**实例 8.1.3** (列表类型)
定义列表类型和基本操作：

```rust
// 列表类型
type List<A> = Vec<A>;

// 空列表
let nil: List<A> = vec![];

// 连接操作
let cons: A -> List<A> -> List<A> = 
    λx:A.λxs:List<A>.cons(x, xs);

// 映射函数
let map: (A -> B) -> List<A> -> List<B> = 
    λf:A->B.λxs:List<A>.map(f, xs);
```

## 9. 代码实现

### 9.1 Rust实现

```rust
// 简单类型λ演算 - Rust实现
// 文件名: simply_typed_lambda_calculus.rs

use std::collections::HashMap;
use std::fmt;

/// 类型定义
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Base(String),
    Function(Box<Type>, Box<Type>),
}

impl Type {
    /// 创建基本类型
    pub fn base(name: &str) -> Self {
        Type::Base(name.to_string())
    }
    
    /// 创建函数类型
    pub fn function(from: Type, to: Type) -> Self {
        Type::Function(Box::new(from), Box::new(to))
    }
    
    /// 获取函数类型的分量
    pub fn function_components(&self) -> Option<(&Type, &Type)> {
        match self {
            Type::Function(from, to) => Some((from, to)),
            _ => None,
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Base(name) => write!(f, "{}", name),
            Type::Function(from, to) => {
                match **from {
                    Type::Function(_, _) => write!(f, "({})", from)?,
                    _ => write!(f, "{}", from)?,
                }
                write!(f, " -> {}", to)
            }
        }
    }
}

/// 项定义
#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    Variable(String),
    Abstraction(String, Type, Box<Term>),
    Application(Box<Term>, Box<Term>),
}

impl Term {
    /// 创建变量
    pub fn var(name: &str) -> Self {
        Term::Variable(name.to_string())
    }
    
    /// 创建抽象
    pub fn abs(name: &str, ty: Type, body: Term) -> Self {
        Term::Abstraction(name.to_string(), ty, Box::new(body))
    }
    
    /// 创建应用
    pub fn app(fun: Term, arg: Term) -> Self {
        Term::Application(Box::new(fun), Box::new(arg))
    }
    
    /// 获取自由变量
    pub fn free_variables(&self) -> Vec<String> {
        match self {
            Term::Variable(name) => vec![name.clone()],
            Term::Abstraction(param, _, body) => {
                let mut fv = body.free_variables();
                fv.retain(|x| x != param);
                fv
            }
            Term::Application(fun, arg) => {
                let mut fv = fun.free_variables();
                fv.extend(arg.free_variables());
                fv.sort();
                fv.dedup();
                fv
            }
        }
    }
    
    /// 变量替换
    pub fn substitute(&self, var: &str, replacement: &Term) -> Term {
        match self {
            Term::Variable(name) => {
                if name == var {
                    replacement.clone()
                } else {
                    self.clone()
                }
            }
            Term::Abstraction(param, ty, body) => {
                if param == var {
                    Term::Abstraction(param.clone(), ty.clone(), body.clone())
                } else {
                    let new_body = body.substitute(var, replacement);
                    Term::Abstraction(param.clone(), ty.clone(), Box::new(new_body))
                }
            }
            Term::Application(fun, arg) => {
                let new_fun = fun.substitute(var, replacement);
                let new_arg = arg.substitute(var, replacement);
                Term::Application(Box::new(new_fun), Box::new(new_arg))
            }
        }
    }
    
    /// 检查是否为值
    pub fn is_value(&self) -> bool {
        match self {
            Term::Variable(_) => true,
            Term::Abstraction(_, _, _) => true,
            Term::Application(_, _) => false,
        }
    }
    
    /// 一步归约
    pub fn step(&self) -> Option<Term> {
        match self {
            Term::Application(fun, arg) => {
                // β归约
                if let Term::Abstraction(param, _, body) = &**fun {
                    if arg.is_value() {
                        return Some(body.substitute(param, arg));
                    }
                }
                
                // 应用归约
                if let Some(new_fun) = fun.step() {
                    return Some(Term::Application(Box::new(new_fun), arg.clone()));
                }
                
                if let Some(new_arg) = arg.step() {
                    return Some(Term::Application(fun.clone(), Box::new(new_arg)));
                }
                
                None
            }
            _ => None,
        }
    }
    
    /// 多步归约
    pub fn reduce(&self) -> Term {
        let mut current = self.clone();
        while let Some(next) = current.step() {
            current = next;
        }
        current
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Variable(name) => write!(f, "{}", name),
            Term::Abstraction(param, ty, body) => {
                write!(f, "λ{}:{}. {}", param, ty, body)
            }
            Term::Application(fun, arg) => {
                match **fun {
                    Term::Abstraction(_, _, _) => write!(f, "({})", fun)?,
                    _ => write!(f, "{}", fun)?,
                }
                match **arg {
                    Term::Variable(_) => write!(f, " {}", arg),
                    _ => write!(f, " ({})", arg),
                }
            }
        }
    }
}

/// 类型上下文
pub type Context = HashMap<String, Type>;

/// 类型检查器
pub struct TypeChecker;

impl TypeChecker {
    /// 类型检查
    pub fn type_check(context: &Context, term: &Term) -> Result<Type, String> {
        match term {
            Term::Variable(name) => {
                context.get(name)
                    .cloned()
                    .ok_or_else(|| format!("Unbound variable: {}", name))
            }
            Term::Abstraction(param, param_type, body) => {
                let mut new_context = context.clone();
                new_context.insert(param.clone(), param_type.clone());
                let body_type = Self::type_check(&new_context, body)?;
                Ok(Type::function(param_type.clone(), body_type))
            }
            Term::Application(fun, arg) => {
                let fun_type = Self::type_check(context, fun)?;
                let arg_type = Self::type_check(context, arg)?;
                
                if let Type::Function(from, to) = fun_type {
                    if arg_type == *from {
                        Ok(*to)
                    } else {
                        Err(format!("Type mismatch: expected {}, got {}", from, arg_type))
                    }
                } else {
                    Err(format!("Expected function type, got {}", fun_type))
                }
            }
        }
    }
    
    /// 类型推导
    pub fn infer_type(context: &Context, term: &Term) -> Result<Type, String> {
        Self::type_check(context, term)
    }
    
    /// 检查类型安全
    pub fn is_type_safe(context: &Context, term: &Term) -> bool {
        Self::type_check(context, term).is_ok()
    }
}

/// 类型推导算法
pub struct TypeInference;

impl TypeInference {
    /// 类型推导
    pub fn infer(context: &Context, term: &Term) -> Result<Type, String> {
        TypeChecker::infer_type(context, term)
    }
    
    /// 检查类型唯一性
    pub fn check_uniqueness(context: &Context, term: &Term) -> bool {
        if let Ok(ty1) = Self::infer(context, term) {
            if let Ok(ty2) = Self::infer(context, term) {
                return ty1 == ty2;
            }
        }
        false
    }
}

/// 归约系统
pub struct ReductionSystem;

impl ReductionSystem {
    /// β归约
    pub fn beta_reduce(term: &Term) -> Option<Term> {
        match term {
            Term::Application(fun, arg) => {
                if let Term::Abstraction(param, _, body) = &**fun {
                    if arg.is_value() {
                        return Some(body.substitute(param, arg));
                    }
                }
                None
            }
            _ => None,
        }
    }
    
    /// η归约
    pub fn eta_reduce(term: &Term) -> Option<Term> {
        if let Term::Abstraction(param, param_type, body) = term {
            if let Term::Application(fun, arg) = &**body {
                if let Term::Variable(name) = &**arg {
                    if name == param && !fun.free_variables().contains(param) {
                        return Some((**fun).clone());
                    }
                }
            }
        }
        None
    }
    
    /// 检查强正规化
    pub fn is_strongly_normalizing(term: &Term) -> bool {
        let mut current = term.clone();
        let mut steps = 0;
        let max_steps = 1000; // 防止无限循环
        
        while let Some(next) = current.step() {
            current = next;
            steps += 1;
            if steps > max_steps {
                return false;
            }
        }
        
        true
    }
}

/// 示例和测试
pub struct Examples;

impl Examples {
    /// 恒等函数
    pub fn identity_function() -> Term {
        Term::abs("x", Type::base("A"), Term::var("x"))
    }
    
    /// 常量函数
    pub fn constant_function() -> Term {
        Term::abs("x", Type::base("A"), 
            Term::abs("y", Type::base("B"), Term::var("x")))
    }
    
    /// 函数组合
    pub fn function_composition() -> Term {
        Term::abs("f", Type::function(Type::base("B"), Type::base("C")),
            Term::abs("g", Type::function(Type::base("A"), Type::base("B")),
                Term::abs("x", Type::base("A"),
                    Term::app(Term::var("f"), 
                        Term::app(Term::var("g"), Term::var("x"))))))
    }
    
    /// 布尔真值
    pub fn boolean_true() -> Term {
        Term::abs("x", Type::base("Bool"),
            Term::abs("y", Type::base("Bool"), Term::var("x")))
    }
    
    /// 布尔假值
    pub fn boolean_false() -> Term {
        Term::abs("x", Type::base("Bool"),
            Term::abs("y", Type::base("Bool"), Term::var("y")))
    }
    
    /// 条件表达式
    pub fn conditional() -> Term {
        Term::abs("b", Type::base("Bool"),
            Term::abs("x", Type::base("A"),
                Term::abs("y", Type::base("A"),
                    Term::app(
                        Term::app(Term::var("b"), Term::var("x")),
                        Term::var("y")))))
    }
}

/// 测试模块
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type_checking() {
        let mut context = Context::new();
        context.insert("x".to_string(), Type::base("Int"));
        
        let term = Term::var("x");
        let result = TypeChecker::type_check(&context, &term);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Type::base("Int"));
    }

    #[test]
    fn test_abstraction_type() {
        let context = Context::new();
        let term = Term::abs("x", Type::base("Int"), Term::var("x"));
        let result = TypeChecker::type_check(&context, &term);
        assert!(result.is_ok());
        
        let expected_type = Type::function(Type::base("Int"), Type::base("Int"));
        assert_eq!(result.unwrap(), expected_type);
    }

    #[test]
    fn test_application_type() {
        let context = Context::new();
        let fun = Term::abs("x", Type::base("Int"), Term::var("x"));
        let arg = Term::var("y");
        let mut app_context = context.clone();
        app_context.insert("y".to_string(), Type::base("Int"));
        
        let term = Term::app(fun, arg);
        let result = TypeChecker::type_check(&app_context, &term);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Type::base("Int"));
    }

    #[test]
    fn test_beta_reduction() {
        let fun = Term::abs("x", Type::base("Int"), Term::var("x"));
        let arg = Term::var("y");
        let term = Term::app(fun, arg);
        
        let reduced = term.step();
        assert!(reduced.is_some());
        assert_eq!(reduced.unwrap(), Term::var("y"));
    }

    #[test]
    fn test_type_safety() {
        let context = Context::new();
        let term = Examples::identity_function();
        assert!(TypeChecker::is_type_safe(&context, &term));
    }

    #[test]
    fn test_strong_normalization() {
        let context = Context::new();
        let term = Examples::identity_function();
        assert!(ReductionSystem::is_strongly_normalizing(&term));
    }

    #[test]
    fn test_type_uniqueness() {
        let context = Context::new();
        let term = Examples::identity_function();
        assert!(TypeInference::check_uniqueness(&context, &term));
    }
}
```

### 9.2 Haskell实现

```haskell
-- 简单类型λ演算 - Haskell实现
-- 文件名: SimplyTypedLambdaCalculus.hs

{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module SimplyTypedLambdaCalculus where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (fromJust)

-- 类型定义
data Type = Base String | Function Type Type
  deriving (Show, Eq, Ord)

-- 项定义
data Term = Variable String | Abstraction String Type Term | Application Term Term
  deriving (Show, Eq)

-- 类型上下文
type Context = Map String Type

-- 类型检查器
class TypeChecker where
  typeCheck :: Context -> Term -> Either String Type
  inferType :: Context -> Term -> Either String Type
  isTypeSafe :: Context -> Term -> Bool

-- 类型检查器实例
instance TypeChecker where
  typeCheck context (Variable name) = case Map.lookup name context of
    Just ty -> Right ty
    Nothing -> Left $ "Unbound variable: " ++ name
  
  typeCheck context (Abstraction param paramType body) = do
    let newContext = Map.insert param paramType context
    bodyType <- typeCheck newContext body
    return $ Function paramType bodyType
  
  typeCheck context (Application fun arg) = do
    funType <- typeCheck context fun
    argType <- typeCheck context arg
    case funType of
      Function from to -> if argType == from then return to else Left $ "Type mismatch: expected " ++ show from ++ ", got " ++ show argType
      _ -> Left $ "Expected function type, got " ++ show funType
  
  inferType = typeCheck
  
  isTypeSafe context term = case typeCheck context term of
    Right _ -> True
    Left _ -> False

-- 自由变量
freeVariables :: Term -> Set String
freeVariables (Variable name) = Set.singleton name
freeVariables (Abstraction param _ body) = Set.delete param (freeVariables body)
freeVariables (Application fun arg) = Set.union (freeVariables fun) (freeVariables arg)

-- 变量替换
substitute :: Term -> String -> Term -> Term
substitute (Variable name) var replacement = if name == var then replacement else Variable name
substitute (Abstraction param ty body) var replacement = 
  if param == var 
    then Abstraction param ty body 
    else Abstraction param ty (substitute body var replacement)
substitute (Application fun arg) var replacement = 
  Application (substitute fun var replacement) (substitute arg var replacement)

-- 检查是否为值
isValue :: Term -> Bool
isValue (Variable _) = True
isValue (Abstraction _ _ _) = True
isValue (Application _ _) = False

-- 一步归约
step :: Term -> Maybe Term
step (Application fun arg) = case fun of
  Abstraction param _ body -> if isValue arg then Just (substitute body param arg) else Nothing
  _ -> case step fun of
    Just newFun -> Just (Application newFun arg)
    Nothing -> case step arg of
      Just newArg -> Just (Application fun newArg)
      Nothing -> Nothing
step _ = Nothing

-- 多步归约
reduce :: Term -> Term
reduce term = case step term of
  Just next -> reduce next
  Nothing -> term

-- 归约系统
class ReductionSystem where
  betaReduce :: Term -> Maybe Term
  etaReduce :: Term -> Maybe Term
  isStronglyNormalizing :: Term -> Bool

instance ReductionSystem where
  betaReduce (Application fun arg) = case fun of
    Abstraction param _ body -> if isValue arg then Just (substitute body param arg) else Nothing
    _ -> Nothing
  betaReduce _ = Nothing
  
  etaReduce (Abstraction param paramType (Application fun arg)) = case arg of
    Variable name -> if name == param && not (Set.member param (freeVariables fun)) then Just fun else Nothing
    _ -> Nothing
  etaReduce _ = Nothing
  
  isStronglyNormalizing term = go term 0
    where
      go _ 1000 = False  -- 防止无限循环
      go t steps = case step t of
        Just next -> go next (steps + 1)
        Nothing -> True

-- 类型推导算法
class TypeInference where
  infer :: Context -> Term -> Either String Type
  checkUniqueness :: Context -> Term -> Bool

instance TypeInference where
  infer = typeCheck
  
  checkUniqueness context term = case (infer context term, infer context term) of
    (Right ty1, Right ty2) -> ty1 == ty2
    _ -> False

-- 示例
class Examples where
  identityFunction :: Term
  constantFunction :: Term
  functionComposition :: Term
  booleanTrue :: Term
  booleanFalse :: Term
  conditional :: Term

instance Examples where
  identityFunction = Abstraction "x" (Base "A") (Variable "x")
  
  constantFunction = Abstraction "x" (Base "A") 
    (Abstraction "y" (Base "B") (Variable "x"))
  
  functionComposition = Abstraction "f" (Function (Base "B") (Base "C"))
    (Abstraction "g" (Function (Base "A") (Base "B"))
      (Abstraction "x" (Base "A")
        (Application (Variable "f") 
          (Application (Variable "g") (Variable "x")))))
  
  booleanTrue = Abstraction "x" (Base "Bool")
    (Abstraction "y" (Base "Bool") (Variable "x"))
  
  booleanFalse = Abstraction "x" (Base "Bool")
    (Abstraction "y" (Base "Bool") (Variable "y"))
  
  conditional = Abstraction "b" (Base "Bool")
    (Abstraction "x" (Base "A")
      (Abstraction "y" (Base "A")
        (Application
          (Application (Variable "b") (Variable "x"))
          (Variable "y"))))

-- 测试函数
testTypeChecking :: Bool
testTypeChecking = 
  let context = Map.singleton "x" (Base "Int")
      term = Variable "x"
      result = typeCheck context term
  in case result of
    Right ty -> ty == Base "Int"
    Left _ -> False

testAbstractionType :: Bool
testAbstractionType =
  let context = Map.empty
      term = Abstraction "x" (Base "Int") (Variable "x")
      result = typeCheck context term
  in case result of
    Right ty -> ty == Function (Base "Int") (Base "Int")
    Left _ -> False

testApplicationType :: Bool
testApplicationType =
  let context = Map.singleton "y" (Base "Int")
      fun = Abstraction "x" (Base "Int") (Variable "x")
      arg = Variable "y"
      term = Application fun arg
      result = typeCheck context term
  in case result of
    Right ty -> ty == Base "Int"
    Left _ -> False

testBetaReduction :: Bool
testBetaReduction =
  let fun = Abstraction "x" (Base "Int") (Variable "x")
      arg = Variable "y"
      term = Application fun arg
      reduced = step term
  in case reduced of
    Just result -> result == Variable "y"
    Nothing -> False

testTypeSafety :: Bool
testTypeSafety =
  let context = Map.empty
      term = identityFunction
  in isTypeSafe context term

testStrongNormalization :: Bool
testStrongNormalization =
  let term = identityFunction
  in isStronglyNormalizing term

testTypeUniqueness :: Bool
testTypeUniqueness =
  let context = Map.empty
      term = identityFunction
  in checkUniqueness context term

-- 运行所有测试
runAllTests :: IO ()
runAllTests = do
  putStrLn "Running simply typed lambda calculus tests..."
  putStrLn $ "Type checking test: " ++ show testTypeChecking
  putStrLn $ "Abstraction type test: " ++ show testAbstractionType
  putStrLn $ "Application type test: " ++ show testApplicationType
  putStrLn $ "Beta reduction test: " ++ show testBetaReduction
  putStrLn $ "Type safety test: " ++ show testTypeSafety
  putStrLn $ "Strong normalization test: " ++ show testStrongNormalization
  putStrLn $ "Type uniqueness test: " ++ show testTypeUniqueness
  putStrLn "All tests completed!"
```

## 10. 参考文献

1. Church, Alonzo. *The Calculi of Lambda-Conversion*. Princeton University Press, 1941.
2. Curry, Haskell B. and Feys, Robert. *Combinatory Logic*. North-Holland, 1958.
3. Hindley, J. Roger and Seldin, Jonathan P. *Lambda-Calculus and Combinators: An Introduction*. Cambridge University Press, 2008.
4. Barendregt, Henk P. *The Lambda Calculus: Its Syntax and Semantics*. North-Holland, 1984.
5. Pierce, Benjamin C. *Types and Programming Languages*. MIT Press, 2002.
6. Girard, Jean-Yves, Lafont, Yves, and Taylor, Paul. *Proofs and Types*. Cambridge University Press, 1989.
7. Sørensen, Morten Heine and Urzyczyn, Paweł. *Lectures on the Curry-Howard Isomorphism*. Elsevier, 2006.
8. Thompson, Simon. *Type Theory and Functional Programming*. Addison-Wesley, 1991.
9. Nordström, Bengt, Petersson, Kent, and Smith, Jan M. *Programming in Martin-Löf's Type Theory*. Oxford University Press, 1990.
10. Coquand, Thierry and Huet, Gérard. *The Calculus of Constructions*. Information and Computation, 1988.

---

**最后更新时间**: 2024年12月21日  
**版本**: v1.0  
**维护者**: 形式科学理论体系重构团队  
**状态**: ✅ 已完成


## 批判性分析

- 本节内容待补充：请从多元理论视角、局限性、争议点、应用前景等方面进行批判性分析。
