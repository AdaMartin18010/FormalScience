# 三值逻辑基本概念

## 概述

三值逻辑是经典二值逻辑的重要扩展，允许命题取三个真值：真（True）、假（False）和未知（Unknown/Undefined）。它提供了处理不确定性、部分信息和边界情况的强大工具，在数据库理论、程序验证、人工智能等领域有广泛应用。

## 基本概念

### 真值系统

#### 1. 真值集合

三值逻辑的真值集合为：
$$\mathcal{V} = \{T, F, U\}$$
其中：

- $T$ 表示"真"（True）
- $F$ 表示"假"（False）
- $U$ 表示"未知"（Unknown）或"不确定"（Undefined）

#### 2. 真值排序

三值逻辑中的真值可以按照信息量进行排序：
$$F < U < T$$

这个排序反映了真值的信息含量：

- $F$ 提供最少的信息（明确为假）
- $U$ 提供中等的信息（不确定）
- $T$ 提供最多的信息（明确为真）

### 逻辑连接词

#### 1. 否定算子

三值逻辑的否定算子 $\neg$ 定义如下：

| $\phi$ | $\neg \phi$ |
|--------|-------------|
| T      | F           |
| U      | U           |
| F      | T           |

#### 2. 合取算子

三值逻辑的合取算子 $\land$ 定义如下：

| $\phi$ | $\psi$ | $\phi \land \psi$ |
|--------|--------|-------------------|
| T      | T      | T                 |
| T      | U      | U                 |
| T      | F      | F                 |
| U      | T      | U                 |
| U      | U      | U                 |
| U      | F      | F                 |
| F      | T      | F                 |
| F      | U      | F                 |
| F      | F      | F                 |

#### 3. 析取算子

三值逻辑的析取算子 $\lor$ 定义如下：

| $\phi$ | $\psi$ | $\phi \lor \psi$ |
|--------|--------|------------------|
| T      | T      | T                |
| T      | U      | T                |
| T      | F      | T                |
| U      | T      | T                |
| U      | U      | U                |
| U      | F      | U                |
| F      | T      | T                |
| F      | U      | U                |
| F      | F      | F                |

#### 4. 蕴含算子

三值逻辑的蕴含算子 $\rightarrow$ 定义如下：

| $\phi$ | $\psi$ | $\phi \rightarrow \psi$ |
|--------|--------|-------------------------|
| T      | T      | T                       |
| T      | U      | U                       |
| T      | F      | F                       |
| U      | T      | T                       |
| U      | U      | U                       |
| U      | F      | U                       |
| F      | T      | T                       |
| F      | U      | T                       |
| F      | F      | T                       |

#### 5. 等价算子

三值逻辑的等价算子 $\leftrightarrow$ 定义如下：

| $\phi$ | $\psi$ | $\phi \leftrightarrow \psi$ |
|--------|--------|----------------------------|
| T      | T      | T                          |
| T      | U      | U                          |
| T      | F      | F                          |
| U      | T      | U                          |
| U      | U      | U                          |
| U      | F      | U                          |
| F      | T      | F                          |
| F      | U      | U                          |
| F      | F      | T                          |

### 语义理论

#### 1. 真值赋值

三值逻辑的真值赋值函数 $v: \mathcal{P} \rightarrow \mathcal{V}$ 将原子命题映射到真值集合。

#### 2. 语义解释

设 $\phi$ 和 $\psi$ 为三值逻辑公式，$v$ 为真值赋值函数，则：

1. **原子命题**：$v(p) \in \mathcal{V}$，其中 $p$ 为原子命题
2. **否定**：$v(\neg \phi) = \neg v(\phi)$
3. **合取**：$v(\phi \land \psi) = v(\phi) \land v(\psi)$
4. **析取**：$v(\phi \lor \psi) = v(\phi) \lor v(\psi)$
5. **蕴含**：$v(\phi \rightarrow \psi) = v(\phi) \rightarrow v(\psi)$
6. **等价**：$v(\phi \leftrightarrow \psi) = v(\phi) \leftrightarrow v(\psi)$

#### 3. 语义性质

##### 幂等性

- $\phi \land \phi \equiv \phi$
- $\phi \lor \phi \equiv \phi$

##### 交换性

- $\phi \land \psi \equiv \psi \land \phi$
- $\phi \lor \psi \equiv \psi \lor \phi$

##### 结合性

- $(\phi \land \psi) \land \chi \equiv \phi \land (\psi \land \chi)$
- $(\phi \lor \psi) \lor \chi \equiv \phi \lor (\psi \lor \chi)$

##### 分配性

- $\phi \land (\psi \lor \chi) \equiv (\phi \land \psi) \lor (\phi \land \chi)$
- $\phi \lor (\psi \land \chi) \equiv (\phi \lor \psi) \land (\phi \lor \chi)$

##### 德摩根律

- $\neg(\phi \land \psi) \equiv \neg \phi \lor \neg \psi$
- $\neg(\phi \lor \psi) \equiv \neg \phi \land \neg \psi$

### 推理规则

#### 1. 基本推理规则

##### 合取引入

如果 $\phi$ 和 $\psi$ 都为真，则 $\phi \land \psi$ 为真。

##### 合取消除

如果 $\phi \land \psi$ 为真，则 $\phi$ 和 $\psi$ 都为真。

##### 析取引入

如果 $\phi$ 为真，则 $\phi \lor \psi$ 为真。

##### 析取消除

如果 $\phi \lor \psi$ 为真，且从 $\phi$ 可以推出 $\chi$，从 $\psi$ 可以推出 $\chi$，则 $\chi$ 为真。

#### 2. 三值推理的特殊规则

##### 未知处理

- 如果 $\phi$ 为未知，则 $\neg \phi$ 也为未知
- 如果 $\phi$ 为未知且 $\psi$ 为假，则 $\phi \land \psi$ 为假
- 如果 $\phi$ 为未知且 $\psi$ 为真，则 $\phi \lor \psi$ 为真

##### 保守推理

三值逻辑采用保守推理策略：

- 当信息不足时，倾向于保持未知状态
- 只有在明确的情况下才做出真或假的判断

### 重要性质

#### 1. 单调性

三值逻辑的连接词具有单调性：

- 如果 $\phi \leq \psi$，则 $\phi \land \chi \leq \psi \land \chi$
- 如果 $\phi \leq \psi$，则 $\phi \lor \chi \leq \psi \lor \chi$

#### 2. 连续性

三值逻辑的连接词是连续的：

- 对于任何真值序列，连接词的结果是连续的

#### 3. 信息保持

三值逻辑保持信息量：

- 连接词不会增加信息量
- 未知状态在推理过程中得到保持

## 应用实例

### 数据库理论

#### NULL值处理

```sql
-- 三值逻辑在SQL中的应用
SELECT * FROM users 
WHERE age > 18 OR age IS NULL;

-- 等价于三值逻辑公式
-- age > 18 ∨ age = NULL
```

#### 部分信息查询

```sql
-- 处理不完整的信息
SELECT * FROM products 
WHERE price < 100 OR price IS NULL;

-- 三值逻辑公式
-- price < 100 ∨ price = NULL
```

### 程序验证

#### 边界条件检查

```rust
// 三值逻辑在程序验证中的应用
fn check_boundary(index: Option<usize>, size: usize) -> ThreeValued {
    match index {
        Some(i) => {
            if i < size {
                ThreeValued::True
            } else {
                ThreeValued::False
            }
        }
        None => ThreeValued::Unknown
    }
}
```

#### 初始化检查

```rust
// 检查变量是否已初始化
fn is_initialized(var: Option<T>) -> ThreeValued {
    match var {
        Some(_) => ThreeValued::True,
        None => ThreeValued::False
    }
}
```

### 人工智能

#### 不确定性推理

```python
# 三值逻辑在AI中的应用
def uncertain_reasoning(evidence, hypothesis):
    if evidence is None:
        return ThreeValued.UNKNOWN
    elif evidence > threshold:
        return ThreeValued.TRUE
    else:
        return ThreeValued.FALSE
```

## 代码实现

### Rust实现

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ThreeValued {
    True,
    False,
    Unknown,
}

impl ThreeValued {
    pub fn not(self) -> Self {
        match self {
            ThreeValued::True => ThreeValued::False,
            ThreeValued::False => ThreeValued::True,
            ThreeValued::Unknown => ThreeValued::Unknown,
        }
    }
    
    pub fn and(self, other: Self) -> Self {
        match (self, other) {
            (ThreeValued::True, ThreeValued::True) => ThreeValued::True,
            (ThreeValued::True, ThreeValued::Unknown) => ThreeValued::Unknown,
            (ThreeValued::True, ThreeValued::False) => ThreeValued::False,
            (ThreeValued::Unknown, ThreeValued::True) => ThreeValued::Unknown,
            (ThreeValued::Unknown, ThreeValued::Unknown) => ThreeValued::Unknown,
            (ThreeValued::Unknown, ThreeValued::False) => ThreeValued::False,
            (ThreeValued::False, _) => ThreeValued::False,
        }
    }
    
    pub fn or(self, other: Self) -> Self {
        match (self, other) {
            (ThreeValued::True, _) => ThreeValued::True,
            (ThreeValued::Unknown, ThreeValued::True) => ThreeValued::True,
            (ThreeValued::Unknown, ThreeValued::Unknown) => ThreeValued::Unknown,
            (ThreeValued::Unknown, ThreeValued::False) => ThreeValued::Unknown,
            (ThreeValued::False, ThreeValued::True) => ThreeValued::True,
            (ThreeValued::False, ThreeValued::Unknown) => ThreeValued::Unknown,
            (ThreeValued::False, ThreeValued::False) => ThreeValued::False,
        }
    }
    
    pub fn implies(self, other: Self) -> Self {
        match (self, other) {
            (ThreeValued::True, ThreeValued::True) => ThreeValued::True,
            (ThreeValued::True, ThreeValued::Unknown) => ThreeValued::Unknown,
            (ThreeValued::True, ThreeValued::False) => ThreeValued::False,
            (ThreeValued::Unknown, ThreeValued::True) => ThreeValued::True,
            (ThreeValued::Unknown, ThreeValued::Unknown) => ThreeValued::Unknown,
            (ThreeValued::Unknown, ThreeValued::False) => ThreeValued::Unknown,
            (ThreeValued::False, _) => ThreeValued::True,
        }
    }
    
    pub fn equivalent(self, other: Self) -> Self {
        match (self, other) {
            (ThreeValued::True, ThreeValued::True) => ThreeValued::True,
            (ThreeValued::True, ThreeValued::Unknown) => ThreeValued::Unknown,
            (ThreeValued::True, ThreeValued::False) => ThreeValued::False,
            (ThreeValued::Unknown, ThreeValued::True) => ThreeValued::Unknown,
            (ThreeValued::Unknown, ThreeValued::Unknown) => ThreeValued::Unknown,
            (ThreeValued::Unknown, ThreeValued::False) => ThreeValued::Unknown,
            (ThreeValued::False, ThreeValued::True) => ThreeValued::False,
            (ThreeValued::False, ThreeValued::Unknown) => ThreeValued::Unknown,
            (ThreeValued::False, ThreeValued::False) => ThreeValued::True,
        }
    }
}

impl std::ops::Not for ThreeValued {
    type Output = Self;
    
    fn not(self) -> Self::Output {
        self.not()
    }
}

impl std::ops::BitAnd for ThreeValued {
    type Output = Self;
    
    fn bitand(self, rhs: Self) -> Self::Output {
        self.and(rhs)
    }
}

impl std::ops::BitOr for ThreeValued {
    type Output = Self;
    
    fn bitor(self, rhs: Self) -> Self::Output {
        self.or(rhs)
    }
}

// 三值逻辑公式
#[derive(Debug, Clone)]
pub enum ThreeValuedFormula {
    Atom(String),
    Not(Box<ThreeValuedFormula>),
    And(Box<ThreeValuedFormula>, Box<ThreeValuedFormula>),
    Or(Box<ThreeValuedFormula>, Box<ThreeValuedFormula>),
    Implies(Box<ThreeValuedFormula>, Box<ThreeValuedFormula>),
    Equivalent(Box<ThreeValuedFormula>, Box<ThreeValuedFormula>),
}

impl ThreeValuedFormula {
    pub fn atom(name: &str) -> Self {
        ThreeValuedFormula::Atom(name.to_string())
    }
    
    pub fn not(phi: ThreeValuedFormula) -> Self {
        ThreeValuedFormula::Not(Box::new(phi))
    }
    
    pub fn and(phi: ThreeValuedFormula, psi: ThreeValuedFormula) -> Self {
        ThreeValuedFormula::And(Box::new(phi), Box::new(psi))
    }
    
    pub fn or(phi: ThreeValuedFormula, psi: ThreeValuedFormula) -> Self {
        ThreeValuedFormula::Or(Box::new(phi), Box::new(psi))
    }
    
    pub fn implies(phi: ThreeValuedFormula, psi: ThreeValuedFormula) -> Self {
        ThreeValuedFormula::Implies(Box::new(phi), Box::new(psi))
    }
    
    pub fn equivalent(phi: ThreeValuedFormula, psi: ThreeValuedFormula) -> Self {
        ThreeValuedFormula::Equivalent(Box::new(phi), Box::new(psi))
    }
}

// 三值语义解释器
pub struct ThreeValuedSemantics {
    assignments: std::collections::HashMap<String, ThreeValued>,
}

impl ThreeValuedSemantics {
    pub fn new() -> Self {
        ThreeValuedSemantics {
            assignments: std::collections::HashMap::new(),
        }
    }
    
    pub fn assign(&mut self, atom: &str, value: ThreeValued) {
        self.assignments.insert(atom.to_string(), value);
    }
    
    pub fn evaluate(&self, formula: &ThreeValuedFormula) -> ThreeValued {
        match formula {
            ThreeValuedFormula::Atom(name) => {
                self.assignments.get(name).copied().unwrap_or(ThreeValued::Unknown)
            }
            ThreeValuedFormula::Not(phi) => !self.evaluate(phi),
            ThreeValuedFormula::And(phi, psi) => {
                self.evaluate(phi) & self.evaluate(psi)
            }
            ThreeValuedFormula::Or(phi, psi) => {
                self.evaluate(phi) | self.evaluate(psi)
            }
            ThreeValuedFormula::Implies(phi, psi) => {
                self.evaluate(phi).implies(self.evaluate(psi))
            }
            ThreeValuedFormula::Equivalent(phi, psi) => {
                self.evaluate(phi).equivalent(self.evaluate(psi))
            }
        }
    }
}

// 示例使用
fn main() {
    // 创建三值逻辑公式：p ∧ (q ∨ ¬r)
    let p = ThreeValuedFormula::atom("p");
    let q = ThreeValuedFormula::atom("q");
    let r = ThreeValuedFormula::atom("r");
    let formula = ThreeValuedFormula::and(
        p.clone(),
        ThreeValuedFormula::or(q, ThreeValuedFormula::not(r))
    );
    
    // 创建语义解释器
    let mut semantics = ThreeValuedSemantics::new();
    semantics.assign("p", ThreeValued::True);
    semantics.assign("q", ThreeValued::Unknown);
    semantics.assign("r", ThreeValued::False);
    
    // 评估公式
    let result = semantics.evaluate(&formula);
    println!("Formula evaluated to: {:?}", result);
}
```

### Haskell实现

```haskell
-- 三值数据类型
data ThreeValued = True | False | Unknown
    deriving (Show, Eq, Ord)

-- 否定算子
not' :: ThreeValued -> ThreeValued
not' True = False
not' False = True
not' Unknown = Unknown

-- 合取算子
and' :: ThreeValued -> ThreeValued -> ThreeValued
and' True True = True
and' True Unknown = Unknown
and' True False = False
and' Unknown True = Unknown
and' Unknown Unknown = Unknown
and' Unknown False = False
and' False _ = False

-- 析取算子
or' :: ThreeValued -> ThreeValued -> ThreeValued
or' True _ = True
or' Unknown True = True
or' Unknown Unknown = Unknown
or' Unknown False = Unknown
or' False True = True
or' False Unknown = Unknown
or' False False = False

-- 蕴含算子
implies :: ThreeValued -> ThreeValued -> ThreeValued
implies True True = True
implies True Unknown = Unknown
implies True False = False
implies Unknown True = True
implies Unknown Unknown = Unknown
implies Unknown False = Unknown
implies False _ = True

-- 等价算子
equivalent :: ThreeValued -> ThreeValued -> ThreeValued
equivalent True True = True
equivalent True Unknown = Unknown
equivalent True False = False
equivalent Unknown True = Unknown
equivalent Unknown Unknown = Unknown
equivalent Unknown False = Unknown
equivalent False True = False
equivalent False Unknown = Unknown
equivalent False False = True

-- 三值逻辑公式数据类型
data ThreeValuedFormula = Atom String
                        | Not ThreeValuedFormula
                        | And ThreeValuedFormula ThreeValuedFormula
                        | Or ThreeValuedFormula ThreeValuedFormula
                        | Implies ThreeValuedFormula ThreeValuedFormula
                        | Equivalent ThreeValuedFormula ThreeValuedFormula
                        deriving (Show, Eq)

-- 构造函数
atom :: String -> ThreeValuedFormula
atom = Atom

not'' :: ThreeValuedFormula -> ThreeValuedFormula
not'' = Not

and'' :: ThreeValuedFormula -> ThreeValuedFormula -> ThreeValuedFormula
and'' = And

or'' :: ThreeValuedFormula -> ThreeValuedFormula -> ThreeValuedFormula
or'' = Or

implies' :: ThreeValuedFormula -> ThreeValuedFormula -> ThreeValuedFormula
implies' = Implies

equivalent' :: ThreeValuedFormula -> ThreeValuedFormula -> ThreeValuedFormula
equivalent' = Equivalent

-- 三值语义解释器
type Assignment = [(String, ThreeValued)]

-- 查找原子命题的真值
findValue :: String -> Assignment -> ThreeValued
findValue name assignment = maybe Unknown id (lookup name assignment)

-- 语义评估函数
evaluate :: Assignment -> ThreeValuedFormula -> ThreeValued
evaluate assignment formula = case formula of
    Atom name -> findValue name assignment
    Not phi -> not' (evaluate assignment phi)
    And phi psi -> 
        and' (evaluate assignment phi) (evaluate assignment psi)
    Or phi psi -> 
        or' (evaluate assignment phi) (evaluate assignment psi)
    Implies phi psi -> 
        implies (evaluate assignment phi) (evaluate assignment psi)
    Equivalent phi psi -> 
        equivalent (evaluate assignment phi) (evaluate assignment psi)

-- 示例使用
main :: IO ()
main = do
    -- 创建三值逻辑公式：p ∧ (q ∨ ¬r)
    let p = atom "p"
        q = atom "q"
        r = atom "r"
        formula = and'' p (or'' q (not'' r))
    
    -- 创建赋值
    let assignment = [("p", True), ("q", Unknown), ("r", False)]
    
    -- 评估公式
    let result = evaluate assignment formula
    putStrLn $ "Formula evaluated to: " ++ show result
```

## 总结

三值逻辑为处理不确定性、部分信息和边界情况提供了强大的逻辑工具。通过引入未知真值，三值逻辑能够更准确地反映现实世界中的复杂情况。

三值逻辑的语义理论基于真值表和代数运算，提供了严格的数学基础。通过代码实现，我们可以实际应用三值逻辑来解决各种实际问题，特别是在数据库理论、程序验证和人工智能等领域。

三值逻辑是经典二值逻辑的重要扩展，为处理不确定性提供了重要的理论基础，为后续的多值逻辑发展奠定了基础。
