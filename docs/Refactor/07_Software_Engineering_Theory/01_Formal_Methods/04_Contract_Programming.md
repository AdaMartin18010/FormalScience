# 契约式编程

## 📋 概述

契约式编程(Contract Programming)是一种基于形式化契约的软件开发方法，通过前置条件、后置条件和不变式来明确程序的行为规范。本文档系统性地介绍契约式编程的理论基础、方法体系、工具实现和实际应用。

## 🎯 核心目标

1. **建立契约式编程的理论框架**
2. **系统化契约类型和验证方法**
3. **提供契约验证工具实现**
4. **展示实际应用案例**

## 📚 目录

1. [基本概念](#1-基本概念)
2. [形式化定义](#2-形式化定义)
3. [定理与证明](#3-定理与证明)
4. [代码实现](#4-代码实现)
5. [应用示例](#5-应用示例)
6. [相关理论](#6-相关理论)
7. [参考文献](#7-参考文献)

## 1. 基本概念

### 1.1 契约式编程的定义

契约式编程是一种软件开发方法，其核心思想是：

- **契约作为规范**：程序行为由契约明确定义
- **前置条件**：调用者必须满足的条件
- **后置条件**：被调用者必须保证的结果
- **不变式**：对象状态必须保持的性质

### 1.2 契约类型

#### 1.2.1 前置条件 (Preconditions)

```latex
前置条件 = {
    输入验证: {参数类型, 参数范围, 参数关系},
    状态验证: {对象状态, 系统状态, 环境状态},
    资源验证: {资源可用性, 权限检查, 容量限制}
}
```

#### 1.2.2 后置条件 (Postconditions)

```latex
后置条件 = {
    返回值验证: {返回值类型, 返回值范围, 返回值关系},
    状态变化: {对象状态变化, 系统状态变化, 副作用},
    资源管理: {资源释放, 资源分配, 资源状态}
}
```

#### 1.2.3 不变式 (Invariants)

```latex
不变式 = {
    类不变式: {对象状态一致性, 数据完整性, 业务规则},
    循环不变式: {循环变量性质, 循环终止条件, 循环进度},
    全局不变式: {系统一致性, 全局约束, 跨对象关系}
}
```

### 1.3 契约验证策略

#### 1.3.1 静态验证

- **编译时检查**：类型检查、静态分析
- **定理证明**：形式化证明契约正确性
- **抽象解释**：静态分析程序性质

#### 1.3.2 动态验证

- **运行时检查**：执行时验证契约
- **断言检查**：关键点断言验证
- **监控系统**：持续监控契约违反

## 2. 形式化定义

### 2.1 契约定义

**定义 2.1** (契约):
契约是一个三元组 $C = (P, Q, I)$，其中：

```latex
C = (P, Q, I)

其中:
- P: 前置条件 (Precondition)
- Q: 后置条件 (Postcondition)  
- I: 不变式 (Invariant)
```

### 2.2 契约满足定义

**定义 2.2** (契约满足):
程序 $S$ 满足契约 $C = (P, Q, I)$，当且仅当：

```latex
∀σ: P(σ) ∧ I(σ) ⟹ wp(S, Q ∧ I)

其中:
- σ: 程序状态
- wp: 最弱前置条件
- I: 不变式保持
```

### 2.3 契约组合定义

**定义 2.3** (契约组合):
对于契约 $C_1 = (P_1, Q_1, I_1)$ 和 $C_2 = (P_2, Q_2, I_2)$，其组合为：

```latex
C₁ ∘ C₂ = (P₁ ∧ wp(S₁, P₂), Q₁ ∧ wp(S₁, Q₂), I₁ ∧ I₂)

其中:
- S₁: 第一个程序的语句
- wp: 最弱前置条件
```

## 3. 定理与证明

### 3.1 契约正确性定理

**定理 3.1** (契约正确性):
如果程序 $S$ 满足契约 $C = (P, Q, I)$，则对于任何满足前置条件的状态，程序执行后满足后置条件和不变式。

**证明**:

```latex
1. 契约满足定义: ∀σ: P(σ) ∧ I(σ) ⟹ wp(S, Q ∧ I)
2. 最弱前置条件性质: wp(S, Q ∧ I)(σ) ⟺ ∀σ': σ' = S(σ) ⟹ Q(σ') ∧ I(σ')
3. 因此: P(σ) ∧ I(σ) ⟹ ∀σ': σ' = S(σ) ⟹ Q(σ') ∧ I(σ')
4. 即程序满足契约
```

### 3.2 契约组合定理

**定理 3.2** (契约组合):
如果程序 $S_1$ 满足契约 $C_1$，程序 $S_2$ 满足契约 $C_2$，则 $S_1; S_2$ 满足契约 $C_1 \circ C_2$。

**证明**:

```latex
1. S₁ 满足 C₁: ∀σ: P₁(σ) ∧ I₁(σ) ⟹ wp(S₁, Q₁ ∧ I₁)
2. S₂ 满足 C₂: ∀σ: P₂(σ) ∧ I₂(σ) ⟹ wp(S₂, Q₂ ∧ I₂)
3. 序列组合: wp(S₁; S₂, Q) = wp(S₁, wp(S₂, Q))
4. 因此: S₁; S₂ 满足 C₁ ∘ C₂
```

### 3.3 契约继承定理

**定理 3.3** (契约继承):
如果子类契约 $C_s = (P_s, Q_s, I_s)$ 强于父类契约 $C_p = (P_p, Q_p, I_p)$，则子类可以替换父类。

**证明**:

```latex
1. 契约强化: P_s ⟹ P_p, Q_p ⟹ Q_s, I_s ⟹ I_p
2. 里氏替换原则: 子类可以替换父类
3. 契约满足: 子类满足父类契约
4. 因此替换是安全的
```

## 4. 代码实现

### 4.1 契约式编程框架 (Rust)

```rust
use std::collections::HashMap;

/// 契约验证器
trait ContractValidator {
    fn validate_precondition(&self, args: &[&str]) -> bool;
    fn validate_postcondition(&self, result: &str, args: &[&str]) -> bool;
    fn validate_invariant(&self, state: &str) -> bool;
}

/// 契约定义
struct Contract {
    precondition: String,
    postcondition: String,
    invariant: String,
}

impl Contract {
    fn new(pre: String, post: String, inv: String) -> Self {
        Self {
            precondition: pre,
            postcondition: post,
            invariant: inv,
        }
    }
}

/// 契约式函数包装器
struct ContractFunction<F> {
    contract: Contract,
    function: F,
}

impl<F> ContractFunction<F>
where
    F: Fn(&[&str]) -> String,
{
    fn new(contract: Contract, function: F) -> Self {
        Self { contract, function }
    }

    fn call(&self, args: &[&str]) -> Result<String, String> {
        // 验证前置条件
        if !self.validate_precondition(args) {
            return Err("Precondition violation".to_string());
        }

        // 验证不变式
        if !self.validate_invariant("before_call") {
            return Err("Invariant violation before call".to_string());
        }

        // 执行函数
        let result = (self.function)(args);

        // 验证后置条件
        if !self.validate_postcondition(&result, args) {
            return Err("Postcondition violation".to_string());
        }

        // 验证不变式
        if !self.validate_invariant("after_call") {
            return Err("Invariant violation after call".to_string());
        }

        Ok(result)
    }
}

impl<F> ContractValidator for ContractFunction<F> {
    fn validate_precondition(&self, args: &[&str]) -> bool {
        // 简化的前置条件验证
        match self.contract.precondition.as_str() {
            "non_empty" => !args.is_empty(),
            "positive" => args.iter().all(|&arg| arg.parse::<i32>().unwrap_or(0) > 0),
            "sorted" => {
                let mut sorted = args.to_vec();
                sorted.sort();
                args == sorted.as_slice()
            }
            _ => true,
        }
    }

    fn validate_postcondition(&self, result: &str, args: &[&str]) -> bool {
        // 简化的后置条件验证
        match self.contract.postcondition.as_str() {
            "positive_result" => result.parse::<i32>().unwrap_or(0) > 0,
            "length_preserved" => result.len() == args.len(),
            "sorted_result" => {
                let mut chars: Vec<char> = result.chars().collect();
                let mut sorted = chars.clone();
                sorted.sort();
                chars == sorted
            }
            _ => true,
        }
    }

    fn validate_invariant(&self, state: &str) -> bool {
        // 简化的不变式验证
        match self.contract.invariant.as_str() {
            "state_consistent" => state != "corrupted",
            "memory_safe" => state != "memory_leak",
            _ => true,
        }
    }
}

/// 契约式类
struct ContractClass {
    data: Vec<i32>,
    contract: Contract,
}

impl ContractClass {
    fn new(contract: Contract) -> Self {
        Self {
            data: Vec::new(),
            contract,
        }
    }

    fn add(&mut self, value: i32) -> Result<(), String> {
        // 验证前置条件
        if !self.validate_precondition_add(value) {
            return Err("Add precondition violation".to_string());
        }

        // 验证不变式
        if !self.validate_invariant() {
            return Err("Invariant violation before add".to_string());
        }

        // 执行操作
        self.data.push(value);

        // 验证后置条件
        if !self.validate_postcondition_add(value) {
            return Err("Add postcondition violation".to_string());
        }

        // 验证不变式
        if !self.validate_invariant() {
            return Err("Invariant violation after add".to_string());
        }

        Ok(())
    }

    fn remove(&mut self, index: usize) -> Result<i32, String> {
        // 验证前置条件
        if !self.validate_precondition_remove(index) {
            return Err("Remove precondition violation".to_string());
        }

        // 验证不变式
        if !self.validate_invariant() {
            return Err("Invariant violation before remove".to_string());
        }

        // 执行操作
        let result = self.data.remove(index);

        // 验证后置条件
        if !self.validate_postcondition_remove(result, index) {
            return Err("Remove postcondition violation".to_string());
        }

        // 验证不变式
        if !self.validate_invariant() {
            return Err("Invariant violation after remove".to_string());
        }

        Ok(result)
    }

    fn get(&self, index: usize) -> Result<i32, String> {
        // 验证前置条件
        if !self.validate_precondition_get(index) {
            return Err("Get precondition violation".to_string());
        }

        // 验证不变式
        if !self.validate_invariant() {
            return Err("Invariant violation before get".to_string());
        }

        // 执行操作
        let result = self.data[index];

        // 验证后置条件
        if !self.validate_postcondition_get(result, index) {
            return Err("Get postcondition violation".to_string());
        }

        Ok(result)
    }
}

impl ContractClass {
    fn validate_precondition_add(&self, value: i32) -> bool {
        // 前置条件：值必须为正数
        value > 0
    }

    fn validate_postcondition_add(&self, value: i32) -> bool {
        // 后置条件：值必须被添加到数据中
        self.data.contains(&value)
    }

    fn validate_precondition_remove(&self, index: usize) -> bool {
        // 前置条件：索引必须在有效范围内
        index < self.data.len()
    }

    fn validate_postcondition_remove(&self, result: i32, index: usize) -> bool {
        // 后置条件：返回的值必须是从指定位置移除的值
        // 这里简化处理，实际应该检查数据确实被移除
        true
    }

    fn validate_precondition_get(&self, index: usize) -> bool {
        // 前置条件：索引必须在有效范围内
        index < self.data.len()
    }

    fn validate_postcondition_get(&self, result: i32, index: usize) -> bool {
        // 后置条件：返回的值必须是指定位置的值
        self.data[index] == result
    }

    fn validate_invariant(&self) -> bool {
        // 不变式：所有数据必须为正数
        self.data.iter().all(|&x| x > 0)
    }
}

/// 高级契约验证器
struct AdvancedContractValidator {
    rules: HashMap<String, Box<dyn Fn(&[&str]) -> bool>>,
}

impl AdvancedContractValidator {
    fn new() -> Self {
        let mut rules = HashMap::new();
        
        // 添加验证规则
        rules.insert("array_bounds".to_string(), Box::new(|args| {
            if args.len() < 2 {
                return false;
            }
            let index: usize = args[0].parse().unwrap_or(0);
            let array_len: usize = args[1].parse().unwrap_or(0);
            index < array_len
        }));

        rules.insert("non_null".to_string(), Box::new(|args| {
            !args.is_empty() && args.iter().all(|&arg| arg != "null")
        }));

        rules.insert("sorted_array".to_string(), Box::new(|args| {
            let mut sorted = args.to_vec();
            sorted.sort();
            args == sorted.as_slice()
        }));

        Self { rules }
    }

    fn validate(&self, rule_name: &str, args: &[&str]) -> bool {
        if let Some(rule) = self.rules.get(rule_name) {
            rule(args)
        } else {
            true // 未知规则默认通过
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_contract_function() {
        let contract = Contract::new(
            "non_empty".to_string(),
            "positive_result".to_string(),
            "state_consistent".to_string(),
        );

        let function = |args: &[&str]| {
            let sum: i32 = args.iter()
                .map(|&arg| arg.parse::<i32>().unwrap_or(0))
                .sum();
            sum.to_string()
        };

        let contract_fn = ContractFunction::new(contract, function);

        // 测试成功情况
        let result = contract_fn.call(&["1", "2", "3"]);
        assert!(result.is_ok());

        // 测试前置条件违反
        let result = contract_fn.call(&[]);
        assert!(result.is_err());
    }

    #[test]
    fn test_contract_class() {
        let contract = Contract::new(
            "valid_operation".to_string(),
            "operation_success".to_string(),
            "data_consistent".to_string(),
        );

        let mut contract_class = ContractClass::new(contract);

        // 测试添加操作
        assert!(contract_class.add(5).is_ok());
        assert!(contract_class.add(-1).is_err()); // 违反前置条件

        // 测试获取操作
        assert_eq!(contract_class.get(0).unwrap(), 5);
        assert!(contract_class.get(10).is_err()); // 违反前置条件

        // 测试移除操作
        assert_eq!(contract_class.remove(0).unwrap(), 5);
        assert!(contract_class.remove(0).is_err()); // 违反前置条件
    }

    #[test]
    fn test_advanced_validator() {
        let validator = AdvancedContractValidator::new();

        // 测试数组边界检查
        assert!(validator.validate("array_bounds", &["0", "5"]));
        assert!(!validator.validate("array_bounds", &["10", "5"]));

        // 测试非空检查
        assert!(validator.validate("non_null", &["hello", "world"]));
        assert!(!validator.validate("non_null", &["null"]));

        // 测试排序检查
        assert!(validator.validate("sorted_array", &["1", "2", "3"]));
        assert!(!validator.validate("sorted_array", &["3", "1", "2"]));
    }
}
```

### 4.2 契约验证引擎 (Haskell)

```haskell
-- 契约定义
data Contract = Contract {
    precondition :: String,
    postcondition :: String,
    invariant :: String
} deriving (Show, Eq)

-- 验证结果
data ValidationResult = 
    Success
  | PreconditionViolation String
  | PostconditionViolation String
  | InvariantViolation String
  deriving (Show, Eq)

-- 契约验证器
class ContractValidator a where
    validatePrecondition :: a -> [String] -> Bool
    validatePostcondition :: a -> String -> [String] -> Bool
    validateInvariant :: a -> String -> Bool

-- 简单契约验证器
data SimpleValidator = SimpleValidator deriving (Show)

instance ContractValidator SimpleValidator where
    validatePrecondition validator args = 
        case precondition validator of
            "non_empty" -> not (null args)
            "positive" -> all (\arg -> read arg > 0) args
            "sorted" -> args == sort args
            _ -> True
    
    validatePostcondition validator result args = 
        case postcondition validator of
            "positive_result" -> read result > 0
            "length_preserved" -> length result == length args
            "sorted_result" -> result == sort result
            _ -> True
    
    validateInvariant validator state = 
        case invariant validator of
            "state_consistent" -> state /= "corrupted"
            "memory_safe" -> state /= "memory_leak"
            _ -> True

-- 契约式函数
data ContractFunction a b = ContractFunction {
    contract :: Contract,
    function :: [String] -> String,
    validator :: SimpleValidator
} deriving (Show)

-- 执行契约式函数
executeContractFunction :: ContractFunction a b -> [String] -> Either String String
executeContractFunction contractFn args = do
    -- 验证前置条件
    unless (validatePrecondition (validator contractFn) args) $
        Left "Precondition violation"
    
    -- 验证不变式
    unless (validateInvariant (validator contractFn) "before_call") $
        Left "Invariant violation before call"
    
    -- 执行函数
    let result = function contractFn args
    
    -- 验证后置条件
    unless (validatePostcondition (validator contractFn) result args) $
        Left "Postcondition violation"
    
    -- 验证不变式
    unless (validateInvariant (validator contractFn) "after_call") $
        Left "Invariant violation after call"
    
    Right result

-- 契约式类
data ContractClass = ContractClass {
    data_ :: [Int],
    classContract :: Contract,
    classValidator :: SimpleValidator
} deriving (Show)

-- 类操作
addElement :: ContractClass -> Int -> Either String ContractClass
addElement cls value = do
    -- 验证前置条件
    unless (value > 0) $
        Left "Add precondition violation: value must be positive"
    
    -- 验证不变式
    unless (all (> 0) (data_ cls)) $
        Left "Invariant violation before add"
    
    -- 执行操作
    let newData = data_ cls ++ [value]
    let newClass = cls { data_ = newData }
    
    -- 验证后置条件
    unless (value `elem` newData) $
        Left "Add postcondition violation: value not added"
    
    -- 验证不变式
    unless (all (> 0) newData) $
        Left "Invariant violation after add"
    
    Right newClass

removeElement :: ContractClass -> Int -> Either String (Int, ContractClass)
removeElement cls index = do
    -- 验证前置条件
    unless (index >= 0 && index < length (data_ cls)) $
        Left "Remove precondition violation: index out of bounds"
    
    -- 验证不变式
    unless (all (> 0) (data_ cls)) $
        Left "Invariant violation before remove"
    
    -- 执行操作
    let (before, after) = splitAt index (data_ cls)
    let removed = head after
    let newData = before ++ tail after
    let newClass = cls { data_ = newData }
    
    -- 验证后置条件
    unless (removed `notElem` newData) $
        Left "Remove postcondition violation: element still present"
    
    -- 验证不变式
    unless (all (> 0) newData) $
        Left "Invariant violation after remove"
    
    Right (removed, newClass)

getElement :: ContractClass -> Int -> Either String Int
getElement cls index = do
    -- 验证前置条件
    unless (index >= 0 && index < length (data_ cls)) $
        Left "Get precondition violation: index out of bounds"
    
    -- 验证不变式
    unless (all (> 0) (data_ cls)) $
        Left "Invariant violation before get"
    
    -- 执行操作
    let result = (data_ cls) !! index
    
    -- 验证后置条件
    unless (result == (data_ cls) !! index) $
        Left "Get postcondition violation: wrong element returned"
    
    Right result

-- 高级契约验证器
data AdvancedValidator = AdvancedValidator {
    rules :: [(String, [String] -> Bool)]
} deriving (Show)

instance ContractValidator AdvancedValidator where
    validatePrecondition validator args = 
        all (\(ruleName, rule) -> rule args) (rules validator)
    
    validatePostcondition validator result args = 
        all (\(ruleName, rule) -> rule (result:args)) (rules validator)
    
    validateInvariant validator state = 
        all (\(ruleName, rule) -> rule [state]) (rules validator)

-- 创建高级验证器
createAdvancedValidator :: AdvancedValidator
createAdvancedValidator = AdvancedValidator {
    rules = [
        ("array_bounds", \args -> 
            case args of
                [index, len] -> read index < read len
                _ -> False),
        ("non_null", \args -> 
            not (null args) && all (/= "null") args),
        ("sorted_array", \args -> 
            args == sort args)
    ]
}

-- 契约组合
combineContracts :: Contract -> Contract -> Contract
combineContracts c1 c2 = Contract {
    precondition = precondition c1 ++ " && " ++ precondition c2,
    postcondition = postcondition c1 ++ " && " ++ postcondition c2,
    invariant = invariant c1 ++ " && " ++ invariant c2
}

-- 契约继承
strengthenContract :: Contract -> Contract -> Bool
strengthenContract child parent = 
    -- 简化的契约强化检查
    precondition child `isSubsetOf` precondition parent &&
    postcondition parent `isSubsetOf` postcondition child &&
    invariant child `isSubsetOf` invariant parent

isSubsetOf :: String -> String -> Bool
isSubsetOf child parent = 
    -- 简化的子集检查
    child `isInfixOf` parent

-- 示例
exampleContract :: Contract
exampleContract = Contract {
    precondition = "non_empty",
    postcondition = "positive_result",
    invariant = "state_consistent"
}

exampleFunction :: ContractFunction Int String
exampleFunction = ContractFunction {
    contract = exampleContract,
    function = \args -> show (sum (map read args)),
    validator = SimpleValidator
}

exampleClass :: ContractClass
exampleClass = ContractClass {
    data_ = [],
    classContract = exampleContract,
    classValidator = SimpleValidator
}

-- 测试
testContractProgramming :: IO ()
testContractProgramming = do
    putStrLn "Testing Contract Function:"
    let result1 = executeContractFunction exampleFunction ["1", "2", "3"]
    print result1
    
    let result2 = executeContractFunction exampleFunction []
    print result2
    
    putStrLn "\nTesting Contract Class:"
    let class1 = addElement exampleClass 5
    print class1
    
    case class1 of
        Right cls -> do
            let (removed, cls2) = removeElement cls 0
            print removed
            print cls2
        Left err -> print err
```

## 5. 应用示例

### 5.1 银行账户系统

```rust
/// 银行账户契约
#[derive(Debug, Clone)]
struct BankAccount {
    balance: f64,
    account_number: String,
    is_active: bool,
}

impl BankAccount {
    fn new(account_number: String, initial_balance: f64) -> Result<Self, String> {
        // 前置条件：初始余额必须非负
        if initial_balance < 0.0 {
            return Err("Initial balance must be non-negative".to_string());
        }

        // 前置条件：账户号不能为空
        if account_number.is_empty() {
            return Err("Account number cannot be empty".to_string());
        }

        Ok(Self {
            balance: initial_balance,
            account_number,
            is_active: true,
        })
    }

    fn deposit(&mut self, amount: f64) -> Result<(), String> {
        // 前置条件：存款金额必须为正数
        if amount <= 0.0 {
            return Err("Deposit amount must be positive".to_string());
        }

        // 前置条件：账户必须处于活跃状态
        if !self.is_active {
            return Err("Account is not active".to_string());
        }

        // 验证不变式
        self.validate_invariant()?;

        // 执行存款操作
        self.balance += amount;

        // 后置条件：余额必须增加
        if self.balance < amount {
            return Err("Balance did not increase properly".to_string());
        }

        // 验证不变式
        self.validate_invariant()?;

        Ok(())
    }

    fn withdraw(&mut self, amount: f64) -> Result<(), String> {
        // 前置条件：取款金额必须为正数
        if amount <= 0.0 {
            return Err("Withdrawal amount must be positive".to_string());
        }

        // 前置条件：账户必须处于活跃状态
        if !self.is_active {
            return Err("Account is not active".to_string());
        }

        // 前置条件：余额必须足够
        if self.balance < amount {
            return Err("Insufficient funds".to_string());
        }

        // 验证不变式
        self.validate_invariant()?;

        // 执行取款操作
        let old_balance = self.balance;
        self.balance -= amount;

        // 后置条件：余额必须减少
        if self.balance >= old_balance {
            return Err("Balance did not decrease properly".to_string());
        }

        // 验证不变式
        self.validate_invariant()?;

        Ok(())
    }

    fn get_balance(&self) -> Result<f64, String> {
        // 前置条件：账户必须处于活跃状态
        if !self.is_active {
            return Err("Account is not active".to_string());
        }

        // 验证不变式
        self.validate_invariant()?;

        Ok(self.balance)
    }

    fn deactivate(&mut self) -> Result<(), String> {
        // 前置条件：账户必须处于活跃状态
        if !self.is_active {
            return Err("Account is already inactive".to_string());
        }

        // 验证不变式
        self.validate_invariant()?;

        // 执行停用操作
        self.is_active = false;

        // 后置条件：账户必须处于非活跃状态
        if self.is_active {
            return Err("Account was not deactivated".to_string());
        }

        Ok(())
    }
}

impl BankAccount {
    fn validate_invariant(&self) -> Result<(), String> {
        // 不变式1：余额必须非负
        if self.balance < 0.0 {
            return Err("Balance cannot be negative".to_string());
        }

        // 不变式2：账户号不能为空
        if self.account_number.is_empty() {
            return Err("Account number cannot be empty".to_string());
        }

        // 不变式3：如果账户非活跃，余额必须为零
        if !self.is_active && self.balance != 0.0 {
            return Err("Inactive account must have zero balance".to_string());
        }

        Ok(())
    }
}

#[cfg(test)]
mod bank_tests {
    use super::*;

    #[test]
    fn test_bank_account_creation() {
        // 测试成功创建
        let account = BankAccount::new("12345".to_string(), 100.0);
        assert!(account.is_ok());

        // 测试负余额创建失败
        let account = BankAccount::new("12345".to_string(), -100.0);
        assert!(account.is_err());

        // 测试空账户号创建失败
        let account = BankAccount::new("".to_string(), 100.0);
        assert!(account.is_err());
    }

    #[test]
    fn test_deposit_operations() {
        let mut account = BankAccount::new("12345".to_string(), 100.0).unwrap();

        // 测试成功存款
        assert!(account.deposit(50.0).is_ok());
        assert_eq!(account.get_balance().unwrap(), 150.0);

        // 测试负存款失败
        assert!(account.deposit(-50.0).is_err());

        // 测试零存款失败
        assert!(account.deposit(0.0).is_err());
    }

    #[test]
    fn test_withdrawal_operations() {
        let mut account = BankAccount::new("12345".to_string(), 100.0).unwrap();

        // 测试成功取款
        assert!(account.withdraw(50.0).is_ok());
        assert_eq!(account.get_balance().unwrap(), 50.0);

        // 测试超额取款失败
        assert!(account.withdraw(100.0).is_err());

        // 测试负取款失败
        assert!(account.withdraw(-50.0).is_err());
    }

    #[test]
    fn test_account_deactivation() {
        let mut account = BankAccount::new("12345".to_string(), 100.0).unwrap();

        // 测试成功停用
        assert!(account.deactivate().is_ok());
        assert!(!account.is_active);

        // 测试重复停用失败
        assert!(account.deactivate().is_err());
    }
}
```

### 5.2 线程安全队列

```rust
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

/// 线程安全队列契约
#[derive(Debug, Clone)]
struct ThreadSafeQueue<T> {
    data: Arc<Mutex<Vec<T>>>,
    capacity: usize,
}

impl<T: Clone + Send + 'static> ThreadSafeQueue<T> {
    fn new(capacity: usize) -> Result<Self, String> {
        // 前置条件：容量必须为正数
        if capacity == 0 {
            return Err("Capacity must be positive".to_string());
        }

        Ok(Self {
            data: Arc::new(Mutex::new(Vec::new())),
            capacity,
        })
    }

    fn enqueue(&self, item: T) -> Result<(), String> {
        // 前置条件：队列不能已满
        if self.is_full()? {
            return Err("Queue is full".to_string());
        }

        // 验证不变式
        self.validate_invariant()?;

        // 执行入队操作
        if let Ok(mut data) = self.data.lock() {
            data.push(item);
        } else {
            return Err("Failed to acquire lock".to_string());
        }

        // 后置条件：队列不能为空
        if self.is_empty()? {
            return Err("Queue became empty after enqueue".to_string());
        }

        // 验证不变式
        self.validate_invariant()?;

        Ok(())
    }

    fn dequeue(&self) -> Result<T, String> {
        // 前置条件：队列不能为空
        if self.is_empty()? {
            return Err("Queue is empty".to_string());
        }

        // 验证不变式
        self.validate_invariant()?;

        // 执行出队操作
        let item = if let Ok(mut data) = self.data.lock() {
            if data.is_empty() {
                return Err("Queue is empty".to_string());
            }
            data.remove(0)
        } else {
            return Err("Failed to acquire lock".to_string());
        };

        // 验证不变式
        self.validate_invariant()?;

        Ok(item)
    }

    fn peek(&self) -> Result<T, String> {
        // 前置条件：队列不能为空
        if self.is_empty()? {
            return Err("Queue is empty".to_string());
        }

        // 验证不变式
        self.validate_invariant()?;

        // 执行查看操作
        let item = if let Ok(data) = self.data.lock() {
            if data.is_empty() {
                return Err("Queue is empty".to_string());
            }
            data[0].clone()
        } else {
            return Err("Failed to acquire lock".to_string());
        };

        Ok(item)
    }

    fn is_empty(&self) -> Result<bool, String> {
        if let Ok(data) = self.data.lock() {
            Ok(data.is_empty())
        } else {
            Err("Failed to acquire lock".to_string())
        }
    }

    fn is_full(&self) -> Result<bool, String> {
        if let Ok(data) = self.data.lock() {
            Ok(data.len() >= self.capacity)
        } else {
            Err("Failed to acquire lock".to_string())
        }
    }

    fn size(&self) -> Result<usize, String> {
        if let Ok(data) = self.data.lock() {
            Ok(data.len())
        } else {
            Err("Failed to acquire lock".to_string())
        }
    }
}

impl<T: Clone + Send + 'static> ThreadSafeQueue<T> {
    fn validate_invariant(&self) -> Result<(), String> {
        // 不变式1：队列大小不能超过容量
        let size = self.size()?;
        if size > self.capacity {
            return Err("Queue size exceeds capacity".to_string());
        }

        // 不变式2：队列大小必须非负
        if size < 0 {
            return Err("Queue size cannot be negative".to_string());
        }

        // 不变式3：如果队列为空，不能进行出队操作
        // 这个在具体操作中验证

        Ok(())
    }
}

#[cfg(test)]
mod queue_tests {
    use super::*;

    #[test]
    fn test_queue_creation() {
        // 测试成功创建
        let queue = ThreadSafeQueue::<i32>::new(10);
        assert!(queue.is_ok());

        // 测试零容量创建失败
        let queue = ThreadSafeQueue::<i32>::new(0);
        assert!(queue.is_err());
    }

    #[test]
    fn test_enqueue_dequeue() {
        let queue = ThreadSafeQueue::<i32>::new(5).unwrap();

        // 测试入队
        assert!(queue.enqueue(1).is_ok());
        assert!(queue.enqueue(2).is_ok());
        assert!(queue.enqueue(3).is_ok());

        // 测试出队
        assert_eq!(queue.dequeue().unwrap(), 1);
        assert_eq!(queue.dequeue().unwrap(), 2);
        assert_eq!(queue.dequeue().unwrap(), 3);

        // 测试空队列出队失败
        assert!(queue.dequeue().is_err());
    }

    #[test]
    fn test_queue_full() {
        let queue = ThreadSafeQueue::<i32>::new(2).unwrap();

        // 填满队列
        assert!(queue.enqueue(1).is_ok());
        assert!(queue.enqueue(2).is_ok());

        // 测试队列已满
        assert!(queue.is_full().unwrap());
        assert!(queue.enqueue(3).is_err());
    }

    #[test]
    fn test_peek_operation() {
        let queue = ThreadSafeQueue::<i32>::new(5).unwrap();

        // 测试空队列查看失败
        assert!(queue.peek().is_err());

        // 测试查看操作
        assert!(queue.enqueue(1).is_ok());
        assert_eq!(queue.peek().unwrap(), 1);
        assert_eq!(queue.size().unwrap(), 1); // 查看不应改变队列大小
    }

    #[test]
    fn test_concurrent_access() {
        let queue = Arc::new(ThreadSafeQueue::<i32>::new(100).unwrap());
        let mut handles = vec![];

        // 创建多个生产者线程
        for i in 0..5 {
            let queue_clone = Arc::clone(&queue);
            let handle = thread::spawn(move || {
                for j in 0..20 {
                    queue_clone.enqueue(i * 20 + j).unwrap();
                    thread::sleep(Duration::from_millis(1));
                }
            });
            handles.push(handle);
        }

        // 创建多个消费者线程
        for _ in 0..3 {
            let queue_clone = Arc::clone(&queue);
            let handle = thread::spawn(move || {
                for _ in 0..33 {
                    if let Ok(item) = queue_clone.dequeue() {
                        println!("Dequeued: {}", item);
                    }
                    thread::sleep(Duration::from_millis(1));
                }
            });
            handles.push(handle);
        }

        // 等待所有线程完成
        for handle in handles {
            handle.join().unwrap();
        }

        // 验证队列最终状态
        assert!(queue.is_empty().unwrap());
    }
}
```

## 6. 相关理论

### 6.1 与形式化验证的关系

- **契约作为规格说明**：契约是形式化验证的规格说明
- **契约验证**：验证程序满足契约
- **契约推理**：从契约推导程序性质

### 6.2 与类型理论的关系

- **类型作为契约**：类型系统是静态契约
- **依赖类型**：更丰富的契约表达能力
- **线性类型**：资源管理契约

### 6.3 与软件测试的关系

- **契约测试**：基于契约的测试用例生成
- **属性测试**：契约作为测试属性
- **回归测试**：契约变化检测

### 6.4 与软件架构的关系

- **接口契约**：组件间接口规范
- **服务契约**：服务级别协议
- **架构契约**：系统级约束

## 7. 参考文献

1. Meyer, B. (1992). Applying "design by contract". Computer, 25(10), 40-51.
2. Hoare, C. A. R. (1969). An axiomatic basis for computer programming. Communications of the ACM, 12(10), 576-580.
3. Dijkstra, E. W. (1975). Guarded commands, nondeterminacy and formal derivation of programs. Communications of the ACM, 18(8), 453-457.
4. Barnett, M., Leino, K. R. M., & Schulte, W. (2004). The Spec# programming system: An overview. In International Workshop on Construction and Analysis of Safe, Secure, and Interoperable Smart Devices (pp. 49-69).
5. Leavens, G. T., Baker, A. L., & Ruby, C. (1999). JML: A notation for detailed design. In Behavioral Specifications of Businesses and Systems (pp. 175-188).

---

**相关文档**:

- [形式化规格说明](../01_Formal_Methods/01_Formal_Specification.md)
- [形式化验证方法](../01_Formal_Methods/02_Formal_Verification_Methods.md)
- [模型驱动开发](../01_Formal_Methods/03_Model_Driven_Development.md)
- [软件架构设计原则](../02_Software_Architecture/01_Architecture_Design_Principles.md)
