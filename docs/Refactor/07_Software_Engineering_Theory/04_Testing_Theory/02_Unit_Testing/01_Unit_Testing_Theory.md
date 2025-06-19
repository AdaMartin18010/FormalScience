# 07.4.2 单元测试理论

## 📋 概述

单元测试是软件测试的基础层次，专注于测试软件的最小可测试单元。本文档从形式化角度分析单元测试的理论基础、数学定义和实现方法。

## 🎯 核心目标

1. **形式化定义**: 建立单元测试的严格数学定义
2. **测试策略**: 系统化分类单元测试策略
3. **理论证明**: 提供单元测试正确性的形式化证明
4. **代码实现**: 提供完整的Rust实现示例

## 📚 目录

1. [基本概念](#1-基本概念)
2. [形式化定义](#2-形式化定义)
3. [测试策略](#3-测试策略)
4. [定理与证明](#4-定理与证明)
5. [代码实现](#5-代码实现)
6. [应用示例](#6-应用示例)
7. [相关理论](#7-相关理论)
8. [参考文献](#8-参考文献)

## 1. 基本概念

### 1.1 单元测试定义

**定义 1.1** (单元)
单元是软件中最小的可独立测试的组件，通常是一个函数、方法或类。

**定义 1.2** (单元测试)
单元测试是验证单个单元在隔离环境下正确性的测试过程。

### 1.2 核心原则

**原则 1.1** (独立性)
单元测试应独立于其他测试和外部依赖。

**原则 1.2** (快速性)
单元测试应快速执行，通常在毫秒级别。

**原则 1.3** (确定性)
单元测试结果应具有确定性和可重复性。

## 2. 形式化定义

### 2.1 单元形式化

**定义 2.1** (单元)
单元 $U$ 是一个函数 $U: D \rightarrow R$，其中：
- $D$ 是输入域
- $R$ 是输出域

### 2.2 单元测试形式化

**定义 2.2** (单元测试)
单元测试是一个三元组 $(U, T, V)$，其中：
- $U$ 是被测试单元
- $T$ 是测试用例集合
- $V$ 是验证函数 $V: R \times R \rightarrow \text{Bool}$

### 2.3 测试覆盖形式化

**定义 2.3** (语句覆盖)
语句覆盖 $C_s(U, T) = \frac{|S_{executed}|}{|S_{total}|}$，其中：
- $S_{executed}$ 是执行的语句集合
- $S_{total}$ 是总语句集合

## 3. 测试策略

### 3.1 测试用例设计策略

| 策略名称 | 英文名称 | 核心思想 | 适用场景 |
|---------|---------|---------|---------|
| 等价类划分 | Equivalence Partitioning | 输入域划分 | 数值计算 |
| 边界值分析 | Boundary Value Analysis | 边界条件测试 | 范围验证 |
| 错误推测 | Error Guessing | 经验性测试 | 缺陷发现 |
| 因果图 | Cause-Effect Graphing | 因果关系分析 | 逻辑测试 |

### 3.2 测试类型分类

| 测试类型 | 英文名称 | 测试目标 | 实现方式 |
|---------|---------|---------|---------|
| 功能测试 | Functional Testing | 验证功能正确性 | 输入输出验证 |
| 边界测试 | Boundary Testing | 验证边界条件 | 边界值测试 |
| 异常测试 | Exception Testing | 验证异常处理 | 异常输入测试 |
| 性能测试 | Performance Testing | 验证性能要求 | 时间测量 |

### 3.3 测试模式

| 模式名称 | 英文名称 | 核心思想 | 适用场景 |
|---------|---------|---------|---------|
| AAA模式 | Arrange-Act-Assert | 准备-执行-断言 | 标准测试 |
| Given-When-Then | Given-When-Then | 给定-当-那么 | BDD测试 |
| Setup-Exercise-Verify | Setup-Exercise-Verify | 设置-执行-验证 | 复杂测试 |

## 4. 定理与证明

### 4.1 单元测试充分性定理

**定理 4.1** (单元测试充分性)
如果单元测试的语句覆盖率达到100%，则能够发现单元中的大部分逻辑错误。

**证明**：
1. 设错误集合为 $E = \{e_1, e_2, ..., e_n\}$
2. 每个错误 $e_i$ 对应一个语句 $s_i$
3. 100%语句覆盖确保所有语句都被执行
4. 因此所有错误都能被发现。□

### 4.2 单元测试独立性定理

**定理 4.2** (单元测试独立性)
独立的单元测试能够并行执行，提高测试效率。

**证明**：
1. 设测试集合 $T = \{t_1, t_2, ..., t_n\}$
2. 每个测试 $t_i$ 只依赖单元 $U_i$
3. 不同单元间无依赖关系
4. 因此测试可以并行执行。□

## 5. 代码实现

### 5.1 单元测试框架实现

```rust
use std::fmt::Debug;
use std::time::Instant;

/// 单元测试特征
pub trait UnitTest: Debug {
    fn name(&self) -> &str;
    fn run(&self) -> UnitTestResult;
    fn setup(&self) -> Result<(), String> { Ok(()) }
    fn teardown(&self) -> Result<(), String> { Ok(()) }
}

/// 单元测试结果
#[derive(Debug, Clone)]
pub enum UnitTestResult {
    Pass,
    Fail(String),
    Error(String),
    Skip(String),
}

/// 单元测试套件
#[derive(Debug)]
pub struct UnitTestSuite {
    name: String,
    tests: Vec<Box<dyn UnitTest>>,
    setup_hook: Option<Box<dyn Fn() -> Result<(), String>>>,
    teardown_hook: Option<Box<dyn Fn() -> Result<(), String>>>,
}

impl UnitTestSuite {
    pub fn new(name: String) -> Self {
        UnitTestSuite {
            name,
            tests: Vec::new(),
            setup_hook: None,
            teardown_hook: None,
        }
    }
    
    pub fn add_test(&mut self, test: Box<dyn UnitTest>) {
        self.tests.push(test);
    }
    
    pub fn set_setup_hook<F>(&mut self, hook: F)
    where
        F: Fn() -> Result<(), String> + 'static,
    {
        self.setup_hook = Some(Box::new(hook));
    }
    
    pub fn set_teardown_hook<F>(&mut self, hook: F)
    where
        F: Fn() -> Result<(), String> + 'static,
    {
        self.teardown_hook = Some(Box::new(hook));
    }
    
    pub fn run_all(&self) -> UnitTestReport {
        let mut report = UnitTestReport::new(self.name.clone());
        let start_time = Instant::now();
        
        // 全局设置
        if let Some(ref setup) = self.setup_hook {
            if let Err(e) = setup() {
                report.add_error("Global Setup", e);
                return report;
            }
        }
        
        // 运行所有测试
        for test in &self.tests {
            let test_start = Instant::now();
            let result = self.run_single_test(test);
            let duration = test_start.elapsed();
            
            report.add_result(test.name(), result, duration);
        }
        
        // 全局清理
        if let Some(ref teardown) = self.teardown_hook {
            if let Err(e) = teardown() {
                report.add_error("Global Teardown", e);
            }
        }
        
        report.set_total_duration(start_time.elapsed());
        report
    }
    
    fn run_single_test(&self, test: &Box<dyn UnitTest>) -> UnitTestResult {
        // 测试设置
        if let Err(e) = test.setup() {
            return UnitTestResult::Error(format!("Setup failed: {}", e));
        }
        
        // 运行测试
        let result = test.run();
        
        // 测试清理
        if let Err(e) = test.teardown() {
            return UnitTestResult::Error(format!("Teardown failed: {}", e));
        }
        
        result
    }
}

/// 单元测试报告
#[derive(Debug)]
pub struct UnitTestReport {
    suite_name: String,
    results: Vec<UnitTestResultItem>,
    errors: Vec<(String, String)>,
    total_duration: Option<std::time::Duration>,
}

#[derive(Debug)]
struct UnitTestResultItem {
    test_name: String,
    result: UnitTestResult,
    duration: std::time::Duration,
}

impl UnitTestReport {
    pub fn new(suite_name: String) -> Self {
        UnitTestReport {
            suite_name,
            results: Vec::new(),
            errors: Vec::new(),
            total_duration: None,
        }
    }
    
    pub fn add_result(&mut self, test_name: &str, result: UnitTestResult, duration: std::time::Duration) {
        self.results.push(UnitTestResultItem {
            test_name: test_name.to_string(),
            result,
            duration,
        });
    }
    
    pub fn add_error(&mut self, context: &str, error: String) {
        self.errors.push((context.to_string(), error));
    }
    
    pub fn set_total_duration(&mut self, duration: std::time::Duration) {
        self.total_duration = Some(duration);
    }
    
    pub fn summary(&self) -> UnitTestSummary {
        let total = self.results.len();
        let passed = self.results.iter()
            .filter(|r| matches!(r.result, UnitTestResult::Pass))
            .count();
        let failed = self.results.iter()
            .filter(|r| matches!(r.result, UnitTestResult::Fail(_)))
            .count();
        let errors = self.results.iter()
            .filter(|r| matches!(r.result, UnitTestResult::Error(_)))
            .count();
        let skipped = self.results.iter()
            .filter(|r| matches!(r.result, UnitTestResult::Skip(_)))
            .count();
        
        UnitTestSummary {
            total,
            passed,
            failed,
            errors,
            skipped,
            total_duration: self.total_duration,
        }
    }
    
    pub fn print_report(&self) {
        println!("=== Unit Test Report: {} ===", self.suite_name);
        
        if let Some(duration) = self.total_duration {
            println!("Total Duration: {:?}", duration);
        }
        
        println!();
        
        for result in &self.results {
            match &result.result {
                UnitTestResult::Pass => {
                    println!("✅ {}: PASS ({:?})", result.test_name, result.duration);
                }
                UnitTestResult::Fail(reason) => {
                    println!("❌ {}: FAIL - {} ({:?})", result.test_name, reason, result.duration);
                }
                UnitTestResult::Error(reason) => {
                    println!("💥 {}: ERROR - {} ({:?})", result.test_name, reason, result.duration);
                }
                UnitTestResult::Skip(reason) => {
                    println!("⏭️ {}: SKIP - {} ({:?})", result.test_name, reason, result.duration);
                }
            }
        }
        
        if !self.errors.is_empty() {
            println!("\n=== Errors ===");
            for (context, error) in &self.errors {
                println!("{}: {}", context, error);
            }
        }
        
        println!();
        let summary = self.summary();
        println!("Summary: {}/{} tests passed", summary.passed, summary.total);
    }
}

/// 单元测试摘要
#[derive(Debug)]
pub struct UnitTestSummary {
    pub total: usize,
    pub passed: usize,
    pub failed: usize,
    pub errors: usize,
    pub skipped: usize,
    pub total_duration: Option<std::time::Duration>,
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_unit_test_suite_creation() {
        let suite = UnitTestSuite::new("TestSuite".to_string());
        assert_eq!(suite.name, "TestSuite");
    }
}
```

### 5.2 测试用例生成器

```rust
use std::fmt::Debug;

/// 测试用例生成器特征
pub trait TestCaseGenerator<T> {
    fn generate_test_cases(&self) -> Vec<T>;
}

/// 等价类测试用例生成器
#[derive(Debug)]
pub struct EquivalenceClassGenerator<T> {
    classes: Vec<Vec<T>>,
}

impl<T: Clone> EquivalenceClassGenerator<T> {
    pub fn new(classes: Vec<Vec<T>>) -> Self {
        EquivalenceClassGenerator { classes }
    }
    
    pub fn integer_equivalence_classes() -> EquivalenceClassGenerator<i32> {
        EquivalenceClassGenerator::new(vec![
            vec![i32::MIN, -1000, -100, -10, -1], // 负数类
            vec![0], // 零类
            vec![1, 10, 100, 1000, i32::MAX], // 正数类
        ])
    }
    
    pub fn string_equivalence_classes() -> EquivalenceClassGenerator<String> {
        EquivalenceClassGenerator::new(vec![
            vec!["".to_string()], // 空字符串类
            vec!["a".to_string(), "hello".to_string()], // 正常字符串类
            vec!["a".repeat(1000)], // 长字符串类
        ])
    }
}

impl<T: Clone> TestCaseGenerator<T> for EquivalenceClassGenerator<T> {
    fn generate_test_cases(&self) -> Vec<T> {
        let mut cases = Vec::new();
        for class in &self.classes {
            cases.extend_from_slice(class);
        }
        cases
    }
}

/// 边界值测试用例生成器
#[derive(Debug)]
pub struct BoundaryValueGenerator<T> {
    values: Vec<T>,
}

impl<T: Clone> BoundaryValueGenerator<T> {
    pub fn new(values: Vec<T>) -> Self {
        BoundaryValueGenerator { values }
    }
    
    pub fn integer_boundaries() -> BoundaryValueGenerator<i32> {
        BoundaryValueGenerator::new(vec![
            i32::MIN,
            i32::MIN + 1,
            -1,
            0,
            1,
            i32::MAX - 1,
            i32::MAX,
        ])
    }
    
    pub fn string_boundaries() -> BoundaryValueGenerator<String> {
        BoundaryValueGenerator::new(vec![
            "".to_string(),
            "a".to_string(),
            "ab".to_string(),
            "a".repeat(1000),
        ])
    }
}

impl<T: Clone> TestCaseGenerator<T> for BoundaryValueGenerator<T> {
    fn generate_test_cases(&self) -> Vec<T> {
        self.values.clone()
    }
}

/// 组合测试用例生成器
#[derive(Debug)]
pub struct CombinatorialGenerator<T> {
    parameters: Vec<Vec<T>>,
}

impl<T: Clone> CombinatorialGenerator<T> {
    pub fn new(parameters: Vec<Vec<T>>) -> Self {
        CombinatorialGenerator { parameters }
    }
    
    pub fn pairwise() -> CombinatorialGenerator<i32> {
        CombinatorialGenerator::new(vec![
            vec![1, 2, 3], // 参数1
            vec![10, 20], // 参数2
            vec![100, 200, 300], // 参数3
        ])
    }
}

impl<T: Clone> TestCaseGenerator<Vec<T>> for CombinatorialGenerator<T> {
    fn generate_test_cases(&self) -> Vec<Vec<T>> {
        self.generate_combinations(0, Vec::new())
    }
    
    fn generate_combinations(&self, index: usize, current: Vec<T>) -> Vec<Vec<T>> {
        if index >= self.parameters.len() {
            return vec![current];
        }
        
        let mut combinations = Vec::new();
        for value in &self.parameters[index] {
            let mut new_current = current.clone();
            new_current.push(value.clone());
            combinations.extend(self.generate_combinations(index + 1, new_current));
        }
        combinations
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_equivalence_class_generator() {
        let generator = EquivalenceClassGenerator::integer_equivalence_classes();
        let cases = generator.generate_test_cases();
        assert!(!cases.is_empty());
    }
    
    #[test]
    fn test_boundary_value_generator() {
        let generator = BoundaryValueGenerator::integer_boundaries();
        let cases = generator.generate_test_cases();
        assert_eq!(cases.len(), 7);
    }
    
    #[test]
    fn test_combinatorial_generator() {
        let generator = CombinatorialGenerator::pairwise();
        let cases = generator.generate_test_cases();
        assert_eq!(cases.len(), 18); // 3 * 2 * 3
    }
}
```

### 5.3 模拟对象框架

```rust
use std::collections::HashMap;
use std::fmt::Debug;

/// 模拟对象特征
pub trait MockObject: Debug {
    fn verify(&self) -> Result<(), String>;
}

/// 方法调用记录
#[derive(Debug, Clone)]
pub struct MethodCall {
    method_name: String,
    arguments: Vec<String>,
    return_value: Option<String>,
}

/// 通用模拟对象
#[derive(Debug)]
pub struct GenericMock {
    name: String,
    expected_calls: Vec<MethodCall>,
    actual_calls: Vec<MethodCall>,
}

impl GenericMock {
    pub fn new(name: String) -> Self {
        GenericMock {
            name,
            expected_calls: Vec::new(),
            actual_calls: Vec::new(),
        }
    }
    
    pub fn expect_call(&mut self, method_name: &str, arguments: Vec<String>, return_value: Option<String>) {
        self.expected_calls.push(MethodCall {
            method_name: method_name.to_string(),
            arguments,
            return_value,
        });
    }
    
    pub fn record_call(&mut self, method_name: &str, arguments: Vec<String>) -> Option<String> {
        let call = MethodCall {
            method_name: method_name.to_string(),
            arguments,
            return_value: None,
        };
        self.actual_calls.push(call);
        
        // 查找匹配的预期调用
        for expected in &self.expected_calls {
            if expected.method_name == method_name {
                return expected.return_value.clone();
            }
        }
        
        None
    }
}

impl MockObject for GenericMock {
    fn verify(&self) -> Result<(), String> {
        if self.actual_calls.len() != self.expected_calls.len() {
            return Err(format!(
                "Expected {} calls, but got {}",
                self.expected_calls.len(),
                self.actual_calls.len()
            ));
        }
        
        for (i, (expected, actual)) in self.expected_calls.iter().zip(self.actual_calls.iter()).enumerate() {
            if expected.method_name != actual.method_name {
                return Err(format!(
                    "Call {}: Expected method '{}', but got '{}'",
                    i, expected.method_name, actual.method_name
                ));
            }
        }
        
        Ok(())
    }
}

/// 数据库模拟对象
#[derive(Debug)]
pub struct DatabaseMock {
    mock: GenericMock,
    data: HashMap<String, String>,
}

impl DatabaseMock {
    pub fn new() -> Self {
        DatabaseMock {
            mock: GenericMock::new("Database".to_string()),
            data: HashMap::new(),
        }
    }
    
    pub fn expect_query(&mut self, query: &str, result: &str) {
        self.mock.expect_call("query", vec![query.to_string()], Some(result.to_string()));
    }
    
    pub fn query(&mut self, query: &str) -> Option<String> {
        self.mock.record_call("query", vec![query.to_string()])
    }
    
    pub fn expect_insert(&mut self, table: &str, data: &str) {
        self.mock.expect_call("insert", vec![table.to_string(), data.to_string()], None);
    }
    
    pub fn insert(&mut self, table: &str, data: &str) {
        self.mock.record_call("insert", vec![table.to_string(), data.to_string()]);
        self.data.insert(format!("{}:{}", table, data), "inserted".to_string());
    }
}

impl MockObject for DatabaseMock {
    fn verify(&self) -> Result<(), String> {
        self.mock.verify()
    }
}

/// 网络服务模拟对象
#[derive(Debug)]
pub struct NetworkServiceMock {
    mock: GenericMock,
    responses: HashMap<String, String>,
}

impl NetworkServiceMock {
    pub fn new() -> Self {
        NetworkServiceMock {
            mock: GenericMock::new("NetworkService".to_string()),
            responses: HashMap::new(),
        }
    }
    
    pub fn expect_get(&mut self, url: &str, response: &str) {
        self.mock.expect_call("get", vec![url.to_string()], Some(response.to_string()));
        self.responses.insert(url.to_string(), response.to_string());
    }
    
    pub fn get(&mut self, url: &str) -> Option<String> {
        self.mock.record_call("get", vec![url.to_string()]);
        self.responses.get(url).cloned()
    }
}

impl MockObject for NetworkServiceMock {
    fn verify(&self) -> Result<(), String> {
        self.mock.verify()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_database_mock() {
        let mut db = DatabaseMock::new();
        db.expect_query("SELECT * FROM users", "user1,user2");
        db.expect_insert("users", "new_user");
        
        let result = db.query("SELECT * FROM users");
        assert_eq!(result, Some("user1,user2".to_string()));
        
        db.insert("users", "new_user");
        
        assert!(db.verify().is_ok());
    }
    
    #[test]
    fn test_network_service_mock() {
        let mut service = NetworkServiceMock::new();
        service.expect_get("https://api.example.com/users", r#"{"users": []}"#);
        
        let result = service.get("https://api.example.com/users");
        assert_eq!(result, Some(r#"{"users": []}"#.to_string()));
        
        assert!(service.verify().is_ok());
    }
}
```

## 6. 应用示例

### 6.1 数学函数单元测试

```rust
use std::fmt::Debug;

/// 数学函数库
pub struct MathFunctions;

impl MathFunctions {
    /// 计算阶乘
    pub fn factorial(n: u32) -> Result<u64, String> {
        if n > 20 {
            return Err("Input too large for factorial calculation".to_string());
        }
        
        if n == 0 || n == 1 {
            return Ok(1);
        }
        
        let mut result = 1u64;
        for i in 2..=n {
            result = result.checked_mul(i as u64)
                .ok_or_else(|| "Overflow in factorial calculation".to_string())?;
        }
        
        Ok(result)
    }
    
    /// 计算斐波那契数
    pub fn fibonacci(n: u32) -> Result<u64, String> {
        if n > 93 {
            return Err("Input too large for fibonacci calculation".to_string());
        }
        
        if n == 0 {
            return Ok(0);
        }
        if n == 1 {
            return Ok(1);
        }
        
        let mut a = 0u64;
        let mut b = 1u64;
        
        for _ in 2..=n {
            let temp = a + b;
            a = b;
            b = temp;
        }
        
        Ok(b)
    }
    
    /// 判断是否为素数
    pub fn is_prime(n: u32) -> bool {
        if n < 2 {
            return false;
        }
        if n == 2 {
            return true;
        }
        if n % 2 == 0 {
            return false;
        }
        
        let sqrt_n = (n as f64).sqrt() as u32;
        for i in (3..=sqrt_n).step_by(2) {
            if n % i == 0 {
                return false;
            }
        }
        
        true
    }
}

/// 阶乘函数测试
#[derive(Debug)]
pub struct FactorialTest {
    input: u32,
    expected: Result<u64, String>,
}

impl FactorialTest {
    pub fn new(input: u32, expected: Result<u64, String>) -> Self {
        FactorialTest { input, expected }
    }
}

impl UnitTest for FactorialTest {
    fn name(&self) -> &str {
        &format!("factorial({})", self.input)
    }
    
    fn run(&self) -> UnitTestResult {
        let result = MathFunctions::factorial(self.input);
        
        match (&result, &self.expected) {
            (Ok(r), Ok(e)) if r == e => UnitTestResult::Pass,
            (Err(r), Err(e)) if r == e => UnitTestResult::Pass,
            _ => UnitTestResult::Fail(format!(
                "Expected {:?}, but got {:?}",
                self.expected, result
            )),
        }
    }
}

/// 斐波那契函数测试
#[derive(Debug)]
pub struct FibonacciTest {
    input: u32,
    expected: Result<u64, String>,
}

impl FibonacciTest {
    pub fn new(input: u32, expected: Result<u64, String>) -> Self {
        FibonacciTest { input, expected }
    }
}

impl UnitTest for FibonacciTest {
    fn name(&self) -> &str {
        &format!("fibonacci({})", self.input)
    }
    
    fn run(&self) -> UnitTestResult {
        let result = MathFunctions::fibonacci(self.input);
        
        match (&result, &self.expected) {
            (Ok(r), Ok(e)) if r == e => UnitTestResult::Pass,
            (Err(r), Err(e)) if r == e => UnitTestResult::Pass,
            _ => UnitTestResult::Fail(format!(
                "Expected {:?}, but got {:?}",
                self.expected, result
            )),
        }
    }
}

/// 素数判断测试
#[derive(Debug)]
pub struct IsPrimeTest {
    input: u32,
    expected: bool,
}

impl IsPrimeTest {
    pub fn new(input: u32, expected: bool) -> Self {
        IsPrimeTest { input, expected }
    }
}

impl UnitTest for IsPrimeTest {
    fn name(&self) -> &str {
        &format!("is_prime({})", self.input)
    }
    
    fn run(&self) -> UnitTestResult {
        let result = MathFunctions::is_prime(self.input);
        
        if result == self.expected {
            UnitTestResult::Pass
        } else {
            UnitTestResult::Fail(format!(
                "Expected {}, but got {}",
                self.expected, result
            ))
        }
    }
}

/// 数学函数测试套件
pub struct MathFunctionsTestSuite;

impl MathFunctionsTestSuite {
    pub fn create() -> UnitTestSuite {
        let mut suite = UnitTestSuite::new("Math Functions Tests".to_string());
        
        // 阶乘测试
        suite.add_test(Box::new(FactorialTest::new(0, Ok(1))));
        suite.add_test(Box::new(FactorialTest::new(1, Ok(1))));
        suite.add_test(Box::new(FactorialTest::new(5, Ok(120))));
        suite.add_test(Box::new(FactorialTest::new(10, Ok(3628800))));
        suite.add_test(Box::new(FactorialTest::new(21, Err("Input too large for factorial calculation".to_string()))));
        
        // 斐波那契测试
        suite.add_test(Box::new(FibonacciTest::new(0, Ok(0))));
        suite.add_test(Box::new(FibonacciTest::new(1, Ok(1))));
        suite.add_test(Box::new(FibonacciTest::new(5, Ok(5))));
        suite.add_test(Box::new(FibonacciTest::new(10, Ok(55))));
        suite.add_test(Box::new(FibonacciTest::new(94, Err("Input too large for fibonacci calculation".to_string()))));
        
        // 素数测试
        suite.add_test(Box::new(IsPrimeTest::new(0, false)));
        suite.add_test(Box::new(IsPrimeTest::new(1, false)));
        suite.add_test(Box::new(IsPrimeTest::new(2, true)));
        suite.add_test(Box::new(IsPrimeTest::new(3, true)));
        suite.add_test(Box::new(IsPrimeTest::new(4, false)));
        suite.add_test(Box::new(IsPrimeTest::new(17, true)));
        suite.add_test(Box::new(IsPrimeTest::new(25, false)));
        
        suite
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_math_functions_suite() {
        let suite = MathFunctionsTestSuite::create();
        let report = suite.run_all();
        report.print_report();
        
        let summary = report.summary();
        assert!(summary.passed > 0);
    }
}
```

### 6.2 字符串处理单元测试

```rust
use std::fmt::Debug;

/// 字符串处理工具
pub struct StringUtils;

impl StringUtils {
    /// 反转字符串
    pub fn reverse(s: &str) -> String {
        s.chars().rev().collect()
    }
    
    /// 判断是否为回文
    pub fn is_palindrome(s: &str) -> bool {
        let cleaned: String = s.chars()
            .filter(|c| c.is_alphanumeric())
            .map(|c| c.to_lowercase().next().unwrap())
            .collect();
        
        let reversed: String = cleaned.chars().rev().collect();
        cleaned == reversed
    }
    
    /// 计算字符频率
    pub fn character_frequency(s: &str) -> std::collections::HashMap<char, usize> {
        let mut freq = std::collections::HashMap::new();
        for ch in s.chars() {
            *freq.entry(ch).or_insert(0) += 1;
        }
        freq
    }
    
    /// 查找最长公共子序列
    pub fn longest_common_subsequence(s1: &str, s2: &str) -> String {
        let chars1: Vec<char> = s1.chars().collect();
        let chars2: Vec<char> = s2.chars().collect();
        let m = chars1.len();
        let n = chars2.len();
        
        let mut dp = vec![vec![0; n + 1]; m + 1];
        
        for i in 1..=m {
            for j in 1..=n {
                if chars1[i - 1] == chars2[j - 1] {
                    dp[i][j] = dp[i - 1][j - 1] + 1;
                } else {
                    dp[i][j] = dp[i - 1][j].max(dp[i][j - 1]);
                }
            }
        }
        
        let mut result = String::new();
        let mut i = m;
        let mut j = n;
        
        while i > 0 && j > 0 {
            if chars1[i - 1] == chars2[j - 1] {
                result.insert(0, chars1[i - 1]);
                i -= 1;
                j -= 1;
            } else if dp[i - 1][j] > dp[i][j - 1] {
                i -= 1;
            } else {
                j -= 1;
            }
        }
        
        result
    }
}

/// 字符串反转测试
#[derive(Debug)]
pub struct ReverseTest {
    input: String,
    expected: String,
}

impl ReverseTest {
    pub fn new(input: String, expected: String) -> Self {
        ReverseTest { input, expected }
    }
}

impl UnitTest for ReverseTest {
    fn name(&self) -> &str {
        &format!("reverse(\"{}\")", self.input)
    }
    
    fn run(&self) -> UnitTestResult {
        let result = StringUtils::reverse(&self.input);
        
        if result == self.expected {
            UnitTestResult::Pass
        } else {
            UnitTestResult::Fail(format!(
                "Expected \"{}\", but got \"{}\"",
                self.expected, result
            ))
        }
    }
}

/// 回文判断测试
#[derive(Debug)]
pub struct PalindromeTest {
    input: String,
    expected: bool,
}

impl PalindromeTest {
    pub fn new(input: String, expected: bool) -> Self {
        PalindromeTest { input, expected }
    }
}

impl UnitTest for PalindromeTest {
    fn name(&self) -> &str {
        &format!("is_palindrome(\"{}\")", self.input)
    }
    
    fn run(&self) -> UnitTestResult {
        let result = StringUtils::is_palindrome(&self.input);
        
        if result == self.expected {
            UnitTestResult::Pass
        } else {
            UnitTestResult::Fail(format!(
                "Expected {}, but got {}",
                self.expected, result
            ))
        }
    }
}

/// 字符串工具测试套件
pub struct StringUtilsTestSuite;

impl StringUtilsTestSuite {
    pub fn create() -> UnitTestSuite {
        let mut suite = UnitTestSuite::new("String Utils Tests".to_string());
        
        // 反转测试
        suite.add_test(Box::new(ReverseTest::new("".to_string(), "".to_string())));
        suite.add_test(Box::new(ReverseTest::new("a".to_string(), "a".to_string())));
        suite.add_test(Box::new(ReverseTest::new("hello".to_string(), "olleh".to_string())));
        suite.add_test(Box::new(ReverseTest::new("racecar".to_string(), "racecar".to_string())));
        
        // 回文测试
        suite.add_test(Box::new(PalindromeTest::new("".to_string(), true)));
        suite.add_test(Box::new(PalindromeTest::new("a".to_string(), true)));
        suite.add_test(Box::new(PalindromeTest::new("racecar".to_string(), true)));
        suite.add_test(Box::new(PalindromeTest::new("hello".to_string(), false)));
        suite.add_test(Box::new(PalindromeTest::new("A man a plan a canal Panama".to_string(), true)));
        
        suite
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_string_utils_suite() {
        let suite = StringUtilsTestSuite::create();
        let report = suite.run_all();
        report.print_report();
        
        let summary = report.summary();
        assert!(summary.passed > 0);
    }
}
```

## 7. 相关理论

### 7.1 测试理论
- [测试理论基础](../01_Testing_Foundations/01_Testing_Foundations_Theory.md)
- [集成测试理论](../03_Integration_Testing/01_Integration_Testing_Theory.md)
- [系统测试理论](../04_System_Testing/01_System_Testing_Theory.md)

### 7.2 软件工程理论
- [软件质量理论](../05_Software_Quality/01_Software_Quality_Theory.md)
- [软件验证理论](../06_Software_Verification/01_Software_Verification_Theory.md)
- [软件维护理论](../07_Software_Maintenance/01_Software_Maintenance_Theory.md)

### 7.3 形式化方法
- [形式化规格说明](../01_Formal_Specification/01_Formal_Specification_Theory.md)
- [形式化验证方法](../02_Formal_Verification/01_Formal_Verification_Theory.md)
- [模型检测理论](../03_Model_Checking/01_Model_Checking_Theory.md)

## 8. 参考文献

1. Beck, K. (2002). Test Driven Development: By Example. Addison-Wesley.
2. Freeman, S., & Pryce, N. (2009). Growing Object-Oriented Software, Guided by Tests. Addison-Wesley.
3. Meszaros, G. (2007). xUnit Test Patterns: Refactoring Test Code. Addison-Wesley.
4. Fowler, M. (2006). Refactoring: Improving the Design of Existing Code. Addison-Wesley.
5. Martin, R. C. (2008). Clean Code: A Handbook of Agile Software Craftsmanship. Prentice Hall.

---

**最后更新**: 2024年12月21日  
**维护者**: AI助手  
**版本**: v1.0 