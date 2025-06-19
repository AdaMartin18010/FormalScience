# 07.5.1 软件质量理论

## 📋 概述

软件质量理论是软件工程的核心组成部分，研究如何定义、测量、评估和改进软件系统的质量属性。本文档从形式化角度分析软件质量的理论基础、数学定义和实现方法。

## 🎯 核心目标

1. **形式化定义**: 建立软件质量的严格数学定义
2. **质量模型**: 系统化分类软件质量属性
3. **理论证明**: 提供质量评估的形式化证明
4. **代码实现**: 提供完整的Rust实现示例

## 📚 目录

1. [基本概念](#1-基本概念)
2. [形式化定义](#2-形式化定义)
3. [质量模型](#3-质量模型)
4. [定理与证明](#4-定理与证明)
5. [代码实现](#5-代码实现)
6. [应用示例](#6-应用示例)
7. [相关理论](#7-相关理论)
8. [参考文献](#8-参考文献)

## 1. 基本概念

### 1.1 软件质量定义

**定义 1.1** (软件质量)
软件质量是软件系统满足明确和隐含需求的程度，以及满足用户期望的能力。

**定义 1.2** (质量属性)
质量属性是软件系统的可测量特性，用于评估其质量水平。

### 1.2 核心原则

**原则 1.1** (用户导向)
软件质量应以满足用户需求为核心。

**原则 1.2** (可测量性)
质量属性应具有可测量和可量化的特征。

**原则 1.3** (平衡性)
不同质量属性之间需要平衡和权衡。

## 2. 形式化定义

### 2.1 软件质量形式化

**定义 2.1** (软件质量)
软件质量 $Q$ 是一个函数 $Q: S \times R \rightarrow [0,1]$，其中：

- $S$ 是软件系统集合
- $R$ 是需求集合
- $Q(s, r)$ 表示系统 $s$ 满足需求 $r$ 的程度

### 2.2 质量属性形式化

**定义 2.2** (质量属性)
质量属性 $A$ 是一个函数 $A: S \rightarrow V$，其中：

- $S$ 是软件系统集合
- $V$ 是属性值域

### 2.3 质量评估形式化

**定义 2.3** (质量评估)
质量评估是一个函数 $E: S \times A_1 \times A_2 \times ... \times A_n \rightarrow Q$，其中：

- $A_i$ 是质量属性
- $Q$ 是综合质量分数

## 3. 质量模型

### 3.1 ISO 9126质量模型

| 质量特性 | 英文名称 | 子特性 | 测量方法 |
|---------|---------|--------|---------|
| 功能性 | Functionality | 适合性、准确性、互操作性、安全性、依从性 | 功能测试、需求覆盖 |
| 可靠性 | Reliability | 成熟性、容错性、易恢复性 | 故障率、MTBF、可用性 |
| 易用性 | Usability | 易理解性、易学性、易操作性、吸引性 | 用户测试、可用性评估 |
| 效率 | Efficiency | 时间特性、资源特性 | 性能测试、资源监控 |
| 可维护性 | Maintainability | 易分析性、易改变性、稳定性、易测试性 | 代码复杂度、修改成本 |
| 可移植性 | Portability | 适应性、易安装性、共存性、易替换性 | 平台兼容性、部署测试 |

### 3.2 质量属性分类

| 分类 | 属性类型 | 特点 | 评估方法 |
|------|---------|------|---------|
| 外部质量 | External Quality | 用户可见的质量 | 用户测试、验收测试 |
| 内部质量 | Internal Quality | 开发者可见的质量 | 代码审查、静态分析 |
| 过程质量 | Process Quality | 开发过程的质量 | 过程评估、CMMI |

### 3.3 质量度量指标

| 度量类型 | 英文名称 | 计算公式 | 目标值 |
|---------|---------|---------|--------|
| 代码覆盖率 | Code Coverage | 已执行代码行数/总代码行数 | >80% |
| 圈复杂度 | Cyclomatic Complexity | 控制流图中的边数-节点数+2 | <10 |
| 缺陷密度 | Defect Density | 缺陷数/代码行数 | <1/KLOC |
| 平均故障间隔 | MTBF | 总运行时间/故障次数 | 最大化 |
| 响应时间 | Response Time | 请求到响应的时间 | <2秒 |

## 4. 定理与证明

### 4.1 质量传递定理

**定理 4.1** (质量传递)
内部质量影响外部质量，过程质量影响内部质量。

**证明**：

1. 设内部质量为 $Q_i$，外部质量为 $Q_e$，过程质量为 $Q_p$
2. 内部质量直接影响代码结构和实现
3. 代码结构影响外部可见的功能和性能
4. 因此 $Q_p \rightarrow Q_i \rightarrow Q_e$。□

### 4.2 质量权衡定理

**定理 4.2** (质量权衡)
不同质量属性之间存在权衡关系，无法同时优化所有属性。

**证明**：

1. 设质量属性集合为 $A = \{a_1, a_2, ..., a_n\}$
2. 优化属性 $a_i$ 可能影响属性 $a_j$
3. 例如：优化性能可能降低可维护性
4. 因此存在权衡关系。□

## 5. 代码实现

### 5.1 质量评估框架

```rust
use std::fmt::Debug;
use std::collections::HashMap;
use std::time::{Instant, Duration};

/// 质量属性特征
pub trait QualityAttribute: Debug {
    fn name(&self) -> &str;
    fn category(&self) -> QualityCategory;
    fn measure(&self, system: &dyn SoftwareSystem) -> QualityMetric;
    fn weight(&self) -> f64;
}

/// 质量类别
#[derive(Debug, Clone)]
pub enum QualityCategory {
    Functionality,
    Reliability,
    Usability,
    Efficiency,
    Maintainability,
    Portability,
}

/// 质量度量
#[derive(Debug, Clone)]
pub struct QualityMetric {
    pub name: String,
    pub value: f64,
    pub unit: String,
    pub target: f64,
    pub weight: f64,
    pub timestamp: Instant,
}

impl QualityMetric {
    pub fn new(name: String, value: f64, unit: String, target: f64, weight: f64) -> Self {
        QualityMetric {
            name,
            value,
            unit,
            target,
            weight,
            timestamp: Instant::now(),
        }
    }
    
    pub fn score(&self) -> f64 {
        if self.value <= self.target {
            1.0
        } else {
            self.target / self.value
        }
    }
    
    pub fn normalized_score(&self) -> f64 {
        (self.score() * self.weight).min(1.0)
    }
}

/// 软件系统特征
pub trait SoftwareSystem: Debug {
    fn name(&self) -> &str;
    fn version(&self) -> &str;
    fn lines_of_code(&self) -> usize;
    fn complexity(&self) -> f64;
    fn defect_count(&self) -> usize;
    fn response_time(&self) -> Duration;
    fn availability(&self) -> f64;
}

/// 质量评估器
#[derive(Debug)]
pub struct QualityEvaluator {
    name: String,
    attributes: Vec<Box<dyn QualityAttribute>>,
    evaluation_history: Vec<QualityEvaluation>,
}

/// 质量评估结果
#[derive(Debug, Clone)]
pub struct QualityEvaluation {
    pub system_name: String,
    pub timestamp: Instant,
    pub metrics: Vec<QualityMetric>,
    pub overall_score: f64,
    pub category_scores: HashMap<QualityCategory, f64>,
}

impl QualityEvaluator {
    pub fn new(name: String) -> Self {
        QualityEvaluator {
            name,
            attributes: Vec::new(),
            evaluation_history: Vec::new(),
        }
    }
    
    pub fn add_attribute(&mut self, attribute: Box<dyn QualityAttribute>) {
        self.attributes.push(attribute);
    }
    
    pub fn evaluate(&mut self, system: &dyn SoftwareSystem) -> QualityEvaluation {
        let mut metrics = Vec::new();
        let mut category_scores: HashMap<QualityCategory, f64> = HashMap::new();
        
        // 评估每个质量属性
        for attribute in &self.attributes {
            let metric = attribute.measure(system);
            metrics.push(metric.clone());
            
            // 计算类别分数
            let category = attribute.category();
            let score = metric.normalized_score();
            let current_score = category_scores.get(&category).unwrap_or(&0.0);
            category_scores.insert(category, current_score + score);
        }
        
        // 计算总体分数
        let total_weight: f64 = self.attributes.iter().map(|a| a.weight()).sum();
        let overall_score = if total_weight > 0.0 {
            metrics.iter().map(|m| m.normalized_score()).sum::<f64>() / total_weight
        } else {
            0.0
        };
        
        let evaluation = QualityEvaluation {
            system_name: system.name().to_string(),
            timestamp: Instant::now(),
            metrics,
            overall_score,
            category_scores,
        };
        
        self.evaluation_history.push(evaluation.clone());
        evaluation
    }
    
    pub fn get_history(&self) -> &[QualityEvaluation] {
        &self.evaluation_history
    }
    
    pub fn print_evaluation(&self, evaluation: &QualityEvaluation) {
        println!("=== Quality Evaluation: {} ===", self.name);
        println!("System: {} v{}", evaluation.system_name, "1.0");
        println!("Timestamp: {:?}", evaluation.timestamp);
        println!("Overall Score: {:.2}", evaluation.overall_score);
        println!();
        
        println!("--- Metrics ---");
        for metric in &evaluation.metrics {
            let score = metric.normalized_score();
            let status = if score >= 0.8 { "✅" } else if score >= 0.6 { "⚠️" } else { "❌" };
            println!("{} {}: {:.2} {} (Target: {:.2}, Score: {:.2})", 
                status, metric.name, metric.value, metric.unit, metric.target, score);
        }
        
        println!("\n--- Category Scores ---");
        for (category, score) in &evaluation.category_scores {
            let status = if *score >= 0.8 { "✅" } else if *score >= 0.6 { "⚠️" } else { "❌" };
            println!("{} {:?}: {:.2}", status, category, score);
        }
    }
}

/// 质量报告生成器
#[derive(Debug)]
pub struct QualityReportGenerator;

impl QualityReportGenerator {
    pub fn generate_report(evaluations: &[QualityEvaluation]) -> QualityReport {
        let mut report = QualityReport {
            total_evaluations: evaluations.len(),
            average_score: 0.0,
            trend_analysis: Vec::new(),
            recommendations: Vec::new(),
        };
        
        if !evaluations.is_empty() {
            // 计算平均分数
            let total_score: f64 = evaluations.iter().map(|e| e.overall_score).sum();
            report.average_score = total_score / evaluations.len() as f64;
            
            // 趋势分析
            for i in 1..evaluations.len() {
                let current = evaluations[i].overall_score;
                let previous = evaluations[i-1].overall_score;
                let change = current - previous;
                
                report.trend_analysis.push(TrendPoint {
                    evaluation_index: i,
                    score_change: change,
                    trend: if change > 0.0 { Trend::Improving } else if change < 0.0 { Trend::Declining } else { Trend::Stable },
                });
            }
            
            // 生成建议
            if let Some(latest) = evaluations.last() {
                report.recommendations = Self::generate_recommendations(latest);
            }
        }
        
        report
    }
    
    fn generate_recommendations(evaluation: &QualityEvaluation) -> Vec<String> {
        let mut recommendations = Vec::new();
        
        // 基于类别分数生成建议
        for (category, score) in &evaluation.category_scores {
            if *score < 0.6 {
                recommendations.push(format!("Improve {:?} quality (current score: {:.2})", category, score));
            }
        }
        
        // 基于总体分数生成建议
        if evaluation.overall_score < 0.7 {
            recommendations.push("Overall quality needs improvement".to_string());
        }
        
        recommendations
    }
}

/// 质量报告
#[derive(Debug)]
pub struct QualityReport {
    pub total_evaluations: usize,
    pub average_score: f64,
    pub trend_analysis: Vec<TrendPoint>,
    pub recommendations: Vec<String>,
}

/// 趋势点
#[derive(Debug)]
pub struct TrendPoint {
    pub evaluation_index: usize,
    pub score_change: f64,
    pub trend: Trend,
}

/// 趋势
#[derive(Debug)]
pub enum Trend {
    Improving,
    Declining,
    Stable,
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_quality_evaluator_creation() {
        let evaluator = QualityEvaluator::new("TestEvaluator".to_string());
        assert_eq!(evaluator.name, "TestEvaluator");
    }
}
```

### 5.2 具体质量属性实现

```rust
use std::fmt::Debug;
use std::time::Duration;

/// 代码覆盖率质量属性
#[derive(Debug)]
pub struct CodeCoverageAttribute {
    name: String,
    weight: f64,
    target_coverage: f64,
}

impl CodeCoverageAttribute {
    pub fn new(target_coverage: f64) -> Self {
        CodeCoverageAttribute {
            name: "Code Coverage".to_string(),
            weight: 0.15,
            target_coverage,
        }
    }
}

impl QualityAttribute for CodeCoverageAttribute {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn category(&self) -> QualityCategory {
        QualityCategory::Maintainability
    }
    
    fn measure(&self, system: &dyn SoftwareSystem) -> QualityMetric {
        // 模拟代码覆盖率计算
        let coverage = 0.85; // 假设85%覆盖率
        QualityMetric::new(
            self.name.clone(),
            coverage,
            "%".to_string(),
            self.target_coverage,
            self.weight,
        )
    }
    
    fn weight(&self) -> f64 {
        self.weight
    }
}

/// 圈复杂度质量属性
#[derive(Debug)]
pub struct CyclomaticComplexityAttribute {
    name: String,
    weight: f64,
    target_complexity: f64,
}

impl CyclomaticComplexityAttribute {
    pub fn new(target_complexity: f64) -> Self {
        CyclomaticComplexityAttribute {
            name: "Cyclomatic Complexity".to_string(),
            weight: 0.12,
            target_complexity,
        }
    }
}

impl QualityAttribute for CyclomaticComplexityAttribute {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn category(&self) -> QualityCategory {
        QualityCategory::Maintainability
    }
    
    fn measure(&self, system: &dyn SoftwareSystem) -> QualityMetric {
        let complexity = system.complexity();
        QualityMetric::new(
            self.name.clone(),
            complexity,
            "".to_string(),
            self.target_complexity,
            self.weight,
        )
    }
    
    fn weight(&self) -> f64 {
        self.weight
    }
}

/// 缺陷密度质量属性
#[derive(Debug)]
pub struct DefectDensityAttribute {
    name: String,
    weight: f64,
    target_density: f64,
}

impl DefectDensityAttribute {
    pub fn new(target_density: f64) -> Self {
        DefectDensityAttribute {
            name: "Defect Density".to_string(),
            weight: 0.20,
            target_density,
        }
    }
}

impl QualityAttribute for DefectDensityAttribute {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn category(&self) -> QualityCategory {
        QualityCategory::Reliability
    }
    
    fn measure(&self, system: &dyn SoftwareSystem) -> QualityMetric {
        let defects = system.defect_count();
        let loc = system.lines_of_code();
        let density = if loc > 0 { defects as f64 / loc as f64 } else { 0.0 };
        
        QualityMetric::new(
            self.name.clone(),
            density,
            "defects/KLOC".to_string(),
            self.target_density,
            self.weight,
        )
    }
    
    fn weight(&self) -> f64 {
        self.weight
    }
}

/// 响应时间质量属性
#[derive(Debug)]
pub struct ResponseTimeAttribute {
    name: String,
    weight: f64,
    target_response_time: Duration,
}

impl ResponseTimeAttribute {
    pub fn new(target_response_time: Duration) -> Self {
        ResponseTimeAttribute {
            name: "Response Time".to_string(),
            weight: 0.18,
            target_response_time,
        }
    }
}

impl QualityAttribute for ResponseTimeAttribute {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn category(&self) -> QualityCategory {
        QualityCategory::Efficiency
    }
    
    fn measure(&self, system: &dyn SoftwareSystem) -> QualityMetric {
        let response_time = system.response_time();
        let time_ms = response_time.as_millis() as f64;
        let target_ms = self.target_response_time.as_millis() as f64;
        
        QualityMetric::new(
            self.name.clone(),
            time_ms,
            "ms".to_string(),
            target_ms,
            self.weight,
        )
    }
    
    fn weight(&self) -> f64 {
        self.weight
    }
}

/// 可用性质量属性
#[derive(Debug)]
pub struct AvailabilityAttribute {
    name: String,
    weight: f64,
    target_availability: f64,
}

impl AvailabilityAttribute {
    pub fn new(target_availability: f64) -> Self {
        AvailabilityAttribute {
            name: "Availability".to_string(),
            weight: 0.25,
            target_availability,
        }
    }
}

impl QualityAttribute for AvailabilityAttribute {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn category(&self) -> QualityCategory {
        QualityCategory::Reliability
    }
    
    fn measure(&self, system: &dyn SoftwareSystem) -> QualityMetric {
        let availability = system.availability();
        QualityMetric::new(
            self.name.clone(),
            availability,
            "%".to_string(),
            self.target_availability,
            self.weight,
        )
    }
    
    fn weight(&self) -> f64 {
        self.weight
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_code_coverage_attribute() {
        let attribute = CodeCoverageAttribute::new(0.80);
        assert_eq!(attribute.name(), "Code Coverage");
        assert_eq!(attribute.weight(), 0.15);
    }
    
    #[test]
    fn test_defect_density_attribute() {
        let attribute = DefectDensityAttribute::new(1.0);
        assert_eq!(attribute.name(), "Defect Density");
        assert_eq!(attribute.weight(), 0.20);
    }
}
```

### 5.3 示例系统实现

```rust
use std::fmt::Debug;
use std::time::Duration;

/// 示例Web应用系统
#[derive(Debug)]
pub struct WebApplicationSystem {
    name: String,
    version: String,
    lines_of_code: usize,
    complexity: f64,
    defect_count: usize,
    response_time: Duration,
    availability: f64,
}

impl WebApplicationSystem {
    pub fn new() -> Self {
        WebApplicationSystem {
            name: "WebApp".to_string(),
            version: "1.0.0".to_string(),
            lines_of_code: 50000,
            complexity: 8.5,
            defect_count: 15,
            response_time: Duration::from_millis(150),
            availability: 99.5,
        }
    }
    
    pub fn with_improvements(mut self) -> Self {
        self.complexity = 6.2;
        self.defect_count = 8;
        self.response_time = Duration::from_millis(120);
        self.availability = 99.8;
        self
    }
    
    pub fn with_degradation(mut self) -> Self {
        self.complexity = 12.0;
        self.defect_count = 25;
        self.response_time = Duration::from_millis(300);
        self.availability = 98.5;
        self
    }
}

impl SoftwareSystem for WebApplicationSystem {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn version(&self) -> &str {
        &self.version
    }
    
    fn lines_of_code(&self) -> usize {
        self.lines_of_code
    }
    
    fn complexity(&self) -> f64 {
        self.complexity
    }
    
    fn defect_count(&self) -> usize {
        self.defect_count
    }
    
    fn response_time(&self) -> Duration {
        self.response_time
    }
    
    fn availability(&self) -> f64 {
        self.availability
    }
}

/// 质量评估示例
pub struct QualityAssessmentExample;

impl QualityAssessmentExample {
    pub fn run_comprehensive_assessment() {
        println!("=== Software Quality Assessment Example ===\n");
        
        // 创建质量评估器
        let mut evaluator = QualityEvaluator::new("Comprehensive Quality Evaluator".to_string());
        
        // 添加质量属性
        evaluator.add_attribute(Box::new(CodeCoverageAttribute::new(0.80)));
        evaluator.add_attribute(Box::new(CyclomaticComplexityAttribute::new(10.0)));
        evaluator.add_attribute(Box::new(DefectDensityAttribute::new(1.0)));
        evaluator.add_attribute(Box::new(ResponseTimeAttribute::new(Duration::from_millis(200))));
        evaluator.add_attribute(Box::new(AvailabilityAttribute::new(99.0)));
        
        // 评估不同版本的系统
        let systems = vec![
            ("Baseline", WebApplicationSystem::new()),
            ("Improved", WebApplicationSystem::new().with_improvements()),
            ("Degraded", WebApplicationSystem::new().with_degradation()),
        ];
        
        for (version_name, system) in systems {
            println!("--- Evaluating {} Version ---", version_name);
            let evaluation = evaluator.evaluate(&system);
            evaluator.print_evaluation(&evaluation);
            println!();
        }
        
        // 生成趋势报告
        let history = evaluator.get_history();
        let report = QualityReportGenerator::generate_report(history);
        
        println!("=== Quality Trend Report ===");
        println!("Total Evaluations: {}", report.total_evaluations);
        println!("Average Score: {:.2}", report.average_score);
        
        println!("\n--- Trend Analysis ---");
        for trend in &report.trend_analysis {
            let trend_symbol = match trend.trend {
                Trend::Improving => "📈",
                Trend::Declining => "📉",
                Trend::Stable => "➡️",
            };
            println!("{} Evaluation {}: {:.3} change", 
                trend_symbol, trend.evaluation_index, trend.score_change);
        }
        
        println!("\n--- Recommendations ---");
        for recommendation in &report.recommendations {
            println!("• {}", recommendation);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_web_application_system() {
        let system = WebApplicationSystem::new();
        assert_eq!(system.name(), "WebApp");
        assert_eq!(system.lines_of_code(), 50000);
        assert_eq!(system.defect_count(), 15);
    }
    
    #[test]
    fn test_quality_assessment() {
        // 这个测试会运行完整的质量评估示例
        QualityAssessmentExample::run_comprehensive_assessment();
    }
}
```

## 6. 应用示例

### 6.1 质量监控系统

```rust
use std::fmt::Debug;
use std::time::{Duration, Instant};
use std::collections::HashMap;

/// 质量监控器
#[derive(Debug)]
pub struct QualityMonitor {
    name: String,
    evaluator: QualityEvaluator,
    monitoring_interval: Duration,
    alert_threshold: f64,
    quality_history: Vec<QualitySnapshot>,
}

/// 质量快照
#[derive(Debug, Clone)]
pub struct QualitySnapshot {
    pub timestamp: Instant,
    pub overall_score: f64,
    pub critical_issues: Vec<String>,
    pub trend: Trend,
}

impl QualityMonitor {
    pub fn new(name: String, monitoring_interval: Duration, alert_threshold: f64) -> Self {
        let mut evaluator = QualityEvaluator::new(format!("{}_Evaluator", name));
        
        // 添加标准质量属性
        evaluator.add_attribute(Box::new(CodeCoverageAttribute::new(0.80)));
        evaluator.add_attribute(Box::new(CyclomaticComplexityAttribute::new(10.0)));
        evaluator.add_attribute(Box::new(DefectDensityAttribute::new(1.0)));
        evaluator.add_attribute(Box::new(ResponseTimeAttribute::new(Duration::from_millis(200))));
        evaluator.add_attribute(Box::new(AvailabilityAttribute::new(99.0)));
        
        QualityMonitor {
            name,
            evaluator,
            monitoring_interval,
            alert_threshold,
            quality_history: Vec::new(),
        }
    }
    
    pub fn monitor_system(&mut self, system: &dyn SoftwareSystem) -> QualityAlert {
        let evaluation = self.evaluator.evaluate(system);
        
        // 创建质量快照
        let trend = if self.quality_history.len() >= 2 {
            let current = evaluation.overall_score;
            let previous = self.quality_history.last().unwrap().overall_score;
            if current > previous { Trend::Improving }
            else if current < previous { Trend::Declining }
            else { Trend::Stable }
        } else {
            Trend::Stable
        };
        
        let critical_issues = self.identify_critical_issues(&evaluation);
        
        let snapshot = QualitySnapshot {
            timestamp: Instant::now(),
            overall_score: evaluation.overall_score,
            critical_issues: critical_issues.clone(),
            trend,
        };
        
        self.quality_history.push(snapshot);
        
        // 检查是否需要报警
        if evaluation.overall_score < self.alert_threshold {
            QualityAlert::Critical {
                score: evaluation.overall_score,
                threshold: self.alert_threshold,
                issues: critical_issues,
            }
        } else if evaluation.overall_score < self.alert_threshold + 0.1 {
            QualityAlert::Warning {
                score: evaluation.overall_score,
                threshold: self.alert_threshold,
                issues: critical_issues,
            }
        } else {
            QualityAlert::Normal {
                score: evaluation.overall_score,
            }
        }
    }
    
    fn identify_critical_issues(&self, evaluation: &QualityEvaluation) -> Vec<String> {
        let mut issues = Vec::new();
        
        for metric in &evaluation.metrics {
            if metric.normalized_score() < 0.5 {
                issues.push(format!("Critical: {} is {:.2} (target: {:.2})", 
                    metric.name, metric.value, metric.target));
            }
        }
        
        issues
    }
    
    pub fn get_quality_trend(&self) -> QualityTrend {
        if self.quality_history.len() < 2 {
            return QualityTrend::InsufficientData;
        }
        
        let recent_scores: Vec<f64> = self.quality_history
            .iter()
            .map(|s| s.overall_score)
            .collect();
        
        let trend = self.calculate_trend(&recent_scores);
        
        QualityTrend::Trend {
            direction: trend,
            average_score: recent_scores.iter().sum::<f64>() / recent_scores.len() as f64,
            volatility: self.calculate_volatility(&recent_scores),
        }
    }
    
    fn calculate_trend(&self, scores: &[f64]) -> TrendDirection {
        if scores.len() < 2 {
            return TrendDirection::Stable;
        }
        
        let first_half: f64 = scores.iter().take(scores.len() / 2).sum();
        let second_half: f64 = scores.iter().skip(scores.len() / 2).sum();
        
        let first_avg = first_half / (scores.len() / 2) as f64;
        let second_avg = second_half / (scores.len() - scores.len() / 2) as f64;
        
        if second_avg > first_avg + 0.05 {
            TrendDirection::Improving
        } else if second_avg < first_avg - 0.05 {
            TrendDirection::Declining
        } else {
            TrendDirection::Stable
        }
    }
    
    fn calculate_volatility(&self, scores: &[f64]) -> f64 {
        if scores.len() < 2 {
            return 0.0;
        }
        
        let mean = scores.iter().sum::<f64>() / scores.len() as f64;
        let variance = scores.iter()
            .map(|s| (s - mean).powi(2))
            .sum::<f64>() / scores.len() as f64;
        
        variance.sqrt()
    }
}

/// 质量报警
#[derive(Debug)]
pub enum QualityAlert {
    Normal { score: f64 },
    Warning { score: f64, threshold: f64, issues: Vec<String> },
    Critical { score: f64, threshold: f64, issues: Vec<String> },
}

/// 质量趋势
#[derive(Debug)]
pub enum QualityTrend {
    InsufficientData,
    Trend { direction: TrendDirection, average_score: f64, volatility: f64 },
}

/// 趋势方向
#[derive(Debug)]
pub enum TrendDirection {
    Improving,
    Declining,
    Stable,
}

/// 质量监控示例
pub struct QualityMonitoringExample;

impl QualityMonitoringExample {
    pub fn run_monitoring_simulation() {
        println!("=== Quality Monitoring Simulation ===\n");
        
        let mut monitor = QualityMonitor::new(
            "Production System Monitor".to_string(),
            Duration::from_secs(3600), // 1小时监控间隔
            0.7, // 70%质量阈值
        );
        
        // 模拟不同质量水平的系统
        let systems = vec![
            ("High Quality", WebApplicationSystem::new().with_improvements()),
            ("Medium Quality", WebApplicationSystem::new()),
            ("Low Quality", WebApplicationSystem::new().with_degradation()),
            ("Recovered Quality", WebApplicationSystem::new().with_improvements()),
        ];
        
        for (system_name, system) in systems {
            println!("--- Monitoring {} ---", system_name);
            
            let alert = monitor.monitor_system(&system);
            
            match alert {
                QualityAlert::Normal { score } => {
                    println!("✅ Normal: Quality score is {:.2}", score);
                }
                QualityAlert::Warning { score, threshold, issues } => {
                    println!("⚠️ Warning: Quality score {:.2} is below threshold {:.2}", score, threshold);
                    for issue in &issues {
                        println!("   - {}", issue);
                    }
                }
                QualityAlert::Critical { score, threshold, issues } => {
                    println!("🚨 Critical: Quality score {:.2} is critically below threshold {:.2}", score, threshold);
                    for issue in &issues {
                        println!("   - {}", issue);
                    }
                }
            }
            println!();
        }
        
        // 分析质量趋势
        let trend = monitor.get_quality_trend();
        println!("--- Quality Trend Analysis ---");
        match trend {
            QualityTrend::InsufficientData => {
                println!("📊 Insufficient data for trend analysis");
            }
            QualityTrend::Trend { direction, average_score, volatility } => {
                let direction_symbol = match direction {
                    TrendDirection::Improving => "📈",
                    TrendDirection::Declining => "📉",
                    TrendDirection::Stable => "➡️",
                };
                println!("{} Trend: {:?}", direction_symbol, direction);
                println!("📊 Average Score: {:.2}", average_score);
                println!("📊 Volatility: {:.3}", volatility);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_quality_monitor() {
        let monitor = QualityMonitor::new(
            "Test Monitor".to_string(),
            Duration::from_secs(60),
            0.8,
        );
        assert_eq!(monitor.name, "Test Monitor");
    }
    
    #[test]
    fn test_quality_monitoring_simulation() {
        QualityMonitoringExample::run_monitoring_simulation();
    }
}
```

## 7. 相关理论

### 7.1 测试理论

- [测试理论基础](../04_Testing_Theory/01_Testing_Foundations/01_Testing_Foundations_Theory.md)
- [单元测试理论](../04_Testing_Theory/02_Unit_Testing/01_Unit_Testing_Theory.md)
- [集成测试理论](../04_Testing_Theory/03_Integration_Testing/01_Integration_Testing_Theory.md)
- [系统测试理论](../04_Testing_Theory/04_System_Testing/01_System_Testing_Theory.md)

### 7.2 软件工程理论

- [软件验证理论](../06_Software_Verification/01_Software_Verification_Theory.md)
- [软件维护理论](../07_Software_Maintenance/01_Software_Maintenance_Theory.md)

### 7.3 形式化方法

- [形式化规格说明](../01_Formal_Specification/01_Formal_Specification_Theory.md)
- [形式化验证方法](../02_Formal_Verification/01_Formal_Verification_Theory.md)
- [模型检测理论](../03_Model_Checking/01_Model_Checking_Theory.md)

## 8. 参考文献

1. ISO/IEC 9126-1:2001. Software engineering -- Product quality -- Part 1: Quality model.
2. McCall, J. A., Richards, P. K., & Walters, G. F. (1977). Factors in Software Quality. Rome Air Development Center.
3. Boehm, B. W., Brown, J. R., & Lipow, M. (1976). Quantitative evaluation of software quality. ICSE '76.
4. Fenton, N. E., & Pfleeger, S. L. (1997). Software Metrics: A Rigorous and Practical Approach. PWS Publishing.
5. Kitchenham, B., & Pfleeger, S. L. (1996). Software quality: The elusive target. IEEE Software.

---

**最后更新**: 2024年12月21日  
**维护者**: AI助手  
**版本**: v1.0
