# 17. 数据科学理论 (Data Science Theory)

## 📋 目录

- [1 模块概述](#1-模块概述)
- [2 核心理论](#2-核心理论)
  - [2.1 数据科学基础理论](#21-数据科学基础理论)
  - [2.2 统计学基础理论](#22-统计学基础理论)
  - [2.3 机器学习理论](#23-机器学习理论)
- [3 Rust实现](#3-rust实现)
  - [3.1 数据科学核心实现](#31-数据科学核心实现)
  - [3.2 统计分析实现](#32-统计分析实现)
- [4 应用示例](#4-应用示例)
  - [4.1 示例1：线性回归分析](#41-示例1线性回归分析)
  - [4.2 示例2：聚类分析](#42-示例2聚类分析)
  - [4.3 示例3：关联规则挖掘](#43-示例3关联规则挖掘)
- [5 理论扩展](#5-理论扩展)
  - [5.1 深度学习理论](#51-深度学习理论)
  - [5.2 贝叶斯统计理论](#52-贝叶斯统计理论)
  - [5.3 信息论在数据科学中的应用](#53-信息论在数据科学中的应用)
- [6 批判性分析](#6-批判性分析)
  - [6.1 多元理论视角](#61-多元理论视角)
  - [6.2 局限性分析](#62-局限性分析)
  - [6.3 争议与分歧](#63-争议与分歧)
  - [6.4 应用前景](#64-应用前景)
  - [6.5 改进建议](#65-改进建议)

---

## 1 模块概述

数据科学理论是研究数据收集、处理、分析和应用的综合性理论体系。本模块涵盖统计学基础、数据挖掘、机器学习、数据可视化等核心概念，为从数据中提取知识和洞察提供理论基础。

## 🏗️ 目录结构

```text
17_Data_Science_Theory/
├── README.md                           # 模块总览
├── 01_Data_Foundation_Theory.md        # 数据基础理论
├── 18.1_Data_Science_Formal_Proofs.md # 数据科学形式化证明
├── 01_Statistical_Analysis/            # 统计分析
│   ├── 01.1_Probability_Theory.md     # 概率论
│   ├── 01.2_Statistical_Inference.md  # 统计推断
│   └── 01.3_Regression_Analysis.md    # 回归分析
└── 02_Data_Mining/                    # 数据挖掘
    ├── 02.1_Pattern_Discovery.md      # 模式发现
    ├── 02.2_Association_Rules.md      # 关联规则
    └── 02.3_Clustering_Analysis.md    # 聚类分析
```

## 2 核心理论

### 2.1 数据科学基础理论

**定义 1.1** (数据)
数据是信息的载体，表示为有序的符号序列 $D = (s_1, s_2, \ldots, s_n)$，其中 $s_i \in \Sigma$ 为符号集。

**定义 1.2** (数据类型)
给定数据类型集合 $\mathcal{T}$，数据类型函数 $type: D \rightarrow \mathcal{T}$ 将数据映射到其类型。

**定理 1.1** (数据类型完备性)
对于任意数据 $D$，存在唯一的数据类型 $t \in \mathcal{T}$ 使得 $type(D) = t$。

### 2.2 统计学基础理论

**定义 2.1** (概率分布)
概率分布是随机变量的取值概率函数：$P(X = x_i) = p_i$

**定义 2.2** (期望值)
随机变量 $X$ 的期望值：$E[X] = \sum_{i} x_i p_i$

**定理 2.1** (大数定律)
当样本量 $n \rightarrow \infty$ 时，样本均值收敛于总体均值。

### 2.3 机器学习理论

**定义 3.1** (学习问题)
学习问题是寻找函数 $f: \mathcal{X} \rightarrow \mathcal{Y}$ 使得 $f(x) \approx y$。

**定义 3.2** (泛化误差)
泛化误差是模型在未见数据上的期望误差：$E_{gen} = E_{(x,y)}[L(f(x), y)]$

**定理 3.1** (VC维理论)
对于有限VC维的假设类，存在泛化误差上界。

## 3 Rust实现

### 3.1 数据科学核心实现

```rust
use std::collections::HashMap;
use std::fmt;
use rand::Rng;
use ndarray::{Array1, Array2, Axis};

/// 数据类型枚举
#[derive(Debug, Clone, PartialEq)]
pub enum DataType {
    Numeric(f64),
    Categorical(String),
    Textual(String),
    Temporal(chrono::DateTime<chrono::Utc>),
    Spatial((f64, f64)), // (latitude, longitude)
}

/// 数据集结构
#[derive(Debug)]
pub struct Dataset {
    pub features: Vec<String>,
    pub data: Vec<Vec<DataType>>,
    pub target: Option<Vec<DataType>>,
}

impl Dataset {
    pub fn new(features: Vec<String>) -> Self {
        Dataset {
            features,
            data: Vec::new(),
            target: None,
        }
    }
    
    /// 添加数据行
    pub fn add_row(&mut self, row: Vec<DataType>) -> Result<(), String> {
        if row.len() != self.features.len() {
            return Err("Row length doesn't match features".to_string());
        }
        self.data.push(row);
        Ok(())
    }
    
    /// 获取数值列
    pub fn get_numeric_column(&self, column_index: usize) -> Result<Vec<f64>, String> {
        if column_index >= self.features.len() {
            return Err("Invalid column index".to_string());
        }
        
        let mut numeric_data = Vec::new();
        for row in &self.data {
            if let DataType::Numeric(value) = row[column_index] {
                numeric_data.push(value);
            } else {
                return Err("Column is not numeric".to_string());
            }
        }
        Ok(numeric_data)
    }
    
    /// 计算描述性统计
    pub fn descriptive_statistics(&self, column_index: usize) -> Result<Statistics, String> {
        let numeric_data = self.get_numeric_column(column_index)?;
        
        let n = numeric_data.len() as f64;
        let sum: f64 = numeric_data.iter().sum();
        let mean = sum / n;
        
        let variance = numeric_data.iter()
            .map(|x| (x - mean).powi(2))
            .sum::<f64>() / (n - 1.0);
        let std_dev = variance.sqrt();
        
        let sorted_data = {
            let mut sorted = numeric_data.clone();
            sorted.sort_by(|a, b| a.partial_cmp(b).unwrap());
            sorted
        };
        
        let median = if n as usize % 2 == 0 {
            (sorted_data[n as usize / 2 - 1] + sorted_data[n as usize / 2]) / 2.0
        } else {
            sorted_data[n as usize / 2]
        };
        
        let min = sorted_data[0];
        let max = sorted_data[sorted_data.len() - 1];
        
        Ok(Statistics {
            count: n as usize,
            mean,
            median,
            std_dev,
            min,
            max,
            variance,
        })
    }
}

#[derive(Debug)]
pub struct Statistics {
    pub count: usize,
    pub mean: f64,
    pub median: f64,
    pub std_dev: f64,
    pub min: f64,
    pub max: f64,
    pub variance: f64,
}

/// 概率分布实现
#[derive(Debug)]
pub struct ProbabilityDistribution {
    pub values: Vec<f64>,
    pub probabilities: Vec<f64>,
}

impl ProbabilityDistribution {
    pub fn new(values: Vec<f64>, probabilities: Vec<f64>) -> Result<Self, String> {
        if values.len() != probabilities.len() {
            return Err("Values and probabilities must have same length".to_string());
        }
        
        let sum: f64 = probabilities.iter().sum();
        if (sum - 1.0).abs() > 1e-10 {
            return Err("Probabilities must sum to 1".to_string());
        }
        
        Ok(ProbabilityDistribution {
            values,
            probabilities,
        })
    }
    
    /// 计算期望值
    pub fn expected_value(&self) -> f64 {
        self.values.iter()
            .zip(self.probabilities.iter())
            .map(|(x, p)| x * p)
            .sum()
    }
    
    /// 计算方差
    pub fn variance(&self) -> f64 {
        let mean = self.expected_value();
        self.values.iter()
            .zip(self.probabilities.iter())
            .map(|(x, p)| p * (x - mean).powi(2))
            .sum()
    }
    
    /// 生成随机样本
    pub fn sample(&self, n: usize) -> Vec<f64> {
        let mut rng = rand::thread_rng();
        let mut samples = Vec::new();
        
        for _ in 0..n {
            let u = rng.gen::<f64>();
            let mut cumulative = 0.0;
            
            for (value, prob) in self.values.iter().zip(self.probabilities.iter()) {
                cumulative += prob;
                if u <= cumulative {
                    samples.push(*value);
                    break;
                }
            }
        }
        
        samples
    }
}

/// 线性回归模型
#[derive(Debug)]
pub struct LinearRegression {
    pub coefficients: Vec<f64>,
    pub intercept: f64,
}

impl LinearRegression {
    pub fn new() -> Self {
        LinearRegression {
            coefficients: Vec::new(),
            intercept: 0.0,
        }
    }
    
    /// 训练模型
    pub fn fit(&mut self, X: &Array2<f64>, y: &Array1<f64>) -> Result<(), String> {
        // 简化的线性回归实现（使用最小二乘法）
        let n_samples = X.shape()[0];
        let n_features = X.shape()[1];
        
        // 添加偏置项
        let mut X_with_bias = Array2::zeros((n_samples, n_features + 1));
        for i in 0..n_samples {
            X_with_bias[[i, 0]] = 1.0; // 偏置项
            for j in 0..n_features {
                X_with_bias[[i, j + 1]] = X[[i, j]];
            }
        }
        
        // 计算最小二乘解：β = (X^T X)^(-1) X^T y
        let X_t = X_with_bias.t();
        let X_t_X = X_t.dot(&X_with_bias);
        let X_t_y = X_t.dot(y);
        
        // 简化的矩阵求逆（实际应用中应使用更稳定的方法）
        if let Ok(inv_X_t_X) = self.inverse_2x2(&X_t_X) {
            let beta = inv_X_t_X.dot(&X_t_y);
            
            self.intercept = beta[0];
            self.coefficients = beta.slice(ndarray::s![1..]).to_vec();
            
            Ok(())
        } else {
            Err("Matrix is not invertible".to_string())
        }
    }
    
    /// 预测
    pub fn predict(&self, X: &Array2<f64>) -> Array1<f64> {
        let n_samples = X.shape()[0];
        let mut predictions = Array1::zeros(n_samples);
        
        for i in 0..n_samples {
            let mut pred = self.intercept;
            for j in 0..self.coefficients.len() {
                pred += self.coefficients[j] * X[[i, j]];
            }
            predictions[i] = pred;
        }
        
        predictions
    }
    
    /// 计算R²分数
    pub fn score(&self, X: &Array2<f64>, y: &Array1<f64>) -> f64 {
        let predictions = self.predict(X);
        let y_mean = y.mean().unwrap();
        
        let ss_res: f64 = y.iter()
            .zip(predictions.iter())
            .map(|(y_true, y_pred)| (y_true - y_pred).powi(2))
            .sum();
        
        let ss_tot: f64 = y.iter()
            .map(|y_true| (y_true - y_mean).powi(2))
            .sum();
        
        1.0 - (ss_res / ss_tot)
    }
    
    /// 简化的2x2矩阵求逆
    fn inverse_2x2(&self, matrix: &Array2<f64>) -> Result<Array2<f64>, String> {
        if matrix.shape() != [2, 2] {
            return Err("Matrix must be 2x2".to_string());
        }
        
        let det = matrix[[0, 0]] * matrix[[1, 1]] - matrix[[0, 1]] * matrix[[1, 0]];
        if det.abs() < 1e-10 {
            return Err("Matrix is singular".to_string());
        }
        
        let inv_det = 1.0 / det;
        let mut inverse = Array2::zeros((2, 2));
        
        inverse[[0, 0]] = matrix[[1, 1]] * inv_det;
        inverse[[0, 1]] = -matrix[[0, 1]] * inv_det;
        inverse[[1, 0]] = -matrix[[1, 0]] * inv_det;
        inverse[[1, 1]] = matrix[[0, 0]] * inv_det;
        
        Ok(inverse)
    }
}

/// 聚类算法实现
#[derive(Debug)]
pub struct KMeans {
    pub k: usize,
    pub centroids: Vec<Vec<f64>>,
    pub labels: Vec<usize>,
}

impl KMeans {
    pub fn new(k: usize) -> Self {
        KMeans {
            k,
            centroids: Vec::new(),
            labels: Vec::new(),
        }
    }
    
    /// 训练聚类模型
    pub fn fit(&mut self, X: &Array2<f64>) -> Result<(), String> {
        let n_samples = X.shape()[0];
        let n_features = X.shape()[1];
        
        // 初始化质心
        self.centroids = self.initialize_centroids(X);
        self.labels = vec![0; n_samples];
        
        let max_iterations = 100;
        let mut converged = false;
        let mut iteration = 0;
        
        while !converged && iteration < max_iterations {
            let old_labels = self.labels.clone();
            
            // 分配样本到最近的质心
            for i in 0..n_samples {
                let mut min_distance = f64::INFINITY;
                let mut best_cluster = 0;
                
                for j in 0..self.k {
                    let distance = self.euclidean_distance(
                        &X.row(i).to_vec(),
                        &self.centroids[j]
                    );
                    
                    if distance < min_distance {
                        min_distance = distance;
                        best_cluster = j;
                    }
                }
                
                self.labels[i] = best_cluster;
            }
            
            // 更新质心
            for j in 0..self.k {
                let cluster_points: Vec<Vec<f64>> = self.labels.iter()
                    .enumerate()
                    .filter(|(_, &label)| label == j)
                    .map(|(i, _)| X.row(i).to_vec())
                    .collect();
                
                if !cluster_points.is_empty() {
                    let mut new_centroid = vec![0.0; n_features];
                    for point in &cluster_points {
                        for (k, &value) in point.iter().enumerate() {
                            new_centroid[k] += value;
                        }
                    }
                    
                    let cluster_size = cluster_points.len() as f64;
                    for value in &mut new_centroid {
                        *value /= cluster_size;
                    }
                    
                    self.centroids[j] = new_centroid;
                }
            }
            
            // 检查收敛
            converged = self.labels == old_labels;
            iteration += 1;
        }
        
        Ok(())
    }
    
    /// 预测聚类标签
    pub fn predict(&self, X: &Array2<f64>) -> Vec<usize> {
        let n_samples = X.shape()[0];
        let mut labels = Vec::new();
        
        for i in 0..n_samples {
            let mut min_distance = f64::INFINITY;
            let mut best_cluster = 0;
            
            for j in 0..self.k {
                let distance = self.euclidean_distance(
                    &X.row(i).to_vec(),
                    &self.centroids[j]
                );
                
                if distance < min_distance {
                    min_distance = distance;
                    best_cluster = j;
                }
            }
            
            labels.push(best_cluster);
        }
        
        labels
    }
    
    /// 初始化质心
    fn initialize_centroids(&self, X: &Array2<f64>) -> Vec<Vec<f64>> {
        let n_features = X.shape()[1];
        let mut rng = rand::thread_rng();
        let mut centroids = Vec::new();
        
        for _ in 0..self.k {
            let mut centroid = Vec::new();
            for j in 0..n_features {
                let min_val = X.column(j).min().unwrap();
                let max_val = X.column(j).max().unwrap();
                let random_val = rng.gen_range(min_val..max_val);
                centroid.push(random_val);
            }
            centroids.push(centroid);
        }
        
        centroids
    }
    
    /// 计算欧几里得距离
    fn euclidean_distance(&self, a: &[f64], b: &[f64]) -> f64 {
        a.iter()
            .zip(b.iter())
            .map(|(x, y)| (x - y).powi(2))
            .sum::<f64>()
            .sqrt()
    }
}

/// 关联规则挖掘
#[derive(Debug)]
pub struct AssociationRuleMining {
    pub min_support: f64,
    pub min_confidence: f64,
}

#[derive(Debug, Clone)]
pub struct AssociationRule {
    pub antecedent: Vec<String>,
    pub consequent: Vec<String>,
    pub support: f64,
    pub confidence: f64,
    pub lift: f64,
}

impl AssociationRuleMining {
    pub fn new(min_support: f64, min_confidence: f64) -> Self {
        AssociationRuleMining {
            min_support,
            min_confidence,
        }
    }
    
    /// 挖掘关联规则
    pub fn mine_rules(&self, transactions: &[Vec<String>]) -> Vec<AssociationRule> {
        let mut rules = Vec::new();
        let total_transactions = transactions.len() as f64;
        
        // 计算频繁项集
        let frequent_itemsets = self.find_frequent_itemsets(transactions);
        
        // 生成关联规则
        for itemset in &frequent_itemsets {
            if itemset.len() < 2 {
                continue;
            }
            
            for i in 1..(1 << itemset.len()) {
                let antecedent: Vec<String> = itemset.iter()
                    .enumerate()
                    .filter(|(j, _)| (i >> j) & 1 == 1)
                    .map(|(_, item)| item.clone())
                    .collect();
                
                let consequent: Vec<String> = itemset.iter()
                    .enumerate()
                    .filter(|(j, _)| (i >> j) & 1 == 0)
                    .map(|(_, item)| item.clone())
                    .collect();
                
                if !antecedent.is_empty() && !consequent.is_empty() {
                    let support = self.calculate_support(itemset, transactions);
                    let confidence = self.calculate_confidence(&antecedent, itemset, transactions);
                    
                    if support >= self.min_support && confidence >= self.min_confidence {
                        let lift = confidence / self.calculate_support(&consequent, transactions);
                        
                        rules.push(AssociationRule {
                            antecedent,
                            consequent,
                            support,
                            confidence,
                            lift,
                        });
                    }
                }
            }
        }
        
        rules
    }
    
    /// 查找频繁项集
    fn find_frequent_itemsets(&self, transactions: &[Vec<String>]) -> Vec<Vec<String>> {
        let mut frequent_itemsets = Vec::new();
        let total_transactions = transactions.len() as f64;
        
        // 获取所有唯一项
        let mut all_items = std::collections::HashSet::new();
        for transaction in transactions {
            for item in transaction {
                all_items.insert(item.clone());
            }
        }
        
        // 生成1项集
        let mut current_itemsets: Vec<Vec<String>> = all_items.into_iter()
            .map(|item| vec![item])
            .collect();
        
        while !current_itemsets.is_empty() {
            let mut frequent_current = Vec::new();
            
            for itemset in &current_itemsets {
                let support = self.calculate_support(itemset, transactions);
                if support >= self.min_support {
                    frequent_current.push(itemset.clone());
                    frequent_itemsets.push(itemset.clone());
                }
            }
            
            // 生成下一层项集
            current_itemsets = self.generate_next_level(&frequent_current);
        }
        
        frequent_itemsets
    }
    
    /// 计算支持度
    fn calculate_support(&self, itemset: &[String], transactions: &[Vec<String>]) -> f64 {
        let count = transactions.iter()
            .filter(|transaction| {
                itemset.iter().all(|item| transaction.contains(item))
            })
            .count();
        
        count as f64 / transactions.len() as f64
    }
    
    /// 计算置信度
    fn calculate_confidence(&self, antecedent: &[String], itemset: &[String], transactions: &[Vec<String>]) -> f64 {
        let antecedent_support = self.calculate_support(antecedent, transactions);
        let itemset_support = self.calculate_support(itemset, transactions);
        
        if antecedent_support > 0.0 {
            itemset_support / antecedent_support
        } else {
            0.0
        }
    }
    
    /// 生成下一层项集
    fn generate_next_level(&self, current_itemsets: &[Vec<String>]) -> Vec<Vec<String>> {
        let mut next_level = Vec::new();
        
        for i in 0..current_itemsets.len() {
            for j in (i + 1)..current_itemsets.len() {
                let itemset1 = &current_itemsets[i];
                let itemset2 = &current_itemsets[j];
                
                // 检查是否可以合并
                if itemset1.len() == itemset2.len() {
                    let mut can_merge = true;
                    let mut new_itemset = Vec::new();
                    
                    for k in 0..(itemset1.len() - 1) {
                        if itemset1[k] != itemset2[k] {
                            can_merge = false;
                            break;
                        }
                        new_itemset.push(itemset1[k].clone());
                    }
                    
                    if can_merge {
                        new_itemset.push(itemset1[itemset1.len() - 1].clone());
                        new_itemset.push(itemset2[itemset2.len() - 1].clone());
                        next_level.push(new_itemset);
                    }
                }
            }
        }
        
        next_level
    }
}
```

### 3.2 统计分析实现

```rust
use std::collections::HashMap;

/// 假设检验
#[derive(Debug)]
pub struct HypothesisTest {
    pub alpha: f64,
    pub test_statistic: f64,
    pub p_value: f64,
    pub critical_value: f64,
}

impl HypothesisTest {
    pub fn new(alpha: f64) -> Self {
        HypothesisTest {
            alpha,
            test_statistic: 0.0,
            p_value: 0.0,
            critical_value: 0.0,
        }
    }
    
    /// t检验
    pub fn t_test(&mut self, sample1: &[f64], sample2: &[f64]) -> Result<bool, String> {
        let n1 = sample1.len() as f64;
        let n2 = sample2.len() as f64;
        
        let mean1 = sample1.iter().sum::<f64>() / n1;
        let mean2 = sample2.iter().sum::<f64>() / n2;
        
        let var1 = sample1.iter()
            .map(|x| (x - mean1).powi(2))
            .sum::<f64>() / (n1 - 1.0);
        
        let var2 = sample2.iter()
            .map(|x| (x - mean2).powi(2))
            .sum::<f64>() / (n2 - 1.0);
        
        let pooled_var = ((n1 - 1.0) * var1 + (n2 - 1.0) * var2) / (n1 + n2 - 2.0);
        let se = (pooled_var * (1.0 / n1 + 1.0 / n2)).sqrt();
        
        self.test_statistic = (mean1 - mean2) / se;
        self.critical_value = self.t_critical_value(n1 + n2 - 2.0);
        
        // 简化的p值计算
        self.p_value = self.calculate_p_value(self.test_statistic.abs());
        
        Ok(self.p_value < self.alpha)
    }
    
    /// 计算t分布的临界值（简化实现）
    fn t_critical_value(&self, df: f64) -> f64 {
        // 简化的t分布临界值
        match self.alpha {
            0.05 => 1.96,
            0.01 => 2.58,
            _ => 1.96,
        }
    }
    
    /// 计算p值（简化实现）
    fn calculate_p_value(&self, t_stat: f64) -> f64 {
        // 简化的p值计算
        if t_stat > 3.0 {
            0.001
        } else if t_stat > 2.0 {
            0.05
        } else {
            0.5
        }
    }
}

/// 时间序列分析
#[derive(Debug)]
pub struct TimeSeriesAnalysis {
    pub data: Vec<(chrono::DateTime<chrono::Utc>, f64)>,
}

impl TimeSeriesAnalysis {
    pub fn new() -> Self {
        TimeSeriesAnalysis {
            data: Vec::new(),
        }
    }
    
    /// 添加时间序列数据
    pub fn add_data_point(&mut self, timestamp: chrono::DateTime<chrono::Utc>, value: f64) {
        self.data.push((timestamp, value));
        self.data.sort_by_key(|(timestamp, _)| *timestamp);
    }
    
    /// 计算移动平均
    pub fn moving_average(&self, window_size: usize) -> Vec<f64> {
        let mut result = Vec::new();
        
        for i in (window_size - 1)..self.data.len() {
            let window_sum: f64 = self.data[i - window_size + 1..=i]
                .iter()
                .map(|(_, value)| value)
                .sum();
            
            result.push(window_sum / window_size as f64);
        }
        
        result
    }
    
    /// 计算趋势
    pub fn calculate_trend(&self) -> f64 {
        let n = self.data.len() as f64;
        let x_sum: f64 = (0..self.data.len()).map(|i| i as f64).sum();
        let y_sum: f64 = self.data.iter().map(|(_, value)| value).sum();
        
        let xy_sum: f64 = self.data.iter()
            .enumerate()
            .map(|(i, (_, value))| (i as f64) * value)
            .sum();
        
        let x_squared_sum: f64 = (0..self.data.len())
            .map(|i| (i as f64).powi(2))
            .sum();
        
        let slope = (n * xy_sum - x_sum * y_sum) / (n * x_squared_sum - x_sum.powi(2));
        slope
    }
    
    /// 季节性分解
    pub fn seasonal_decomposition(&self, period: usize) -> (Vec<f64>, Vec<f64>, Vec<f64>) {
        let n = self.data.len();
        let values: Vec<f64> = self.data.iter().map(|(_, value)| *value).collect();
        
        // 计算趋势（使用移动平均）
        let trend = self.moving_average(period);
        
        // 计算季节性
        let mut seasonal = vec![0.0; period];
        let mut seasonal_counts = vec![0; period];
        
        for i in 0..n {
            let seasonal_idx = i % period;
            if i < trend.len() {
                seasonal[seasonal_idx] += values[i] - trend[i];
                seasonal_counts[seasonal_idx] += 1;
            }
        }
        
        for i in 0..period {
            if seasonal_counts[i] > 0 {
                seasonal[i] /= seasonal_counts[i] as f64;
            }
        }
        
        // 计算残差
        let mut residuals = Vec::new();
        for i in 0..n {
            let seasonal_value = seasonal[i % period];
            let trend_value = if i < trend.len() { trend[i] } else { 0.0 };
            residuals.push(values[i] - trend_value - seasonal_value);
        }
        
        (trend, seasonal, residuals)
    }
}
```

## 4 应用示例

### 4.1 示例1：线性回归分析

```rust
fn main() {
    // 创建数据集
    let mut dataset = Dataset::new(vec![
        "feature1".to_string(),
        "feature2".to_string(),
    ]);
    
    // 添加数据
    for i in 0..100 {
        let x1 = i as f64;
        let x2 = (i * 2) as f64;
        let y = 2.0 * x1 + 3.0 * x2 + 1.0 + (rand::random::<f64>() - 0.5) * 0.1;
        
        dataset.add_row(vec![
            DataType::Numeric(x1),
            DataType::Numeric(x2),
        ]).unwrap();
        
        if dataset.target.is_none() {
            dataset.target = Some(Vec::new());
        }
        dataset.target.as_mut().unwrap().push(DataType::Numeric(y));
    }
    
    // 准备训练数据
    let mut X = Array2::zeros((100, 2));
    let mut y = Array1::zeros(100);
    
    for i in 0..100 {
        if let DataType::Numeric(x1) = dataset.data[i][0] {
            X[[i, 0]] = x1;
        }
        if let DataType::Numeric(x2) = dataset.data[i][1] {
            X[[i, 1]] = x2;
        }
        if let DataType::Numeric(target) = dataset.target.as_ref().unwrap()[i] {
            y[i] = target;
        }
    }
    
    // 训练线性回归模型
    let mut model = LinearRegression::new();
    model.fit(&X, &y).unwrap();
    
    println!("Model coefficients: {:?}", model.coefficients);
    println!("Model intercept: {}", model.intercept);
    println!("R² score: {}", model.score(&X, &y));
}
```

### 4.2 示例2：聚类分析

```rust
fn main() {
    // 生成聚类数据
    let mut rng = rand::thread_rng();
    let mut X = Array2::zeros((300, 2));
    
    // 生成三个聚类
    for i in 0..100 {
        X[[i, 0]] = rng.gen_range(-2.0..2.0);
        X[[i, 1]] = rng.gen_range(-2.0..2.0);
    }
    
    for i in 100..200 {
        X[[i, 0]] = rng.gen_range(3.0..7.0);
        X[[i, 1]] = rng.gen_range(3.0..7.0);
    }
    
    for i in 200..300 {
        X[[i, 0]] = rng.gen_range(-1.0..3.0);
        X[[i, 1]] = rng.gen_range(8.0..12.0);
    }
    
    // 训练K-means模型
    let mut kmeans = KMeans::new(3);
    kmeans.fit(&X).unwrap();
    
    println!("Cluster centroids: {:?}", kmeans.centroids);
    
    // 预测新数据点的聚类
    let new_data = Array2::from_shape_vec((1, 2), vec![1.0, 1.0]).unwrap();
    let cluster = kmeans.predict(&new_data);
    println!("New data point cluster: {}", cluster[0]);
}
```

### 4.3 示例3：关联规则挖掘

```rust
fn main() {
    // 创建交易数据
    let transactions = vec![
        vec!["milk".to_string(), "bread".to_string(), "butter".to_string()],
        vec!["bread".to_string(), "cheese".to_string()],
        vec!["milk".to_string(), "bread".to_string(), "cheese".to_string()],
        vec!["bread".to_string(), "butter".to_string()],
        vec!["milk".to_string(), "bread".to_string()],
    ];
    
    // 挖掘关联规则
    let mining = AssociationRuleMining::new(0.3, 0.6);
    let rules = mining.mine_rules(&transactions);
    
    println!("Found {} association rules:", rules.len());
    for rule in &rules {
        println!("{:?} -> {:?} (support: {:.3}, confidence: {:.3}, lift: {:.3})",
                 rule.antecedent, rule.consequent, rule.support, rule.confidence, rule.lift);
    }
}
```

## 5 理论扩展

### 5.1 深度学习理论

**定义 4.1** (神经网络)
神经网络是函数逼近器：$f(x) = \sigma(W_n \sigma(W_{n-1} \cdots \sigma(W_1 x + b_1) \cdots + b_{n-1}) + b_n)$

**定理 4.1** (通用逼近定理)
具有足够隐藏单元的单隐藏层神经网络可以逼近任意连续函数。

### 5.2 贝叶斯统计理论

**定义 4.2** (贝叶斯定理)
$P(A|B) = \frac{P(B|A)P(A)}{P(B)}$

**定理 4.2** (贝叶斯更新)
后验概率正比于似然与先验的乘积。

### 5.3 信息论在数据科学中的应用

**定义 4.3** (信息熵)
$H(X) = -\sum_{i} p_i \log p_i$

**定理 4.3** (最大熵原理)
在给定约束条件下，熵最大的分布是最优的。

## 6 批判性分析

### 6.1 多元理论视角

- 统计视角：数据科学理论基于统计学原理，提供数据分析和推断方法。
- 机器学习视角：数据科学理论通过机器学习算法实现模式识别和预测。
- 信息视角：数据科学理论利用信息论处理数据中的信息和不确定性。
- 应用视角：数据科学理论为实际应用提供数据驱动的解决方案。

### 6.2 局限性分析

- 数据质量：数据质量和偏见问题影响分析结果的可靠性。
- 模型解释性：复杂模型的解释性不足，影响决策的可信度。
- 过拟合问题：模型过拟合和泛化能力不足影响实际应用效果。
- 隐私保护：数据科学应用面临隐私保护和数据安全的挑战。

### 6.3 争议与分歧

- 模型选择：不同机器学习算法的适用性和性能比较。
- 特征工程：手工特征工程vs自动特征学习的策略选择。
- 评估方法：不同模型评估指标的有效性和适用性。
- 公平性：算法公平性和偏见问题的处理方法。

### 6.4 应用前景

- 商业智能：企业数据分析和决策支持系统。
- 医疗健康：医疗数据分析和个性化医疗。
- 金融科技：金融风险分析和智能投资。
- 智能交通：交通数据分析和智能交通管理。

### 6.5 改进建议

- 发展更强大的数据质量评估和处理技术。
- 建立更透明的模型解释和可解释AI方法。
- 加强数据科学应用的隐私保护和公平性。
- 促进数据科学理论的教育和标准化。

## 📚 参考文献

1. Hastie, T., et al. (2009). "The Elements of Statistical Learning"
2. Bishop, C. M. (2006). "Pattern Recognition and Machine Learning"
3. Murphy, K. P. (2012). "Machine Learning: A Probabilistic Perspective"
4. Han, J., et al. (2011). "Data Mining: Concepts and Techniques"
5. Wasserman, L. (2004). "All of Statistics"

---

*本模块为形式科学知识库的重要组成部分，为数据科学和机器学习提供理论基础。通过严格的数学形式化和Rust代码实现，确保理论的可验证性和实用性。*
