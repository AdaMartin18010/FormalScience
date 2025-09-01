# 02 查询执行计划理论

## 目录

- [02 查询执行计划理论](#02-查询执行计划理论)
  - [目录](#目录)
  - [📋 概述](#-概述)
  - [1. 基本概念](#1-基本概念)
    - [1.1 执行计划定义](#11-执行计划定义)
    - [1.2 计划类型分类](#12-计划类型分类)
  - [2. 形式化定义](#2-形式化定义)
    - [2.1 扫描操作](#21-扫描操作)
    - [2.2 连接操作](#22-连接操作)
    - [2.3 聚合操作](#23-聚合操作)
  - [3. 定理与证明](#3-定理与证明)
    - [3.1 计划优化定理](#31-计划优化定理)
    - [3.2 成本估算定理](#32-成本估算定理)
  - [4. Rust代码实现](#4-rust代码实现)
    - [4.1 执行计划构建](#41-执行计划构建)
    - [4.2 计划优化器](#42-计划优化器)
    - [4.3 成本估算器](#43-成本估算器)
  - [5. 相关理论与交叉引用](#5-相关理论与交叉引用)
  - [6. 参考文献](#6-参考文献)
  - [批判性分析](#批判性分析)
    - [主要理论观点梳理](#主要理论观点梳理)
    - [理论优势与局限性](#理论优势与局限性)
    - [学科交叉融合](#学科交叉融合)
    - [创新批判与未来展望](#创新批判与未来展望)
    - [参考文献](#参考文献)

## 📋 概述

查询执行计划理论研究数据库查询的执行策略、优化方法和成本分析。
该理论涵盖扫描、连接、聚合等核心操作，为查询性能优化提供理论基础。

## 1. 基本概念

### 1.1 执行计划定义

**定义 1.1**（查询执行计划）
查询执行计划是数据库系统为执行查询而制定的操作序列和策略。

### 1.2 计划类型分类

| 计划类型     | 英文名称         | 描述                         | 典型应用         |
|--------------|------------------|------------------------------|------------------|
| 表扫描       | Table Scan       | 顺序扫描整个表               | 小表查询         |
| 索引扫描     | Index Scan       | 通过索引快速定位数据         | 条件查询         |
| 嵌套循环连接 | Nested Loop Join | 双重循环实现表连接           | 小表连接         |
| 哈希连接     | Hash Join        | 基于哈希表的连接算法         | 大表连接         |
| 排序合并连接 | Sort Merge Join  | 排序后合并的连接算法         | 有序数据连接     |

## 2. 形式化定义

### 2.1 扫描操作

**定义 2.1**（表扫描）
表扫描是顺序读取表中所有行的操作。

**定义 2.2**（索引扫描）
索引扫描是通过索引结构快速定位满足条件的数据。

### 2.2 连接操作

**定义 2.3**（嵌套循环连接）
嵌套循环连接通过双重循环比较两个表的每一行。

**定义 2.4**（哈希连接）
哈希连接通过构建哈希表实现高效的连接操作。

### 2.3 聚合操作

**定义 2.5**（聚合操作）
聚合操作是对数据进行分组和统计的操作。

## 3. 定理与证明

### 3.1 计划优化定理

**定理 3.1**（连接顺序优化）
对于多表连接，不同的连接顺序会产生不同的执行成本。

**证明**：
设表A、B、C的大小分别为|A|、|B|、|C|，连接顺序(A⋈B)⋈C的成本为O(|A|×|B|×|C|)，
而A⋈(B⋈C)的成本为O(|A|×|B|×|C|)，但中间结果大小不同，导致实际成本差异。□

### 3.2 成本估算定理

**定理 3.2**（索引扫描成本）
索引扫描的成本为O(log n + k)，其中n是索引大小，k是结果集大小。

**证明**：
索引查找需要O(log n)时间定位到叶子节点，然后需要O(k)时间读取k个结果，
因此总成本为O(log n + k)。□

## 4. Rust代码实现

### 4.1 执行计划构建

```rust
use std::collections::HashMap;

#[derive(Debug)]
pub enum PlanNode {
    TableScan {
        table_name: String,
        filter: Option<FilterCondition>,
    },
    IndexScan {
        table_name: String,
        index_name: String,
        filter: Option<FilterCondition>,
    },
    NestedLoopJoin {
        left: Box<PlanNode>,
        right: Box<PlanNode>,
        condition: JoinCondition,
    },
    HashJoin {
        left: Box<PlanNode>,
        right: Box<PlanNode>,
        condition: JoinCondition,
    },
    SortMergeJoin {
        left: Box<PlanNode>,
        right: Box<PlanNode>,
        condition: JoinCondition,
    },
    Aggregate {
        input: Box<PlanNode>,
        group_by: Vec<String>,
        aggregates: Vec<AggregateFunction>,
    },
    Sort {
        input: Box<PlanNode>,
        order_by: Vec<SortField>,
    },
}

#[derive(Debug)]
pub struct FilterCondition {
    pub field: String,
    pub operator: String,
    pub value: String,
}

#[derive(Debug)]
pub struct JoinCondition {
    pub left_field: String,
    pub right_field: String,
    pub operator: String,
}

#[derive(Debug)]
pub struct SortField {
    pub field: String,
    pub direction: SortDirection,
}

#[derive(Debug)]
pub enum SortDirection {
    Ascending,
    Descending,
}

#[derive(Debug)]
pub struct AggregateFunction {
    pub function: String,
    pub field: String,
    pub alias: String,
}

pub struct ExecutionPlan {
    pub root: PlanNode,
    pub estimated_cost: f64,
    pub estimated_rows: usize,
}

impl ExecutionPlan {
    pub fn new(root: PlanNode) -> Self {
        ExecutionPlan {
            root,
            estimated_cost: 0.0,
            estimated_rows: 0,
        }
    }
    
    pub fn estimate_cost(&mut self) -> f64 {
        self.estimated_cost = self.estimate_node_cost(&self.root);
        self.estimated_cost
    }
    
    fn estimate_node_cost(&self, node: &PlanNode) -> f64 {
        match node {
            PlanNode::TableScan { table_name, filter } => {
                let table_size = self.get_table_size(table_name);
                let selectivity = self.estimate_filter_selectivity(filter);
                table_size as f64 * selectivity
            }
            PlanNode::IndexScan { table_name, index_name, filter } => {
                let table_size = self.get_table_size(table_name);
                let index_selectivity = self.get_index_selectivity(index_name);
                let filter_selectivity = self.estimate_filter_selectivity(filter);
                (table_size as f64 * index_selectivity * filter_selectivity).log2() + 
                (table_size as f64 * index_selectivity * filter_selectivity)
            }
            PlanNode::NestedLoopJoin { left, right, condition } => {
                let left_cost = self.estimate_node_cost(left);
                let right_cost = self.estimate_node_cost(right);
                let left_rows = self.estimate_node_rows(left);
                let right_rows = self.estimate_node_rows(right);
                left_cost + right_cost + (left_rows * right_rows) as f64
            }
            PlanNode::HashJoin { left, right, condition } => {
                let left_cost = self.estimate_node_cost(left);
                let right_cost = self.estimate_node_cost(right);
                let left_rows = self.estimate_node_rows(left);
                let right_rows = self.estimate_node_rows(right);
                left_cost + right_cost + left_rows as f64 + right_rows as f64
            }
            PlanNode::SortMergeJoin { left, right, condition } => {
                let left_cost = self.estimate_node_cost(left);
                let right_cost = self.estimate_node_cost(right);
                let left_rows = self.estimate_node_rows(left);
                let right_rows = self.estimate_node_rows(right);
                left_cost + right_cost + (left_rows * left_rows.log2()) as f64 + 
                (right_rows * right_rows.log2()) as f64
            }
            PlanNode::Aggregate { input, group_by, aggregates } => {
                let input_cost = self.estimate_node_cost(input);
                let input_rows = self.estimate_node_rows(input);
                input_cost + (input_rows / group_by.len().max(1)) as f64
            }
            PlanNode::Sort { input, order_by } => {
                let input_cost = self.estimate_node_cost(input);
                let input_rows = self.estimate_node_rows(input);
                input_cost + (input_rows * input_rows.log2()) as f64
            }
        }
    }
    
    fn estimate_node_rows(&self, node: &PlanNode) -> usize {
        match node {
            PlanNode::TableScan { table_name, filter } => {
                let table_size = self.get_table_size(table_name);
                let selectivity = self.estimate_filter_selectivity(filter);
                (table_size as f64 * selectivity) as usize
            }
            PlanNode::IndexScan { table_name, index_name, filter } => {
                let table_size = self.get_table_size(table_name);
                let index_selectivity = self.get_index_selectivity(index_name);
                let filter_selectivity = self.estimate_filter_selectivity(filter);
                (table_size as f64 * index_selectivity * filter_selectivity) as usize
            }
            PlanNode::NestedLoopJoin { left, right, condition } => {
                let left_rows = self.estimate_node_rows(left);
                let right_rows = self.estimate_node_rows(right);
                left_rows * right_rows
            }
            PlanNode::HashJoin { left, right, condition } => {
                let left_rows = self.estimate_node_rows(left);
                let right_rows = self.estimate_node_rows(right);
                left_rows.min(right_rows)
            }
            PlanNode::SortMergeJoin { left, right, condition } => {
                let left_rows = self.estimate_node_rows(left);
                let right_rows = self.estimate_node_rows(right);
                left_rows.min(right_rows)
            }
            PlanNode::Aggregate { input, group_by, aggregates } => {
                let input_rows = self.estimate_node_rows(input);
                input_rows / group_by.len().max(1)
            }
            PlanNode::Sort { input, order_by } => {
                self.estimate_node_rows(input)
            }
        }
    }
    
    fn get_table_size(&self, table_name: &str) -> usize {
        // 简化的表大小估算
        match table_name {
            "users" => 10000,
            "orders" => 100000,
            "products" => 1000,
            _ => 1000,
        }
    }
    
    fn get_index_selectivity(&self, index_name: &str) -> f64 {
        // 简化的索引选择性估算
        match index_name {
            "primary_key" => 0.01,
            "secondary_index" => 0.1,
            _ => 0.5,
        }
    }
    
    fn estimate_filter_selectivity(&self, filter: &Option<FilterCondition>) -> f64 {
        match filter {
            Some(_) => 0.1, // 简化的选择性估算
            None => 1.0,
        }
    }
}
```

### 4.2 计划优化器

```rust
use std::collections::HashMap;

pub struct QueryOptimizer {
    pub statistics: QueryStatistics,
    pub rules: Vec<OptimizationRule>,
}

#[derive(Debug)]
pub struct QueryStatistics {
    pub table_sizes: HashMap<String, usize>,
    pub column_cardinalities: HashMap<String, usize>,
    pub index_selectivities: HashMap<String, f64>,
}

#[derive(Debug)]
pub struct OptimizationRule {
    pub name: String,
    pub priority: u32,
}

impl QueryOptimizer {
    pub fn new() -> Self {
        QueryOptimizer {
            statistics: QueryStatistics {
                table_sizes: HashMap::new(),
                column_cardinalities: HashMap::new(),
                index_selectivities: HashMap::new(),
            },
            rules: vec![
                OptimizationRule { name: "PushDownFilter".to_string(), priority: 1 },
                OptimizationRule { name: "ReorderJoins".to_string(), priority: 2 },
                OptimizationRule { name: "UseIndex".to_string(), priority: 3 },
            ],
        }
    }
    
    pub fn optimize(&self, plan: &mut ExecutionPlan) -> ExecutionPlan {
        let mut optimized_plan = plan.clone();
        
        // 应用优化规则
        for rule in &self.rules {
            optimized_plan = self.apply_rule(&optimized_plan, rule);
        }
        
        optimized_plan
    }
    
    fn apply_rule(&self, plan: &ExecutionPlan, rule: &OptimizationRule) -> ExecutionPlan {
        match rule.name.as_str() {
            "PushDownFilter" => self.push_down_filter(plan),
            "ReorderJoins" => self.reorder_joins(plan),
            "UseIndex" => self.use_index(plan),
            _ => plan.clone(),
        }
    }
    
    fn push_down_filter(&self, plan: &ExecutionPlan) -> ExecutionPlan {
        // 将过滤条件下推到叶子节点
        let mut new_plan = plan.clone();
        new_plan.root = self.push_down_filter_recursive(&plan.root);
        new_plan
    }
    
    fn push_down_filter_recursive(&self, node: &PlanNode) -> PlanNode {
        match node {
            PlanNode::NestedLoopJoin { left, right, condition } => {
                let optimized_left = self.push_down_filter_recursive(left);
                let optimized_right = self.push_down_filter_recursive(right);
                PlanNode::NestedLoopJoin {
                    left: Box::new(optimized_left),
                    right: Box::new(optimized_right),
                    condition: condition.clone(),
                }
            }
            PlanNode::TableScan { table_name, filter } => {
                // 尝试优化表扫描
                if let Some(index_name) = self.find_better_index(table_name, filter) {
                    PlanNode::IndexScan {
                        table_name: table_name.clone(),
                        index_name,
                        filter: filter.clone(),
                    }
                } else {
                    node.clone()
                }
            }
            _ => node.clone(),
        }
    }
    
    fn reorder_joins(&self, plan: &ExecutionPlan) -> ExecutionPlan {
        // 重新排序连接操作
        let mut new_plan = plan.clone();
        new_plan.root = self.reorder_joins_recursive(&plan.root);
        new_plan
    }
    
    fn reorder_joins_recursive(&self, node: &PlanNode) -> PlanNode {
        match node {
            PlanNode::NestedLoopJoin { left, right, condition } => {
                let left_cost = self.estimate_node_cost(left);
                let right_cost = self.estimate_node_cost(right);
                
                // 选择成本较低的作为左子树
                if left_cost > right_cost {
                    PlanNode::NestedLoopJoin {
                        left: Box::new(self.reorder_joins_recursive(right)),
                        right: Box::new(self.reorder_joins_recursive(left)),
                        condition: condition.clone(),
                    }
                } else {
                    PlanNode::NestedLoopJoin {
                        left: Box::new(self.reorder_joins_recursive(left)),
                        right: Box::new(self.reorder_joins_recursive(right)),
                        condition: condition.clone(),
                    }
                }
            }
            _ => node.clone(),
        }
    }
    
    fn use_index(&self, plan: &ExecutionPlan) -> ExecutionPlan {
        // 使用索引优化查询
        let mut new_plan = plan.clone();
        new_plan.root = self.use_index_recursive(&plan.root);
        new_plan
    }
    
    fn use_index_recursive(&self, node: &PlanNode) -> PlanNode {
        match node {
            PlanNode::TableScan { table_name, filter } => {
                if let Some(index_name) = self.find_better_index(table_name, filter) {
                    PlanNode::IndexScan {
                        table_name: table_name.clone(),
                        index_name,
                        filter: filter.clone(),
                    }
                } else {
                    node.clone()
                }
            }
            _ => node.clone(),
        }
    }
    
    fn find_better_index(&self, table_name: &str, filter: &Option<FilterCondition>) -> Option<String> {
        // 简化的索引选择逻辑
        match filter {
            Some(_) => Some("secondary_index".to_string()),
            None => None,
        }
    }
    
    fn estimate_node_cost(&self, node: &PlanNode) -> f64 {
        // 简化的成本估算
        match node {
            PlanNode::TableScan { .. } => 1000.0,
            PlanNode::IndexScan { .. } => 100.0,
            PlanNode::NestedLoopJoin { .. } => 5000.0,
            _ => 1000.0,
        }
    }
}
```

### 4.3 成本估算器

```rust
use std::collections::HashMap;

pub struct CostEstimator {
    pub statistics: QueryStatistics,
    pub cost_models: HashMap<String, CostModel>,
}

#[derive(Debug)]
pub struct CostModel {
    pub cpu_cost_per_row: f64,
    pub io_cost_per_page: f64,
    pub memory_cost_per_mb: f64,
}

impl CostEstimator {
    pub fn new() -> Self {
        let mut cost_models = HashMap::new();
        cost_models.insert("TableScan".to_string(), CostModel {
            cpu_cost_per_row: 0.1,
            io_cost_per_page: 10.0,
            memory_cost_per_mb: 1.0,
        });
        cost_models.insert("IndexScan".to_string(), CostModel {
            cpu_cost_per_row: 0.05,
            io_cost_per_page: 5.0,
            memory_cost_per_mb: 0.5,
        });
        cost_models.insert("HashJoin".to_string(), CostModel {
            cpu_cost_per_row: 0.2,
            io_cost_per_page: 20.0,
            memory_cost_per_mb: 2.0,
        });
        
        CostEstimator {
            statistics: QueryStatistics {
                table_sizes: HashMap::new(),
                column_cardinalities: HashMap::new(),
                index_selectivities: HashMap::new(),
            },
            cost_models,
        }
    }
    
    pub fn estimate_cost(&self, plan: &ExecutionPlan) -> f64 {
        self.estimate_node_cost(&plan.root)
    }
    
    fn estimate_node_cost(&self, node: &PlanNode) -> f64 {
        match node {
            PlanNode::TableScan { table_name, filter } => {
                let table_size = self.get_table_size(table_name);
                let selectivity = self.estimate_selectivity(filter);
                let rows = (table_size as f64 * selectivity) as usize;
                let pages = (rows as f64 / 100.0).ceil() as usize; // 假设每页100行
                
                let model = self.cost_models.get("TableScan").unwrap();
                rows as f64 * model.cpu_cost_per_row + 
                pages as f64 * model.io_cost_per_page
            }
            PlanNode::IndexScan { table_name, index_name, filter } => {
                let table_size = self.get_table_size(table_name);
                let index_selectivity = self.get_index_selectivity(index_name);
                let filter_selectivity = self.estimate_selectivity(filter);
                let rows = (table_size as f64 * index_selectivity * filter_selectivity) as usize;
                let pages = (rows as f64 / 100.0).ceil() as usize;
                
                let model = self.cost_models.get("IndexScan").unwrap();
                rows as f64 * model.cpu_cost_per_row + 
                pages as f64 * model.io_cost_per_page
            }
            PlanNode::HashJoin { left, right, condition } => {
                let left_cost = self.estimate_node_cost(left);
                let right_cost = self.estimate_node_cost(right);
                let left_rows = self.estimate_node_rows(left);
                let right_rows = self.estimate_node_rows(right);
                
                let model = self.cost_models.get("HashJoin").unwrap();
                left_cost + right_cost + 
                (left_rows + right_rows) as f64 * model.cpu_cost_per_row
            }
            _ => 1000.0, // 默认成本
        }
    }
    
    fn estimate_node_rows(&self, node: &PlanNode) -> usize {
        match node {
            PlanNode::TableScan { table_name, filter } => {
                let table_size = self.get_table_size(table_name);
                let selectivity = self.estimate_selectivity(filter);
                (table_size as f64 * selectivity) as usize
            }
            PlanNode::IndexScan { table_name, index_name, filter } => {
                let table_size = self.get_table_size(table_name);
                let index_selectivity = self.get_index_selectivity(index_name);
                let filter_selectivity = self.estimate_selectivity(filter);
                (table_size as f64 * index_selectivity * filter_selectivity) as usize
            }
            _ => 1000, // 默认行数
        }
    }
    
    fn get_table_size(&self, table_name: &str) -> usize {
        match table_name {
            "users" => 10000,
            "orders" => 100000,
            "products" => 1000,
            _ => 1000,
        }
    }
    
    fn get_index_selectivity(&self, index_name: &str) -> f64 {
        match index_name {
            "primary_key" => 0.01,
            "secondary_index" => 0.1,
            _ => 0.5,
        }
    }
    
    fn estimate_selectivity(&self, filter: &Option<FilterCondition>) -> f64 {
        match filter {
            Some(_) => 0.1,
            None => 1.0,
        }
    }
}
```

## 5. 相关理论与交叉引用

- **数学基础**：算法复杂性、统计学在成本估算中的应用
- **形式语言理论**：查询语言的形式化语义
- **类型理论**：执行计划的类型安全保证
- **控制论**：查询执行的反馈控制机制
- **人工智能理论**：智能化的计划选择和优化

## 6. 参考文献

1. Selinger, P. G., et al. (1979). "Access path selection in a relational database management system"
2. Ioannidis, Y. E. (1996). "Query optimization"
3. Chaudhuri, S. (1998). "An overview of query optimization in relational systems"
4. Graefe, G. (1993). "Query evaluation techniques for large databases"

## 批判性分析

### 主要理论观点梳理

查询执行计划理论关注查询优化、成本分析和执行策略，是构建高性能数据库系统的重要基础。

### 理论优势与局限性

**优势**：

- 提供了系统化的查询优化方法
- 建立了多维度的成本分析体系
- 支持复杂查询的高效执行

**局限性**：

- 成本估算的准确性挑战
- 优化规则的复杂性管理
- 动态环境下的适应性需求

### 学科交叉融合

- 与数学基础在算法复杂性、统计学等领域有深入应用
- 与形式语言理论在查询语义、执行计划等方面有创新应用
- 与人工智能理论在智能优化、自适应调优等方面有新兴融合
- 与控制论在性能反馈、动态调整等方面互补

### 创新批判与未来展望

未来查询执行计划理论需加强与AI、机器学习、自适应系统等领域的融合，推动智能化、自适应的查询优化。

### 参考文献

- 交叉索引.md
- Meta/批判性分析模板.md
