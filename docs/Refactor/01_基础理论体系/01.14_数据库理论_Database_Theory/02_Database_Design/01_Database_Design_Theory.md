# 12.2.1 数据库设计理论

## 目录

- [12.2.1 数据库设计理论](#1221-数据库设计理论)
  - [目录](#目录)
  - [📋 概述](#-概述)
  - [1. 基本概念](#1-基本概念)
    - [1.1 数据库设计定义](#11-数据库设计定义)
    - [1.2 设计阶段分类](#12-设计阶段分类)
  - [2. 形式化定义](#2-形式化定义)
    - [2.1 需求分析](#21-需求分析)
    - [2.2 概念设计](#22-概念设计)
    - [2.3 逻辑设计](#23-逻辑设计)
  - [3. 定理与证明](#3-定理与证明)
    - [3.1 设计完整性定理](#31-设计完整性定理)
    - [3.2 性能优化定理](#32-性能优化定理)
  - [4. Rust代码实现](#4-rust代码实现)
    - [4.1 需求分析系统实现](#41-需求分析系统实现)
    - [4.2 逻辑设计系统实现](#42-逻辑设计系统实现)
    - [4.3 物理设计系统实现](#43-物理设计系统实现)
  - [5. 相关理论与交叉引用](#5-相关理论与交叉引用)
  - [6. 参考文献](#6-参考文献)
  - [批判性分析](#批判性分析)

## 📋 概述

数据库设计理论研究如何设计高效、可靠、可维护的数据库系统。该理论涵盖需求分析、概念设计、逻辑设计、物理设计等核心概念，为数据库系统构建提供理论基础。

## 1. 基本概念

### 1.1 数据库设计定义

**定义 1.1**（数据库设计）
数据库设计是创建数据库结构的过程，包括表结构、关系、约束和索引的设计。

### 1.2 设计阶段分类

| 设计阶段     | 英文名称         | 主要任务                     | 输出产物         |
|--------------|------------------|------------------------------|------------------|
| 需求分析     | Requirements     | 收集和分析用户需求           | 需求规格说明书   |
| 概念设计     | Conceptual       | 建立概念数据模型             | ER图, UML图      |
| 逻辑设计     | Logical          | 转换为逻辑数据模型           | 关系模式         |
| 物理设计     | Physical         | 实现物理存储结构             | 数据库模式       |

## 2. 形式化定义

### 2.1 需求分析

**定义 2.1**（需求分析）
需求分析是识别、收集和分析数据库系统功能和非功能需求的过程。

### 2.2 概念设计

**定义 2.2**（概念设计）
概念设计是将用户需求转换为概念数据模型的过程。

### 2.3 逻辑设计

**定义 2.3**（逻辑设计）
逻辑设计是将概念模型转换为特定数据模型的逻辑结构。

## 3. 定理与证明

### 3.1 设计完整性定理

**定理 3.1**（设计完整性）
若数据库设计满足所有功能需求且无冗余，则称设计完整。

**证明**：
设需求集合为 $R$，设计集合为 $D$，若 $\forall r \in R, \exists d \in D$ 满足 $r$，且 $D$ 中无冗余元素，则设计完整。□

### 3.2 性能优化定理

**定理 3.2**（性能优化）
通过适当的索引设计和查询优化，数据库查询性能可显著提升。

**证明**：
索引将查询复杂度从 $O(n)$ 降低到 $O(\log n)$，查询优化器选择最优执行计划。□

## 4. Rust代码实现

### 4.1 需求分析系统实现

```rust
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone)]
pub struct Requirement {
    pub id: String,
    pub name: String,
    pub description: String,
    pub priority: Priority,
    pub category: RequirementCategory,
    pub stakeholders: Vec<String>,
    pub acceptance_criteria: Vec<String>,
}

#[derive(Debug, Clone)]
pub enum Priority {
    High,
    Medium,
    Low,
}

#[derive(Debug, Clone)]
pub enum RequirementCategory {
    Functional,
    NonFunctional,
    Constraint,
}

#[derive(Debug, Clone)]
pub struct RequirementAnalysis {
    pub requirements: HashMap<String, Requirement>,
    pub entities: Vec<Entity>,
    pub relationships: Vec<Relationship>,
    pub constraints: Vec<Constraint>,
}

#[derive(Debug, Clone)]
pub struct Entity {
    pub name: String,
    pub attributes: Vec<Attribute>,
    pub description: String,
    pub business_rules: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct Relationship {
    pub name: String,
    pub entity1: String,
    pub entity2: String,
    pub cardinality: Cardinality,
    pub description: String,
}

#[derive(Debug, Clone)]
pub enum Cardinality {
    OneToOne,
    OneToMany,
    ManyToOne,
    ManyToMany,
}

#[derive(Debug, Clone)]
pub struct Constraint {
    pub name: String,
    pub constraint_type: ConstraintType,
    pub description: String,
    pub affected_entities: Vec<String>,
}

#[derive(Debug, Clone)]
pub enum ConstraintType {
    PrimaryKey,
    ForeignKey,
    Unique,
    Check,
    NotNull,
}

impl RequirementAnalysis {
    pub fn new() -> Self {
        RequirementAnalysis {
            requirements: HashMap::new(),
            entities: Vec::new(),
            relationships: Vec::new(),
            constraints: Vec::new(),
        }
    }
    
    pub fn add_requirement(&mut self, requirement: Requirement) {
        self.requirements.insert(requirement.id.clone(), requirement);
    }
    
    pub fn add_entity(&mut self, entity: Entity) {
        self.entities.push(entity);
    }
    
    pub fn add_relationship(&mut self, relationship: Relationship) {
        self.relationships.push(relationship);
    }
    
    pub fn add_constraint(&mut self, constraint: Constraint) {
        self.constraints.push(constraint);
    }
    
    pub fn analyze_requirements(&self) -> AnalysisReport {
        let mut report = AnalysisReport::new();
        
        // 分析功能需求
        let functional_requirements: Vec<_> = self.requirements.values()
            .filter(|r| matches!(r.category, RequirementCategory::Functional))
            .collect();
        
        report.functional_count = functional_requirements.len();
        
        // 分析非功能需求
        let non_functional_requirements: Vec<_> = self.requirements.values()
            .filter(|r| matches!(r.category, RequirementCategory::NonFunctional))
            .collect();
        
        report.non_functional_count = non_functional_requirements.len();
        
        // 分析优先级分布
        let mut priority_distribution = HashMap::new();
        for requirement in self.requirements.values() {
            *priority_distribution.entry(requirement.priority.clone()).or_insert(0) += 1;
        }
        report.priority_distribution = priority_distribution;
        
        // 分析实体和关系
        report.entity_count = self.entities.len();
        report.relationship_count = self.relationships.len();
        report.constraint_count = self.constraints.len();
        
        // 检查需求完整性
        report.completeness_score = self.calculate_completeness();
        
        // 检查一致性
        report.consistency_score = self.calculate_consistency();
        
        report
    }
    
    fn calculate_completeness(&self) -> f64 {
        let total_requirements = self.requirements.len();
        if total_requirements == 0 {
            return 0.0;
        }
        
        let mut complete_requirements = 0;
        for requirement in self.requirements.values() {
            if !requirement.description.is_empty() && 
               !requirement.acceptance_criteria.is_empty() &&
               !requirement.stakeholders.is_empty() {
                complete_requirements += 1;
            }
        }
        
        complete_requirements as f64 / total_requirements as f64
    }
    
    fn calculate_consistency(&self) -> f64 {
        let mut consistency_score = 1.0;
        
        // 检查实体名称唯一性
        let mut entity_names = HashSet::new();
        for entity in &self.entities {
            if !entity_names.insert(&entity.name) {
                consistency_score -= 0.1; // 重复实体名称
            }
        }
        
        // 检查关系中的实体是否存在
        for relationship in &self.relationships {
            let entity1_exists = self.entities.iter().any(|e| e.name == relationship.entity1);
            let entity2_exists = self.entities.iter().any(|e| e.name == relationship.entity2);
            
            if !entity1_exists || !entity2_exists {
                consistency_score -= 0.1; // 关系引用不存在的实体
            }
        }
        
        consistency_score.max(0.0)
    }
    
    pub fn generate_er_diagram(&self) -> ERDiagram {
        let mut diagram = ERDiagram::new();
        
        // 添加实体
        for entity in &self.entities {
            diagram.add_entity(entity.clone());
        }
        
        // 添加关系
        for relationship in &self.relationships {
            diagram.add_relationship(relationship.clone());
        }
        
        diagram
    }
    
    pub fn validate_design(&self) -> Vec<String> {
        let mut errors = Vec::new();
        
        // 验证实体
        for entity in &self.entities {
            if entity.name.is_empty() {
                errors.push(format!("Entity has empty name"));
            }
            
            if entity.attributes.is_empty() {
                errors.push(format!("Entity {} has no attributes", entity.name));
            }
        }
        
        // 验证关系
        for relationship in &self.relationships {
            if relationship.entity1 == relationship.entity2 {
                errors.push(format!("Relationship {} connects entity to itself", relationship.name));
            }
        }
        
        // 验证约束
        for constraint in &self.constraints {
            for entity_name in &constraint.affected_entities {
                if !self.entities.iter().any(|e| &e.name == entity_name) {
                    errors.push(format!("Constraint {} references non-existent entity {}", 
                                      constraint.name, entity_name));
                }
            }
        }
        
        errors
    }
}

#[derive(Debug, Clone)]
pub struct AnalysisReport {
    pub functional_count: usize,
    pub non_functional_count: usize,
    pub priority_distribution: HashMap<Priority, usize>,
    pub entity_count: usize,
    pub relationship_count: usize,
    pub constraint_count: usize,
    pub completeness_score: f64,
    pub consistency_score: f64,
}

impl AnalysisReport {
    pub fn new() -> Self {
        AnalysisReport {
            functional_count: 0,
            non_functional_count: 0,
            priority_distribution: HashMap::new(),
            entity_count: 0,
            relationship_count: 0,
            constraint_count: 0,
            completeness_score: 0.0,
            consistency_score: 0.0,
        }
    }
    
    pub fn print_summary(&self) {
        println!("=== 需求分析报告 ===");
        println!("功能需求数量: {}", self.functional_count);
        println!("非功能需求数量: {}", self.non_functional_count);
        println!("实体数量: {}", self.entity_count);
        println!("关系数量: {}", self.relationship_count);
        println!("约束数量: {}", self.constraint_count);
        println!("完整性评分: {:.2}", self.completeness_score);
        println!("一致性评分: {:.2}", self.consistency_score);
    }
}

#[derive(Debug, Clone)]
pub struct ERDiagram {
    pub entities: Vec<Entity>,
    pub relationships: Vec<Relationship>,
}

impl ERDiagram {
    pub fn new() -> Self {
        ERDiagram {
            entities: Vec::new(),
            relationships: Vec::new(),
        }
    }
    
    pub fn add_entity(&mut self, entity: Entity) {
        self.entities.push(entity);
    }
    
    pub fn add_relationship(&mut self, relationship: Relationship) {
        self.relationships.push(relationship);
    }
    
    pub fn export_dot(&self) -> String {
        let mut dot = String::new();
        dot.push_str("digraph ERDiagram {\n");
        dot.push_str("  rankdir=LR;\n");
        dot.push_str("  node [shape=record];\n\n");
        
        // 添加实体
        for entity in &self.entities {
            dot.push_str(&format!("  {} [label=\"{{{}|", entity.name, entity.name));
            
            for (i, attr) in entity.attributes.iter().enumerate() {
                if i > 0 {
                    dot.push_str("|");
                }
                dot.push_str(&attr.name);
            }
            
            dot.push_str("}}\"];\n");
        }
        
        dot.push_str("\n");
        
        // 添加关系
        for relationship in &self.relationships {
            let arrow = match relationship.cardinality {
                Cardinality::OneToOne => "->",
                Cardinality::OneToMany => "->",
                Cardinality::ManyToOne => "->",
                Cardinality::ManyToMany => "<->",
            };
            
            dot.push_str(&format!("  {} {} {} [label=\"{}\"];\n", 
                                 relationship.entity1, arrow, relationship.entity2, relationship.name));
        }
        
        dot.push_str("}\n");
        dot
    }
}
```

### 4.2 逻辑设计系统实现

```rust
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct LogicalDesign {
    pub tables: HashMap<String, Table>,
    pub views: HashMap<String, View>,
    pub indexes: Vec<Index>,
    pub constraints: Vec<TableConstraint>,
}

#[derive(Debug, Clone)]
pub struct Table {
    pub name: String,
    pub columns: Vec<Column>,
    pub primary_key: Vec<String>,
    pub foreign_keys: Vec<ForeignKey>,
    pub unique_constraints: Vec<Vec<String>>,
    pub check_constraints: Vec<CheckConstraint>,
}

#[derive(Debug, Clone)]
pub struct Column {
    pub name: String,
    pub data_type: DataType,
    pub is_nullable: bool,
    pub default_value: Option<String>,
    pub auto_increment: bool,
    pub comment: String,
}

#[derive(Debug, Clone)]
pub enum DataType {
    Integer,
    BigInt,
    Float,
    Double,
    Decimal(usize, usize),
    Char(usize),
    Varchar(usize),
    Text,
    Boolean,
    Date,
    DateTime,
    Timestamp,
    Blob,
}

#[derive(Debug, Clone)]
pub struct ForeignKey {
    pub name: String,
    pub columns: Vec<String>,
    pub referenced_table: String,
    pub referenced_columns: Vec<String>,
    pub on_delete: ReferentialAction,
    pub on_update: ReferentialAction,
}

#[derive(Debug, Clone)]
pub enum ReferentialAction {
    Cascade,
    SetNull,
    SetDefault,
    Restrict,
    NoAction,
}

#[derive(Debug, Clone)]
pub struct CheckConstraint {
    pub name: String,
    pub condition: String,
}

#[derive(Debug, Clone)]
pub struct View {
    pub name: String,
    pub definition: String,
    pub columns: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct Index {
    pub name: String,
    pub table_name: String,
    pub columns: Vec<String>,
    pub index_type: IndexType,
    pub unique: bool,
}

#[derive(Debug, Clone)]
pub enum IndexType {
    BTree,
    Hash,
    FullText,
    Spatial,
}

#[derive(Debug, Clone)]
pub struct TableConstraint {
    pub name: String,
    pub table_name: String,
    pub constraint_type: ConstraintType,
    pub definition: String,
}

#[derive(Debug, Clone)]
pub enum ConstraintType {
    PrimaryKey,
    ForeignKey,
    Unique,
    Check,
    NotNull,
}

impl LogicalDesign {
    pub fn new() -> Self {
        LogicalDesign {
            tables: HashMap::new(),
            views: HashMap::new(),
            indexes: Vec::new(),
            constraints: Vec::new(),
        }
    }
    
    pub fn add_table(&mut self, table: Table) {
        self.tables.insert(table.name.clone(), table);
    }
    
    pub fn add_view(&mut self, view: View) {
        self.views.insert(view.name.clone(), view);
    }
    
    pub fn add_index(&mut self, index: Index) {
        self.indexes.push(index);
    }
    
    pub fn add_constraint(&mut self, constraint: TableConstraint) {
        self.constraints.push(constraint);
    }
    
    pub fn normalize_tables(&mut self) -> Vec<String> {
        let mut messages = Vec::new();
        
        for table in self.tables.values_mut() {
            // 检查1NF
            if !self.is_first_normal_form(table) {
                messages.push(format!("Table {} violates 1NF", table.name));
            }
            
            // 检查2NF
            if !self.is_second_normal_form(table) {
                messages.push(format!("Table {} violates 2NF", table.name));
            }
            
            // 检查3NF
            if !self.is_third_normal_form(table) {
                messages.push(format!("Table {} violates 3NF", table.name));
            }
        }
        
        messages
    }
    
    fn is_first_normal_form(&self, table: &Table) -> bool {
        // 检查是否有重复组
        for column in &table.columns {
            if column.name.contains(',') || column.name.contains(';') {
                return false;
            }
        }
        true
    }
    
    fn is_second_normal_form(&self, table: &Table) -> bool {
        if table.primary_key.len() <= 1 {
            return true; // 单属性主键自动满足2NF
        }
        
        // 检查部分依赖（简化实现）
        true
    }
    
    fn is_third_normal_form(&self, table: &Table) -> bool {
        // 检查传递依赖（简化实现）
        true
    }
    
    pub fn optimize_indexes(&mut self) {
        // 为外键创建索引
        for table in self.tables.values() {
            for fk in &table.foreign_keys {
                let index_name = format!("idx_{}_{}", table.name, fk.name);
                let index = Index {
                    name: index_name,
                    table_name: table.name.clone(),
                    columns: fk.columns.clone(),
                    index_type: IndexType::BTree,
                    unique: false,
                };
                self.indexes.push(index);
            }
        }
        
        // 为经常查询的列创建索引
        for table in self.tables.values() {
            for column in &table.columns {
                if column.name.contains("id") || column.name.contains("name") {
                    let index_name = format!("idx_{}_{}", table.name, column.name);
                    let index = Index {
                        name: index_name,
                        table_name: table.name.clone(),
                        columns: vec![column.name.clone()],
                        index_type: IndexType::BTree,
                        unique: false,
                    };
                    self.indexes.push(index);
                }
            }
        }
    }
    
    pub fn generate_sql(&self) -> String {
        let mut sql = String::new();
        
        // 生成CREATE TABLE语句
        for table in self.tables.values() {
            sql.push_str(&format!("CREATE TABLE {} (\n", table.name));
            
            for (i, column) in table.columns.iter().enumerate() {
                if i > 0 {
                    sql.push_str(",\n");
                }
                sql.push_str(&format!("  {} {}", column.name, self.data_type_to_sql(&column.data_type)));
                
                if !column.is_nullable {
                    sql.push_str(" NOT NULL");
                }
                
                if let Some(default) = &column.default_value {
                    sql.push_str(&format!(" DEFAULT '{}'", default));
                }
                
                if column.auto_increment {
                    sql.push_str(" AUTO_INCREMENT");
                }
            }
            
            // 添加主键约束
            if !table.primary_key.is_empty() {
                sql.push_str(&format!(",\n  PRIMARY KEY ({})", table.primary_key.join(", ")));
            }
            
            // 添加外键约束
            for fk in &table.foreign_keys {
                sql.push_str(&format!(",\n  CONSTRAINT {} FOREIGN KEY ({}) REFERENCES {}({})", 
                                     fk.name, fk.columns.join(", "), fk.referenced_table, fk.referenced_columns.join(", ")));
            }
            
            sql.push_str("\n);\n\n");
        }
        
        // 生成索引
        for index in &self.indexes {
            let unique = if index.unique { "UNIQUE " } else { "" };
            sql.push_str(&format!("CREATE {}INDEX {} ON {} ({});\n", 
                                 unique, index.name, index.table_name, index.columns.join(", ")));
        }
        
        sql
    }
    
    fn data_type_to_sql(&self, data_type: &DataType) -> String {
        match data_type {
            DataType::Integer => "INT".to_string(),
            DataType::BigInt => "BIGINT".to_string(),
            DataType::Float => "FLOAT".to_string(),
            DataType::Double => "DOUBLE".to_string(),
            DataType::Decimal(precision, scale) => format!("DECIMAL({}, {})", precision, scale),
            DataType::Char(length) => format!("CHAR({})", length),
            DataType::Varchar(length) => format!("VARCHAR({})", length),
            DataType::Text => "TEXT".to_string(),
            DataType::Boolean => "BOOLEAN".to_string(),
            DataType::Date => "DATE".to_string(),
            DataType::DateTime => "DATETIME".to_string(),
            DataType::Timestamp => "TIMESTAMP".to_string(),
            DataType::Blob => "BLOB".to_string(),
        }
    }
    
    pub fn calculate_statistics(&self) -> DesignStatistics {
        let mut stats = DesignStatistics::new();
        
        stats.table_count = self.tables.len();
        stats.view_count = self.views.len();
        stats.index_count = self.indexes.len();
        stats.constraint_count = self.constraints.len();
        
        // 计算平均表大小
        let mut total_columns = 0;
        for table in self.tables.values() {
            total_columns += table.columns.len();
        }
        
        if stats.table_count > 0 {
            stats.average_columns_per_table = total_columns as f64 / stats.table_count as f64;
        }
        
        // 计算外键密度
        let mut total_foreign_keys = 0;
        for table in self.tables.values() {
            total_foreign_keys += table.foreign_keys.len();
        }
        
        if stats.table_count > 0 {
            stats.foreign_key_density = total_foreign_keys as f64 / stats.table_count as f64;
        }
        
        stats
    }
}

#[derive(Debug, Clone)]
pub struct DesignStatistics {
    pub table_count: usize,
    pub view_count: usize,
    pub index_count: usize,
    pub constraint_count: usize,
    pub average_columns_per_table: f64,
    pub foreign_key_density: f64,
}

impl DesignStatistics {
    pub fn new() -> Self {
        DesignStatistics {
            table_count: 0,
            view_count: 0,
            index_count: 0,
            constraint_count: 0,
            average_columns_per_table: 0.0,
            foreign_key_density: 0.0,
        }
    }
    
    pub fn print_report(&self) {
        println!("=== 逻辑设计统计 ===");
        println!("表数量: {}", self.table_count);
        println!("视图数量: {}", self.view_count);
        println!("索引数量: {}", self.index_count);
        println!("约束数量: {}", self.constraint_count);
        println!("平均每表列数: {:.2}", self.average_columns_per_table);
        println!("外键密度: {:.2}", self.foreign_key_density);
    }
}
```

### 4.3 物理设计系统实现

```rust
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct PhysicalDesign {
    pub storage_engine: StorageEngine,
    pub tablespaces: HashMap<String, Tablespace>,
    pub partitions: HashMap<String, Partitioning>,
    pub compression: HashMap<String, Compression>,
    pub caching: HashMap<String, Caching>,
}

#[derive(Debug, Clone)]
pub enum StorageEngine {
    InnoDB,
    MyISAM,
    Memory,
    Archive,
    Custom(String),
}

#[derive(Debug, Clone)]
pub struct Tablespace {
    pub name: String,
    pub file_path: String,
    pub initial_size: u64,
    pub auto_extend: bool,
    pub max_size: Option<u64>,
}

#[derive(Debug, Clone)]
pub struct Partitioning {
    pub table_name: String,
    pub partition_type: PartitionType,
    pub partition_columns: Vec<String>,
    pub partitions: Vec<Partition>,
}

#[derive(Debug, Clone)]
pub enum PartitionType {
    Range,
    List,
    Hash,
    Key,
}

#[derive(Debug, Clone)]
pub struct Partition {
    pub name: String,
    pub value: String,
    pub tablespace: String,
}

#[derive(Debug, Clone)]
pub struct Compression {
    pub table_name: String,
    pub algorithm: CompressionAlgorithm,
    pub level: u8,
}

#[derive(Debug, Clone)]
pub enum CompressionAlgorithm {
    Zlib,
    Lz4,
    Zstd,
    Snappy,
}

#[derive(Debug, Clone)]
pub struct Caching {
    pub table_name: String,
    pub cache_type: CacheType,
    pub cache_size: u64,
    pub ttl: Option<u64>,
}

#[derive(Debug, Clone)]
pub enum CacheType {
    Memory,
    Redis,
    Memcached,
}

impl PhysicalDesign {
    pub fn new() -> Self {
        PhysicalDesign {
            storage_engine: StorageEngine::InnoDB,
            tablespaces: HashMap::new(),
            partitions: HashMap::new(),
            compression: HashMap::new(),
            caching: HashMap::new(),
        }
    }
    
    pub fn set_storage_engine(&mut self, engine: StorageEngine) {
        self.storage_engine = engine;
    }
    
    pub fn add_tablespace(&mut self, tablespace: Tablespace) {
        self.tablespaces.insert(tablespace.name.clone(), tablespace);
    }
    
    pub fn add_partitioning(&mut self, partitioning: Partitioning) {
        self.partitions.insert(partitioning.table_name.clone(), partitioning);
    }
    
    pub fn add_compression(&mut self, compression: Compression) {
        self.compression.insert(compression.table_name.clone(), compression);
    }
    
    pub fn add_caching(&mut self, caching: Caching) {
        self.caching.insert(caching.table_name.clone(), caching);
    }
    
    pub fn optimize_for_performance(&mut self, table_name: &str, access_pattern: AccessPattern) {
        match access_pattern {
            AccessPattern::ReadHeavy => {
                // 为读密集型表添加缓存
                let caching = Caching {
                    table_name: table_name.to_string(),
                    cache_type: CacheType::Memory,
                    cache_size: 1024 * 1024 * 100, // 100MB
                    ttl: Some(3600), // 1小时
                };
                self.caching.insert(table_name.to_string(), caching);
            },
            AccessPattern::WriteHeavy => {
                // 为写密集型表使用InnoDB
                self.storage_engine = StorageEngine::InnoDB;
            },
            AccessPattern::Mixed => {
                // 混合访问模式使用InnoDB
                self.storage_engine = StorageEngine::InnoDB;
            },
        }
    }
    
    pub fn generate_ddl(&self) -> String {
        let mut ddl = String::new();
        
        // 创建表空间
        for tablespace in self.tablespaces.values() {
            ddl.push_str(&format!("CREATE TABLESPACE {}\n", tablespace.name));
            ddl.push_str(&format!("  ADD DATAFILE '{}'\n", tablespace.file_path));
            ddl.push_str(&format!("  INITIAL_SIZE {}\n", tablespace.initial_size));
            
            if tablespace.auto_extend {
                ddl.push_str("  AUTOEXTEND_SIZE 1M\n");
            }
            
            if let Some(max_size) = tablespace.max_size {
                ddl.push_str(&format!("  MAX_SIZE {}\n", max_size));
            }
            
            ddl.push_str(";\n\n");
        }
        
        // 创建分区
        for partitioning in self.partitions.values() {
            ddl.push_str(&format!("ALTER TABLE {} PARTITION BY ", partitioning.table_name));
            
            match partitioning.partition_type {
                PartitionType::Range => {
                    ddl.push_str(&format!("RANGE ({}) (\n", partitioning.partition_columns.join(", ")));
                },
                PartitionType::List => {
                    ddl.push_str(&format!("LIST ({}) (\n", partitioning.partition_columns.join(", ")));
                },
                PartitionType::Hash => {
                    ddl.push_str(&format!("HASH ({}) PARTITIONS {}\n", 
                                         partitioning.partition_columns.join(", "), 
                                         partitioning.partitions.len()));
                },
                PartitionType::Key => {
                    ddl.push_str(&format!("KEY ({}) PARTITIONS {}\n", 
                                         partitioning.partition_columns.join(", "), 
                                         partitioning.partitions.len()));
                },
            }
            
            if matches!(partitioning.partition_type, PartitionType::Range | PartitionType::List) {
                for (i, partition) in partitioning.partitions.iter().enumerate() {
                    if i > 0 {
                        ddl.push_str(",\n");
                    }
                    ddl.push_str(&format!("  PARTITION {} VALUES LESS THAN ({}) TABLESPACE {}", 
                                         partition.name, partition.value, partition.tablespace));
                }
                ddl.push_str("\n);\n\n");
            }
        }
        
        ddl
    }
    
    pub fn estimate_storage_requirements(&self, table_stats: &HashMap<String, TableStats>) -> StorageEstimate {
        let mut estimate = StorageEstimate::new();
        
        for (table_name, stats) in table_stats {
            let mut table_size = 0u64;
            
            // 计算行大小
            for column in &stats.columns {
                let column_size = match column.data_type {
                    DataType::Integer => 4,
                    DataType::BigInt => 8,
                    DataType::Float => 4,
                    DataType::Double => 8,
                    DataType::Decimal(_, _) => 8,
                    DataType::Char(length) => length as u64,
                    DataType::Varchar(length) => length as u64 + 2, // 长度前缀
                    DataType::Text => 65535,
                    DataType::Boolean => 1,
                    DataType::Date => 3,
                    DataType::DateTime => 8,
                    DataType::Timestamp => 4,
                    DataType::Blob => 65535,
                };
                table_size += column_size;
            }
            
            // 添加行开销
            table_size += 20; // 行头开销
            
            // 计算总表大小
            let total_table_size = table_size * stats.row_count;
            
            // 添加索引大小
            let index_size = total_table_size * 20 / 100; // 假设索引占20%
            
            estimate.total_size += total_table_size + index_size;
            estimate.table_sizes.insert(table_name.clone(), total_table_size + index_size);
        }
        
        estimate
    }
}

#[derive(Debug, Clone)]
pub enum AccessPattern {
    ReadHeavy,
    WriteHeavy,
    Mixed,
}

#[derive(Debug, Clone)]
pub struct TableStats {
    pub row_count: u64,
    pub columns: Vec<Column>,
}

#[derive(Debug, Clone)]
pub struct StorageEstimate {
    pub total_size: u64,
    pub table_sizes: HashMap<String, u64>,
}

impl StorageEstimate {
    pub fn new() -> Self {
        StorageEstimate {
            total_size: 0,
            table_sizes: HashMap::new(),
        }
    }
    
    pub fn print_report(&self) {
        println!("=== 存储需求估算 ===");
        println!("总存储需求: {} bytes ({:.2} MB)", 
                self.total_size, self.total_size as f64 / (1024.0 * 1024.0));
        
        for (table_name, size) in &self.table_sizes {
            println!("表 {}: {} bytes ({:.2} MB)", 
                    table_name, size, *size as f64 / (1024.0 * 1024.0));
        }
    }
}
```

## 5. 相关理论与交叉引用

- [数据模型理论](../01_Data_Models/01_Data_Models_Theory.md)
- [查询优化理论](../03_Query_Optimization/01_Query_Optimization_Theory.md)
- [事务管理理论](../04_Transaction_Management/01_Transaction_Management_Theory.md)

## 6. 参考文献

1. Connolly, T. M., & Begg, C. E. (2014). Database Systems: A Practical Approach to Design, Implementation, and Management. Pearson.
2. Elmasri, R., & Navathe, S. B. (2015). Fundamentals of Database Systems. Pearson.
3. Silberschatz, A., Korth, H. F., & Sudarshan, S. (2019). Database System Concepts. McGraw-Hill.

---

**最后更新**: 2024年12月21日  
**维护者**: AI助手  
**版本**: v1.0

## 批判性分析

- 多元理论视角：
  - 语义到结构：需求语义→概念模型（ER/概念类图）→逻辑模型（关系/文档/图/列族）→物理模型（分区/索引/存储布局）的分层映射，应与一致性/事务/查询/性能协同设计。
  - 规范化与反规范化：以函数依赖/范式控制冗余与更新代价；结合查询特征与存储/网络成本进行反规范化与物化视图。
- 局限性分析：
  - 静态设计与动态负载：静态模式与动态/多变工作负载背离；跨业务团队的语义漂移与重复建模。
  - 多模数据：跨模型（关系/文档/图/时序）与跨引擎设计一致性与可演进性挑战。
- 争议与分歧：
  - 单一真相源 vs 多源协同；强一致架构 vs 高可用与弹性优先。
- 应用前景：
  - 架构即数据：以元模型/元数据驱动的设计—生成—校验闭环；与可观测性/数据治理/质量门禁联动。
- 改进建议：
  - 证据与基线：输出依赖/范式/查询画像证据；维护跨引擎模式对照与演进策略；将性能与一致性目标纳入设计验收。
