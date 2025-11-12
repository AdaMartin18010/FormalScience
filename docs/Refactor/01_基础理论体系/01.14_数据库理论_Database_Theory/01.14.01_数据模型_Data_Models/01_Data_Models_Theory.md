# 12.1.1 数据模型理论

## 目录

- [12.1.1 数据模型理论](#1211-数据模型理论)
  - [目录](#目录)
  - [📋 概述](#-概述)
  - [1. 基本概念](#1-基本概念)
    - [1.1 数据模型定义](#11-数据模型定义)
    - [1.2 数据模型分类](#12-数据模型分类)
  - [2. 形式化定义](#2-形式化定义)
    - [2.1 关系模型](#21-关系模型)
    - [2.2 实体关系模型](#22-实体关系模型)
    - [2.3 规范化理论](#23-规范化理论)
  - [3. 定理与证明](#3-定理与证明)
    - [3.1 函数依赖传递性定理](#31-函数依赖传递性定理)
    - [3.2 无损连接分解定理](#32-无损连接分解定理)
  - [4. Rust代码实现](#4-rust代码实现)
    - [4.1 关系模型实现](#41-关系模型实现)
    - [4.2 实体关系模型实现](#42-实体关系模型实现)
    - [4.3 规范化算法实现](#43-规范化算法实现)
  - [5. 相关理论与交叉引用](#5-相关理论与交叉引用)
  - [6. 参考文献](#6-参考文献)
  - [批判性分析](#批判性分析)

## 📋 概述

数据模型理论研究数据库中数据的组织、结构和关系表示方法。
该理论涵盖关系模型、实体关系模型、对象模型、文档模型等核心概念，为数据库设计提供理论基础。

## 1. 基本概念

### 1.1 数据模型定义

**定义 1.1**（数据模型）
数据模型是描述数据结构、数据关系和数据约束的抽象概念集合。

### 1.2 数据模型分类

| 模型类型     | 英文名称         | 描述                         | 典型代表         |
|--------------|------------------|------------------------------|------------------|
| 关系模型     | Relational       | 基于表的数据组织             | SQL, MySQL       |
| 实体关系     | Entity-Relation  | 实体和关系的图形表示         | ER图, UML        |
| 对象模型     | Object-Oriented  | 面向对象的数据组织           | OODB, JPA        |
| 文档模型     | Document         | 基于文档的数据组织           | MongoDB, CouchDB |
| 图模型       | Graph            | 基于图的数据组织             | Neo4j, ArangoDB  |

## 2. 形式化定义

### 2.1 关系模型

**定义 2.1**（关系模型）
关系模型是基于数学关系理论的数据模型，数据以表格形式组织。

### 2.2 实体关系模型

**定义 2.2**（实体关系模型）
实体关系模型是描述实体、属性和实体间关系的概念模型。

### 2.3 规范化理论

**定义 2.3**（规范化）
规范化是消除数据冗余和异常的过程，通过分解关系表实现。

## 3. 定理与证明

### 3.1 函数依赖传递性定理

**定理 3.1**（函数依赖传递性）
若 $X \rightarrow Y$ 且 $Y \rightarrow Z$，则 $X \rightarrow Z$。

**证明**：
设 $t_1, t_2$ 是关系中的任意两个元组，若 $t_1[X] = t_2[X]$，则 $t_1[Y] = t_2[Y]$，进而 $t_1[Z] = t_2[Z]$。□

### 3.2 无损连接分解定理

**定理 3.2**（无损连接分解）
关系 $R$ 分解为 $R_1$ 和 $R_2$ 是无损的，当且仅当 $R_1 \cap R_2 \rightarrow R_1$ 或 $R_1 \cap R_2 \rightarrow R_2$。

**证明**：
若 $R_1 \cap R_2 \rightarrow R_1$，则 $R_1 \bowtie R_2 = R$，分解无损。□

## 4. Rust代码实现

### 4.1 关系模型实现

```rust
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone)]
pub struct Attribute {
    pub name: String,
    pub data_type: DataType,
    pub is_primary_key: bool,
    pub is_nullable: bool,
    pub default_value: Option<String>,
}

#[derive(Debug, Clone)]
pub enum DataType {
    Integer,
    Float,
    String(usize),
    Boolean,
    Date,
    Timestamp,
}

#[derive(Debug, Clone)]
pub struct Relation {
    pub name: String,
    pub attributes: Vec<Attribute>,
    pub tuples: Vec<Tuple>,
    pub primary_key: Vec<String>,
    pub foreign_keys: Vec<ForeignKey>,
}

#[derive(Debug, Clone)]
pub struct Tuple {
    pub values: HashMap<String, String>,
}

#[derive(Debug, Clone)]
pub struct ForeignKey {
    pub attribute: String,
    pub referenced_table: String,
    pub referenced_attribute: String,
}

impl Relation {
    pub fn new(name: String) -> Self {
        Relation {
            name,
            attributes: Vec::new(),
            tuples: Vec::new(),
            primary_key: Vec::new(),
            foreign_keys: Vec::new(),
        }
    }

    pub fn add_attribute(&mut self, attribute: Attribute) {
        if attribute.is_primary_key {
            self.primary_key.push(attribute.name.clone());
        }
        self.attributes.push(attribute);
    }

    pub fn insert_tuple(&mut self, values: HashMap<String, String>) -> Result<(), String> {
        // 验证主键约束
        if !self.primary_key.is_empty() {
            let mut key_values = Vec::new();
            for key in &self.primary_key {
                if let Some(value) = values.get(key) {
                    key_values.push((key.clone(), value.clone()));
                } else {
                    return Err(format!("Primary key attribute {} is missing", key));
                }
            }

            // 检查主键唯一性
            for tuple in &self.tuples {
                let mut existing_key_values = Vec::new();
                for key in &self.primary_key {
                    if let Some(value) = tuple.values.get(key) {
                        existing_key_values.push((key.clone(), value.clone()));
                    }
                }

                if key_values == existing_key_values {
                    return Err("Primary key constraint violation".to_string());
                }
            }
        }

        // 验证数据类型
        for attribute in &self.attributes {
            if let Some(value) = values.get(&attribute.name) {
                if !self.validate_data_type(value, &attribute.data_type) {
                    return Err(format!("Invalid data type for attribute {}", attribute.name));
                }
            } else if !attribute.is_nullable && attribute.default_value.is_none() {
                return Err(format!("Non-nullable attribute {} is missing", attribute.name));
            }
        }

        let tuple = Tuple { values };
        self.tuples.push(tuple);
        Ok(())
    }

    pub fn select(&self, condition: Option<Box<dyn Fn(&Tuple) -> bool>>) -> Vec<Tuple> {
        if let Some(predicate) = condition {
            self.tuples.iter()
                .filter(|tuple| predicate(tuple))
                .cloned()
                .collect()
        } else {
            self.tuples.clone()
        }
    }

    pub fn project(&self, attributes: &[String]) -> Relation {
        let mut projected_relation = Relation::new(format!("{}_projected", self.name));

        // 添加投影的属性
        for attr_name in attributes {
            if let Some(attr) = self.attributes.iter().find(|a| &a.name == attr_name) {
                projected_relation.add_attribute(attr.clone());
            }
        }

        // 投影元组
        for tuple in &self.tuples {
            let mut projected_values = HashMap::new();
            for attr_name in attributes {
                if let Some(value) = tuple.values.get(attr_name) {
                    projected_values.insert(attr_name.clone(), value.clone());
                }
            }
            let _ = projected_relation.insert_tuple(projected_values);
        }

        projected_relation
    }

    pub fn join(&self, other: &Relation, condition: Box<dyn Fn(&Tuple, &Tuple) -> bool>) -> Relation {
        let mut joined_relation = Relation::new(format!("{}_join_{}", self.name, other.name));

        // 合并属性
        for attr in &self.attributes {
            joined_relation.add_attribute(attr.clone());
        }
        for attr in &other.attributes {
            joined_relation.add_attribute(attr.clone());
        }

        // 执行连接
        for tuple1 in &self.tuples {
            for tuple2 in &other.tuples {
                if condition(tuple1, tuple2) {
                    let mut joined_values = tuple1.values.clone();
                    joined_values.extend(tuple2.values.clone());
                    let _ = joined_relation.insert_tuple(joined_values);
                }
            }
        }

        joined_relation
    }

    fn validate_data_type(&self, value: &str, data_type: &DataType) -> bool {
        match data_type {
            DataType::Integer => value.parse::<i64>().is_ok(),
            DataType::Float => value.parse::<f64>().is_ok(),
            DataType::String(max_length) => value.len() <= *max_length,
            DataType::Boolean => value == "true" || value == "false",
            DataType::Date => {
                // 简化的日期验证
                value.len() == 10 && value.contains('-')
            },
            DataType::Timestamp => {
                // 简化的时间戳验证
                value.len() >= 19 && value.contains('-') && value.contains(':')
            },
        }
    }

    pub fn get_cardinality(&self) -> usize {
        self.tuples.len()
    }

    pub fn get_degree(&self) -> usize {
        self.attributes.len()
    }
}
```

### 4.2 实体关系模型实现

```rust
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct Entity {
    pub name: String,
    pub attributes: Vec<EntityAttribute>,
    pub primary_key: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct EntityAttribute {
    pub name: String,
    pub data_type: DataType,
    pub is_primary_key: bool,
    pub is_nullable: bool,
    pub is_derived: bool,
}

#[derive(Debug, Clone)]
pub struct Relationship {
    pub name: String,
    pub entities: Vec<String>,
    pub cardinality: Vec<Cardinality>,
    pub attributes: Vec<EntityAttribute>,
}

#[derive(Debug, Clone)]
pub enum Cardinality {
    OneToOne,
    OneToMany,
    ManyToOne,
    ManyToMany,
}

#[derive(Debug, Clone)]
pub struct ERModel {
    pub entities: HashMap<String, Entity>,
    pub relationships: HashMap<String, Relationship>,
}

impl ERModel {
    pub fn new() -> Self {
        ERModel {
            entities: HashMap::new(),
            relationships: HashMap::new(),
        }
    }

    pub fn add_entity(&mut self, entity: Entity) {
        self.entities.insert(entity.name.clone(), entity);
    }

    pub fn add_relationship(&mut self, relationship: Relationship) {
        self.relationships.insert(relationship.name.clone(), relationship);
    }

    pub fn get_entity(&self, name: &str) -> Option<&Entity> {
        self.entities.get(name)
    }

    pub fn get_relationship(&self, name: &str) -> Option<&Relationship> {
        self.relationships.get(name)
    }

    pub fn to_relational_model(&self) -> Vec<Relation> {
        let mut relations = Vec::new();

        // 转换实体为关系
        for entity in self.entities.values() {
            let mut relation = Relation::new(entity.name.clone());

            for attr in &entity.attributes {
                let attribute = Attribute {
                    name: attr.name.clone(),
                    data_type: attr.data_type.clone(),
                    is_primary_key: attr.is_primary_key,
                    is_nullable: attr.is_nullable,
                    default_value: None,
                };
                relation.add_attribute(attribute);
            }

            relations.push(relation);
        }

        // 转换关系为关系表
        for relationship in self.relationships.values() {
            if relationship.entities.len() == 2 {
                let entity1 = &relationship.entities[0];
                let entity2 = &relationship.entities[1];
                let cardinality1 = &relationship.cardinality[0];
                let cardinality2 = &relationship.cardinality[1];

                match (cardinality1, cardinality2) {
                    (Cardinality::ManyToMany, Cardinality::ManyToMany) => {
                        // 创建连接表
                        let mut relation = Relation::new(format!("{}_relation", relationship.name));

                        // 添加外键
                        if let Some(entity1_obj) = self.entities.get(entity1) {
                            for pk in &entity1_obj.primary_key {
                                let attribute = Attribute {
                                    name: format!("{}_id", entity1),
                                    data_type: DataType::Integer,
                                    is_primary_key: true,
                                    is_nullable: false,
                                    default_value: None,
                                };
                                relation.add_attribute(attribute);
                            }
                        }

                        if let Some(entity2_obj) = self.entities.get(entity2) {
                            for pk in &entity2_obj.primary_key {
                                let attribute = Attribute {
                                    name: format!("{}_id", entity2),
                                    data_type: DataType::Integer,
                                    is_primary_key: true,
                                    is_nullable: false,
                                    default_value: None,
                                };
                                relation.add_attribute(attribute);
                            }
                        }

                        // 添加关系属性
                        for attr in &relationship.attributes {
                            let attribute = Attribute {
                                name: attr.name.clone(),
                                data_type: attr.data_type.clone(),
                                is_primary_key: false,
                                is_nullable: attr.is_nullable,
                                default_value: None,
                            };
                            relation.add_attribute(attribute);
                        }

                        relations.push(relation);
                    },
                    (Cardinality::OneToMany, Cardinality::ManyToOne) => {
                        // 在"多"的一方添加外键
                        if let Some(entity2_obj) = self.entities.get(entity2) {
                            if let Some(relation) = relations.iter_mut().find(|r| r.name == *entity2) {
                                for pk in &entity1_obj.primary_key {
                                    let attribute = Attribute {
                                        name: format!("{}_id", entity1),
                                        data_type: DataType::Integer,
                                        is_primary_key: false,
                                        is_nullable: false,
                                        default_value: None,
                                    };
                                    relation.add_attribute(attribute);
                                }
                            }
                        }
                    },
                    _ => {
                        // 其他情况类似处理
                    }
                }
            }
        }

        relations
    }

    pub fn validate_model(&self) -> Vec<String> {
        let mut errors = Vec::new();

        // 检查实体名称唯一性
        let mut entity_names = HashSet::new();
        for entity in self.entities.values() {
            if !entity_names.insert(&entity.name) {
                errors.push(format!("Duplicate entity name: {}", entity.name));
            }
        }

        // 检查关系中的实体是否存在
        for relationship in self.relationships.values() {
            for entity_name in &relationship.entities {
                if !self.entities.contains_key(entity_name) {
                    errors.push(format!("Entity {} referenced in relationship {} does not exist",
                                      entity_name, relationship.name));
                }
            }
        }

        // 检查主键约束
        for entity in self.entities.values() {
            if entity.primary_key.is_empty() {
                errors.push(format!("Entity {} has no primary key", entity.name));
            }

            for pk in &entity.primary_key {
                if !entity.attributes.iter().any(|attr| &attr.name == pk) {
                    errors.push(format!("Primary key {} in entity {} does not exist", pk, entity.name));
                }
            }
        }

        errors
    }
}
```

### 4.3 规范化算法实现

```rust
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone)]
pub struct FunctionalDependency {
    pub determinant: Vec<String>,
    pub dependent: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct NormalizationResult {
    pub relations: Vec<Relation>,
    pub dependencies: Vec<FunctionalDependency>,
    pub normal_form: NormalForm,
}

#[derive(Debug, Clone)]
pub enum NormalForm {
    FirstNormalForm,
    SecondNormalForm,
    ThirdNormalForm,
    BoyceCoddNormalForm,
}

impl Relation {
    pub fn normalize(&self, dependencies: &[FunctionalDependency]) -> NormalizationResult {
        let mut result = NormalizationResult {
            relations: Vec::new(),
            dependencies: dependencies.to_vec(),
            normal_form: NormalForm::FirstNormalForm,
        };

        // 检查1NF
        if self.is_first_normal_form() {
            result.normal_form = NormalForm::FirstNormalForm;

            // 检查2NF
            if self.is_second_normal_form(dependencies) {
                result.normal_form = NormalForm::SecondNormalForm;

                // 检查3NF
                if self.is_third_normal_form(dependencies) {
                    result.normal_form = NormalForm::ThirdNormalForm;

                    // 检查BCNF
                    if self.is_boyce_codd_normal_form(dependencies) {
                        result.normal_form = NormalForm::BoyceCoddNormalForm;
                    } else {
                        // 分解为BCNF
                        result.relations = self.decompose_to_bcnf(dependencies);
                    }
                } else {
                    // 分解为3NF
                    result.relations = self.decompose_to_3nf(dependencies);
                }
            } else {
                // 分解为2NF
                result.relations = self.decompose_to_2nf(dependencies);
            }
        }

        result
    }

    fn is_first_normal_form(&self) -> bool {
        // 检查是否有重复组
        for tuple in &self.tuples {
            for value in tuple.values.values() {
                if value.contains(',') || value.contains(';') {
                    return false; // 可能包含重复组
                }
            }
        }
        true
    }

    fn is_second_normal_form(&self, dependencies: &[FunctionalDependency]) -> bool {
        if self.primary_key.len() <= 1 {
            return true; // 单属性主键自动满足2NF
        }

        // 检查是否有部分函数依赖
        for dependency in dependencies {
            if dependency.dependent.len() == 1 {
                let dependent = &dependency.dependent[0];

                // 检查依赖属性是否在主键中
                if !self.primary_key.contains(dependent) {
                    // 检查是否部分依赖
                    for key_attr in &self.primary_key {
                        if !dependency.determinant.contains(key_attr) {
                            return false; // 存在部分依赖
                        }
                    }
                }
            }
        }
        true
    }

    fn is_third_normal_form(&self, dependencies: &[FunctionalDependency]) -> bool {
        for dependency in dependencies {
            if dependency.dependent.len() == 1 {
                let dependent = &dependency.dependent[0];

                // 检查是否是非主属性
                if !self.primary_key.contains(dependent) {
                    // 检查决定因素是否是超键
                    if !self.is_superkey(&dependency.determinant) {
                        return false; // 存在传递依赖
                    }
                }
            }
        }
        true
    }

    fn is_boyce_codd_normal_form(&self, dependencies: &[FunctionalDependency]) -> bool {
        for dependency in dependencies {
            if !self.is_superkey(&dependency.determinant) {
                return false; // 存在非平凡函数依赖，决定因素不是超键
            }
        }
        true
    }

    fn is_superkey(&self, attributes: &[String]) -> bool {
        let attribute_set: HashSet<_> = attributes.iter().collect();
        let primary_key_set: HashSet<_> = self.primary_key.iter().collect();
        primary_key_set.is_subset(&attribute_set)
    }

    fn decompose_to_2nf(&self, dependencies: &[FunctionalDependency]) -> Vec<Relation> {
        let mut relations = Vec::new();

        // 创建主关系
        let mut main_relation = self.clone();
        relations.push(main_relation);

        // 处理部分依赖
        for dependency in dependencies {
            if dependency.dependent.len() == 1 {
                let dependent = &dependency.dependent[0];

                if !self.primary_key.contains(dependent) {
                    // 检查是否部分依赖
                    let mut is_partial = false;
                    for key_attr in &self.primary_key {
                        if !dependency.determinant.contains(key_attr) {
                            is_partial = true;
                            break;
                        }
                    }

                    if is_partial {
                        // 创建新关系
                        let mut new_relation = Relation::new(format!("{}_partial", self.name));

                        // 添加决定因素和依赖属性
                        for attr_name in &dependency.determinant {
                            if let Some(attr) = self.attributes.iter().find(|a| &a.name == attr_name) {
                                new_relation.add_attribute(attr.clone());
                            }
                        }

                        for attr_name in &dependency.dependent {
                            if let Some(attr) = self.attributes.iter().find(|a| &a.name == attr_name) {
                                new_relation.add_attribute(attr.clone());
                            }
                        }

                        relations.push(new_relation);
                    }
                }
            }
        }

        relations
    }

    fn decompose_to_3nf(&self, dependencies: &[FunctionalDependency]) -> Vec<Relation> {
        let mut relations = Vec::new();

        // 创建主关系
        let mut main_relation = self.clone();
        relations.push(main_relation);

        // 处理传递依赖
        for dependency in dependencies {
            if dependency.dependent.len() == 1 {
                let dependent = &dependency.dependent[0];

                if !self.primary_key.contains(dependent) && !self.is_superkey(&dependency.determinant) {
                    // 创建新关系
                    let mut new_relation = Relation::new(format!("{}_transitive", self.name));

                    // 添加决定因素和依赖属性
                    for attr_name in &dependency.determinant {
                        if let Some(attr) = self.attributes.iter().find(|a| &a.name == attr_name) {
                            new_relation.add_attribute(attr.clone());
                        }
                    }

                    for attr_name in &dependency.dependent {
                        if let Some(attr) = self.attributes.iter().find(|a| &a.name == attr_name) {
                            new_relation.add_attribute(attr.clone());
                        }
                    }

                    relations.push(new_relation);
                }
            }
        }

        relations
    }

    fn decompose_to_bcnf(&self, dependencies: &[FunctionalDependency]) -> Vec<Relation> {
        let mut relations = Vec::new();

        // 创建主关系
        let mut main_relation = self.clone();
        relations.push(main_relation);

        // 处理BCNF违反
        for dependency in dependencies {
            if !self.is_superkey(&dependency.determinant) {
                // 创建新关系
                let mut new_relation = Relation::new(format!("{}_bcnf", self.name));

                // 添加决定因素和依赖属性
                for attr_name in &dependency.determinant {
                    if let Some(attr) = self.attributes.iter().find(|a| &a.name == attr_name) {
                        new_relation.add_attribute(attr.clone());
                    }
                }

                for attr_name in &dependency.dependent {
                    if let Some(attr) = self.attributes.iter().find(|a| &a.name == attr_name) {
                        new_relation.add_attribute(attr.clone());
                    }
                }

                relations.push(new_relation);
            }
        }

        relations
    }
}
```

## 5. 相关理论与交叉引用

- [数据库设计理论](../02_Database_Design/01_Database_Design_Theory.md)
- [查询优化理论](../03_Query_Optimization/01_Query_Optimization_Theory.md)
- [事务管理理论](../04_Transaction_Management/01_Transaction_Management_Theory.md)

## 6. 参考文献

1. Codd, E. F. (1970). A Relational Model of Data for Large Shared Data Banks. Communications of the ACM.
2. Chen, P. P. (1976). The Entity-Relationship Model—Toward a Unified View of Data. ACM Transactions on Database Systems.
3. Date, C. J. (2019). An Introduction to Database Systems. Pearson.

---

**最后更新**: 2024年12月21日
**维护者**: AI助手
**版本**: v1.0

## 批判性分析

- 多元理论视角：
  - 概念—逻辑—物理：ER/概念类图→关系/文档/图/列族→分区/副本/布局，分别承载语义、约束与实现；应与事务/查询/性能协同。
- 局限性分析：
  - 模型碎片化：多模/多引擎带来一致性与治理挑战；跨模型查询与优化缺乏统一抽象。
  - 语义漂移：概念模型与实现模型长期演进脱节。
- 争议与分歧：
  - 单引擎多模型 vs 多引擎专精；强约束 vs 弹性演进。
- 应用前景：
  - 统一中间表示（代数/IR）支持跨模型优化与验证；与数据血缘/质量/合规联动。
- 改进建议：
  - 元模型与证据：维护模型—约束—查询—物理设计的可追溯证据；提供跨模型映射与演进策略。
