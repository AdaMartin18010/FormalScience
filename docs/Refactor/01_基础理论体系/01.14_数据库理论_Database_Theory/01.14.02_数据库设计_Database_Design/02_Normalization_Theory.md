# 02 数据库规范化理论

## 目录

- [02 数据库规范化理论](#02-数据库规范化理论)
  - [目录](#目录)
  - [📋 概述](#-概述)
  - [1. 基本概念](#1-基本概念)
    - [1.1 规范化定义](#11-规范化定义)
    - [1.2 范式分类](#12-范式分类)
  - [2. 形式化定义](#2-形式化定义)
    - [2.1 函数依赖](#21-函数依赖)
    - [2.2 多值依赖](#22-多值依赖)
    - [2.3 连接依赖](#23-连接依赖)
  - [3. 定理与证明](#3-定理与证明)
    - [3.1 无损连接分解定理](#31-无损连接分解定理)
    - [3.2 依赖保持分解定理](#32-依赖保持分解定理)
  - [4. Rust代码实现](#4-rust代码实现)
    - [4.1 函数依赖分析](#41-函数依赖分析)
    - [4.2 范式检查器](#42-范式检查器)
    - [4.3 规范化算法](#43-规范化算法)
  - [5. 相关理论与交叉引用](#5-相关理论与交叉引用)
  - [6. 参考文献](#6-参考文献)
  - [批判性分析](#批判性分析)

## 📋 概述

数据库规范化理论研究关系数据库的设计原则、范式理论和分解方法。
该理论涵盖函数依赖、多值依赖、范式分解等核心概念，为数据库设计提供理论基础。

## 1. 基本概念

### 1.1 规范化定义

**定义 1.1**（数据库规范化）
数据库规范化是通过分解关系模式来消除数据冗余和异常的过程。

### 1.2 范式分类

| 范式类型     | 英文名称         | 描述                         | 消除异常         |
|--------------|------------------|------------------------------|------------------|
| 第一范式     | 1NF              | 每个属性都是原子的           | 重复组           |
| 第二范式     | 2NF              | 消除部分函数依赖             | 部分依赖         |
| 第三范式     | 3NF              | 消除传递函数依赖             | 传递依赖         |
| BCNF         | Boyce-Codd NF    | 消除所有函数依赖             | 所有依赖         |
| 第四范式     | 4NF              | 消除多值依赖                 | 多值依赖         |
| 第五范式     | 5NF              | 消除连接依赖                 | 连接依赖         |

## 2. 形式化定义

### 2.1 函数依赖

**定义 2.1**（函数依赖）
如果关系R中，对于任意两个元组t₁和t₂，若t₁[X] = t₂[X]，则t₁[Y] = t₂[Y]，则称X函数决定Y，记作X → Y。

**定义 2.2**（完全函数依赖）
如果X → Y，且X的任意真子集X'都不满足X' → Y，则称Y完全函数依赖于X。

**定义 2.3**（部分函数依赖）
如果X → Y，但存在X的真子集X'满足X' → Y，则称Y部分函数依赖于X。

### 2.2 多值依赖

**定义 2.4**（多值依赖）
如果关系R中，对于任意两个元组t₁和t₂，若t₁[X] = t₂[X]，则存在元组t₃和t₄，使得t₃[X] = t₄[X] = t₁[X]，且t₃[Y] = t₁[Y]，t₃[Z] = t₂[Z]，t₄[Y] = t₂[Y]，t₄[Z] = t₁[Z]，则称X多值决定Y，记作X →→ Y。

### 2.3 连接依赖

**定义 2.5**（连接依赖）
如果关系R可以无损地分解为R₁, R₂, ..., Rₙ，则称R满足连接依赖。

## 3. 定理与证明

### 3.1 无损连接分解定理

**定理 3.1**（无损连接分解）
关系R分解为R₁和R₂是无损的，当且仅当R₁ ∩ R₂ → R₁ 或 R₁ ∩ R₂ → R₂。

**证明**：
设R₁ ∩ R₂ = X，若X → R₁，则对于任意元组t₁ ∈ R₁和t₂ ∈ R₂，若t₁[X] = t₂[X]，则t₁可以通过X确定。
因此，R₁ ⋈ R₂ = R，分解无损。□

### 3.2 依赖保持分解定理

**定理 3.2**（依赖保持分解）
如果分解R₁, R₂, ..., Rₙ保持函数依赖集F，则对于F中的每个依赖X → Y，存在Rᵢ使得X ∪ Y ⊆ Rᵢ。

**证明**：
如果X → Y ∈ F，且X ∪ Y ⊆ Rᵢ，则Rᵢ中保持了这个依赖。
因此，整个分解保持了所有函数依赖。□

## 4. Rust代码实现

### 4.1 函数依赖分析

```rust
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone)]
pub struct FunctionalDependency {
    pub determinant: HashSet<String>,
    pub dependent: HashSet<String>,
}

#[derive(Debug)]
pub struct DependencyAnalyzer {
    pub dependencies: Vec<FunctionalDependency>,
    pub attributes: HashSet<String>,
}

impl DependencyAnalyzer {
    pub fn new() -> Self {
        DependencyAnalyzer {
            dependencies: Vec::new(),
            attributes: HashSet::new(),
        }
    }

    pub fn add_dependency(&mut self, determinant: Vec<String>, dependent: Vec<String>) {
        let fd = FunctionalDependency {
            determinant: determinant.into_iter().collect(),
            dependent: dependent.into_iter().collect(),
        };

        // 添加属性到属性集
        for attr in &fd.determinant {
            self.attributes.insert(attr.clone());
        }
        for attr in &fd.dependent {
            self.attributes.insert(attr.clone());
        }

        self.dependencies.push(fd);
    }

    pub fn compute_closure(&self, attributes: &HashSet<String>) -> HashSet<String> {
        let mut closure = attributes.clone();
        let mut changed = true;

        while changed {
            changed = false;
            for dependency in &self.dependencies {
                if dependency.determinant.is_subset(&closure) {
                    for attr in &dependency.dependent {
                        if !closure.contains(attr) {
                            closure.insert(attr.clone());
                            changed = true;
                        }
                    }
                }
            }
        }

        closure
    }

    pub fn find_candidate_keys(&self) -> Vec<HashSet<String>> {
        let mut candidate_keys = Vec::new();
        let all_attributes = &self.attributes;

        // 生成所有可能的属性子集
        let subsets = self.generate_subsets(all_attributes);

        for subset in subsets {
            let closure = self.compute_closure(&subset);
            if closure == *all_attributes {
                // 检查是否为最小超键
                let mut is_minimal = true;
                for smaller_subset in self.generate_subsets(&subset) {
                    if smaller_subset != subset {
                        let smaller_closure = self.compute_closure(&smaller_subset);
                        if smaller_closure == *all_attributes {
                            is_minimal = false;
                            break;
                        }
                    }
                }

                if is_minimal {
                    candidate_keys.push(subset);
                }
            }
        }

        candidate_keys
    }

    fn generate_subsets(&self, attributes: &HashSet<String>) -> Vec<HashSet<String>> {
        let mut subsets = Vec::new();
        let attributes_vec: Vec<String> = attributes.iter().cloned().collect();
        let n = attributes_vec.len();

        for i in 0..(1 << n) {
            let mut subset = HashSet::new();
            for j in 0..n {
                if (i >> j) & 1 == 1 {
                    subset.insert(attributes_vec[j].clone());
                }
            }
            subsets.push(subset);
        }

        subsets
    }
}
```

### 4.2 范式检查器

```rust
#[derive(Debug)]
pub struct NormalFormChecker {
    pub analyzer: DependencyAnalyzer,
}

impl NormalFormChecker {
    pub fn new(analyzer: DependencyAnalyzer) -> Self {
        NormalFormChecker { analyzer }
    }

    pub fn check_1nf(&self, relation: &Relation) -> bool {
        // 检查每个属性是否为原子值
        for tuple in &relation.tuples {
            for (_, value) in &tuple.values {
                if let Value::List(_) = value {
                    return false; // 包含重复组，不满足1NF
                }
            }
        }
        true
    }

    pub fn check_2nf(&self, relation: &Relation) -> bool {
        let candidate_keys = self.analyzer.find_candidate_keys();

        for dependency in &self.analyzer.dependencies {
            // 检查是否存在部分函数依赖
            for candidate_key in &candidate_keys {
                if dependency.determinant.is_subset(candidate_key) &&
                   dependency.determinant != *candidate_key {
                    // 存在部分函数依赖，不满足2NF
                    return false;
                }
            }
        }
        true
    }

    pub fn check_3nf(&self, relation: &Relation) -> bool {
        let candidate_keys = self.analyzer.find_candidate_keys();

        for dependency in &self.analyzer.dependencies {
            // 检查是否存在传递函数依赖
            if !self.is_superkey(&dependency.determinant, &candidate_keys) {
                for attr in &dependency.dependent {
                    if !self.is_prime_attribute(attr, &candidate_keys) {
                        return false; // 存在传递函数依赖，不满足3NF
                    }
                }
            }
        }
        true
    }

    pub fn check_bcnf(&self, relation: &Relation) -> bool {
        for dependency in &self.analyzer.dependencies {
            // 检查每个函数依赖的决定因素是否为超键
            if !self.is_superkey(&dependency.determinant, &self.analyzer.find_candidate_keys()) {
                return false; // 不满足BCNF
            }
        }
        true
    }

    fn is_superkey(&self, attributes: &HashSet<String>, candidate_keys: &[HashSet<String>]) -> bool {
        for candidate_key in candidate_keys {
            if attributes.is_superset(candidate_key) {
                return true;
            }
        }
        false
    }

    fn is_prime_attribute(&self, attribute: &str, candidate_keys: &[HashSet<String>]) -> bool {
        for candidate_key in candidate_keys {
            if candidate_key.contains(attribute) {
                return true;
            }
        }
        false
    }
}

#[derive(Debug)]
pub struct Relation {
    pub name: String,
    pub attributes: Vec<String>,
    pub tuples: Vec<Tuple>,
}

#[derive(Debug)]
pub struct Tuple {
    pub values: HashMap<String, Value>,
}

#[derive(Debug)]
pub enum Value {
    String(String),
    Integer(i32),
    List(Vec<String>),
}
```

### 4.3 规范化算法

```rust
#[derive(Debug)]
pub struct NormalizationAlgorithm {
    pub analyzer: DependencyAnalyzer,
}

impl NormalizationAlgorithm {
    pub fn new(analyzer: DependencyAnalyzer) -> Self {
        NormalizationAlgorithm { analyzer }
    }

    pub fn decompose_to_3nf(&self, relation: &Relation) -> Vec<Relation> {
        let mut decomposed_relations = Vec::new();
        let mut remaining_attributes = relation.attributes.clone();
        let mut used_dependencies = HashSet::new();

        // 步骤1：为每个函数依赖创建关系
        for dependency in &self.analyzer.dependencies {
            if !used_dependencies.contains(&dependency.determinant) {
                let mut new_attributes = dependency.determinant.clone();
                new_attributes.extend(dependency.dependent.clone());

                let new_relation = Relation {
                    name: format!("R_{}", decomposed_relations.len() + 1),
                    attributes: new_attributes.into_iter().collect(),
                    tuples: Vec::new(), // 简化实现，实际需要投影数据
                };

                decomposed_relations.push(new_relation);
                used_dependencies.insert(dependency.determinant.clone());

                // 从剩余属性中移除已使用的属性
                for attr in &dependency.dependent {
                    remaining_attributes.retain(|a| a != attr);
                }
            }
        }

        // 步骤2：如果还有剩余属性，创建包含候选键的关系
        if !remaining_attributes.is_empty() {
            let candidate_keys = self.analyzer.find_candidate_keys();
            if let Some(candidate_key) = candidate_keys.first() {
                let mut key_attributes = candidate_key.clone();
                key_attributes.extend(remaining_attributes);

                let key_relation = Relation {
                    name: format!("R_{}", decomposed_relations.len() + 1),
                    attributes: key_attributes.into_iter().collect(),
                    tuples: Vec::new(),
                };

                decomposed_relations.push(key_relation);
            }
        }

        decomposed_relations
    }

    pub fn decompose_to_bcnf(&self, relation: &Relation) -> Vec<Relation> {
        let mut decomposed_relations = Vec::new();
        let mut current_relation = relation.clone();

        loop {
            let violation = self.find_bcnf_violation(&current_relation);

            match violation {
                Some(dependency) => {
                    // 分解关系
                    let mut r1_attributes = dependency.determinant.clone();
                    r1_attributes.extend(dependency.dependent.clone());

                    let r1 = Relation {
                        name: format!("R_{}", decomposed_relations.len() + 1),
                        attributes: r1_attributes.into_iter().collect(),
                        tuples: Vec::new(),
                    };

                    let r2_attributes: HashSet<String> = current_relation.attributes
                        .iter()
                        .filter(|attr| !dependency.dependent.contains(*attr))
                        .cloned()
                        .collect();

                    let r2 = Relation {
                        name: format!("R_{}", decomposed_relations.len() + 2),
                        attributes: r2_attributes.into_iter().collect(),
                        tuples: Vec::new(),
                    };

                    decomposed_relations.push(r1);
                    current_relation = r2;
                }
                None => {
                    // 没有BCNF违反，添加最终关系
                    if !current_relation.attributes.is_empty() {
                        decomposed_relations.push(current_relation);
                    }
                    break;
                }
            }
        }

        decomposed_relations
    }

    fn find_bcnf_violation(&self, relation: &Relation) -> Option<&FunctionalDependency> {
        let candidate_keys = self.analyzer.find_candidate_keys();

        for dependency in &self.analyzer.dependencies {
            // 检查是否所有属性都在当前关系中
            let all_attrs: HashSet<String> = relation.attributes.iter().cloned().collect();
            let dep_attrs: HashSet<String> = dependency.determinant
                .union(&dependency.dependent)
                .cloned()
                .collect();

            if dep_attrs.is_subset(&all_attrs) {
                // 检查决定因素是否为超键
                if !self.is_superkey(&dependency.determinant, &candidate_keys) {
                    return Some(dependency);
                }
            }
        }

        None
    }

    fn is_superkey(&self, attributes: &HashSet<String>, candidate_keys: &[HashSet<String>]) -> bool {
        for candidate_key in candidate_keys {
            if attributes.is_superset(candidate_key) {
                return true;
            }
        }
        false
    }
}
```

## 5. 相关理论与交叉引用

- **数学基础**：集合论、函数论在规范化中的应用
- **形式语言理论**：关系代数的形式化描述
- **类型理论**：数据库模式的类型安全保证
- **控制论**：数据库设计的约束控制机制
- **人工智能理论**：智能化的模式设计和优化

## 6. 参考文献

1. Codd, E. F. (1970). "A relational model of data for large shared data banks"
2. Codd, E. F. (1971). "Further normalization of the data base relational model"
3. Fagin, R. (1977). "Multivalued dependencies and a new normal form for relational databases"
4. Bernstein, P. A. (1976). "Synthesizing third normal form relations from functional dependencies"

## 批判性分析

- 多元理论视角：
  - 依赖→范式：函数依赖/多值依赖/连接依赖等到 3NF/BCNF/4NF/5NF 的分层消除异常，提升一致性与可维护性。
- 局限性分析：
  - 查询代价：高范式可能导致连接开销激增；真实工作负载常需反规范化与物化视图配合。
  - 异构与演进：跨引擎与多模数据下，传统范式的适配性与演进成本高。
- 争议与分歧：
  - 过度范式化与业务性能诉求冲突；函数依赖的获取与稳定性问题。
- 应用前景：
  - 与查询画像/成本模型/存储特性联动，形成“范式—反范式”的可证据化折中策略。
- 改进建议：
  - 证据与基准：输出依赖挖掘结果、异常示例与性能回归基准；提供反规范化准则与回退方案。
