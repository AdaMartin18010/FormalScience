# 02 数据库索引理论

## 目录

- [02 数据库索引理论](#02-数据库索引理论)
  - [目录](#目录)
  - [📋 概述](#-概述)
  - [1. 基本概念](#1-基本概念)
    - [1.1 数据库索引定义](#11-数据库索引定义)
    - [1.2 索引类型分类](#12-索引类型分类)
  - [2. 形式化定义](#2-形式化定义)
    - [2.1 B树索引](#21-b树索引)
    - [2.2 哈希索引](#22-哈希索引)
    - [2.3 位图索引](#23-位图索引)
  - [3. 定理与证明](#3-定理与证明)
    - [3.1 B树平衡性定理](#31-b树平衡性定理)
    - [3.2 索引选择定理](#32-索引选择定理)
  - [4. Rust代码实现](#4-rust代码实现)
    - [4.1 B树索引实现](#41-b树索引实现)
    - [4.2 哈希索引实现](#42-哈希索引实现)
    - [4.3 索引管理器实现](#43-索引管理器实现)
  - [5. 相关理论与交叉引用](#5-相关理论与交叉引用)
  - [6. 参考文献](#6-参考文献)
  - [批判性分析](#批判性分析)
    - [主要理论观点梳理](#主要理论观点梳理)
    - [理论优势与局限性](#理论优势与局限性)
    - [学科交叉融合](#学科交叉融合)
    - [创新批判与未来展望](#创新批判与未来展望)

## 📋 概述

数据库索引理论研究数据库系统中数据索引的设计、实现和优化方法。
该理论涵盖B树、哈希、位图等核心索引结构，为数据库性能优化提供理论基础。

## 1. 基本概念

### 1.1 数据库索引定义

**定义 1.1**（数据库索引）
数据库索引是提高数据检索速度的数据结构，通过建立键值与存储位置的映射关系实现快速查找。

### 1.2 索引类型分类

| 索引类型     | 英文名称         | 描述                         | 典型应用         |
|--------------|------------------|------------------------------|------------------|
| B树索引      | B-Tree Index     | 平衡树结构，支持范围查询     | 关系数据库       |
| 哈希索引     | Hash Index       | 哈希表结构，支持等值查询     | 内存数据库       |
| 位图索引     | Bitmap Index     | 位向量结构，支持多值查询     | 数据仓库         |
| 全文索引     | Full-Text Index  | 文本搜索索引                 | 搜索引擎         |

## 2. 形式化定义

### 2.1 B树索引

**定义 2.1**（B树）
B树是一种自平衡的树形数据结构，所有叶子节点在同一层。

**定义 2.2**（B树节点）
B树节点包含键值对和子节点指针，满足特定的平衡条件。

### 2.2 哈希索引

**定义 2.3**（哈希索引）
哈希索引使用哈希函数将键值映射到存储位置。

**定义 2.4**（哈希冲突）
哈希冲突是指不同键值映射到相同位置的现象。

### 2.3 位图索引

**定义 2.5**（位图索引）
位图索引使用位向量表示数据的存在性。

**定义 2.6**（位图操作）
位图操作包括AND、OR、NOT等逻辑运算。

## 3. 定理与证明

### 3.1 B树平衡性定理

**定理 3.1**（B树平衡性）
B树的所有叶子节点都在同一层，树的高度为O(log n)。

**证明**：
B树通过分裂和合并操作保持平衡，每个节点至少有⌈m/2⌉个子节点，
最多有m个子节点，因此树的高度为O(log n)。□

### 3.2 索引选择定理

**定理 3.2**（索引选择）
对于等值查询，哈希索引比B树索引更高效。

**证明**：
哈希索引的时间复杂度为O(1)，而B树索引的时间复杂度为O(log n)，
因此对于等值查询，哈希索引更高效。□

## 4. Rust代码实现

### 4.1 B树索引实现

```rust
use std::cmp::Ordering;

#[derive(Debug)]
pub struct BTreeNode<K, V> {
    pub keys: Vec<K>,
    pub values: Vec<V>,
    pub children: Vec<BTreeNode<K, V>>,
    pub is_leaf: bool,
}

impl<K: Ord + Clone, V: Clone> BTreeNode<K, V> {
    pub fn new(is_leaf: bool) -> Self {
        BTreeNode {
            keys: Vec::new(),
            values: Vec::new(),
            children: Vec::new(),
            is_leaf,
        }
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        if self.is_leaf {
            self.insert_leaf(key, value)
        } else {
            self.insert_non_leaf(key, value)
        }
    }

    fn insert_leaf(&mut self, key: K, value: V) -> Option<V> {
        let pos = self.keys.binary_search(&key);
        match pos {
            Ok(index) => {
                // 键已存在，替换值
                let old_value = self.values[index].clone();
                self.values[index] = value;
                Some(old_value)
            }
            Err(index) => {
                // 插入新键值对
                self.keys.insert(index, key);
                self.values.insert(index, value);
                None
            }
        }
    }

    fn insert_non_leaf(&mut self, key: K, value: V) -> Option<V> {
        let child_index = self.find_child_index(&key);
        let child = &mut self.children[child_index];

        if child.keys.len() >= 3 { // 简化的分裂条件
            self.split_child(child_index);
            let new_child_index = self.find_child_index(&key);
            return self.children[new_child_index].insert(key, value);
        }

        child.insert(key, value)
    }

    fn find_child_index(&self, key: &K) -> usize {
        self.keys.binary_search(key).unwrap_or_else(|i| i)
    }

    fn split_child(&mut self, child_index: usize) {
        let child = &mut self.children[child_index];
        let mid = child.keys.len() / 2;

        let right_keys = child.keys.split_off(mid + 1);
        let right_values = child.values.split_off(mid + 1);
        let right_children = if !child.is_leaf {
            child.children.split_off(mid + 1)
        } else {
            Vec::new()
        };

        let key = child.keys.pop().unwrap();
        let value = child.values.pop().unwrap();

        let right_node = BTreeNode {
            keys: right_keys,
            values: right_values,
            children: right_children,
            is_leaf: child.is_leaf,
        };

        self.keys.insert(child_index, key);
        self.values.insert(child_index, value);
        self.children.insert(child_index + 1, right_node);
    }

    pub fn search(&self, key: &K) -> Option<&V> {
        if self.is_leaf {
            self.search_leaf(key)
        } else {
            self.search_non_leaf(key)
        }
    }

    fn search_leaf(&self, key: &K) -> Option<&V> {
        self.keys.binary_search(key)
            .ok()
            .map(|index| &self.values[index])
    }

    fn search_non_leaf(&self, key: &K) -> Option<&V> {
        let child_index = self.find_child_index(key);
        if child_index < self.children.len() {
            self.children[child_index].search(key)
        } else {
            None
        }
    }
}
```

### 4.2 哈希索引实现

```rust
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

#[derive(Debug)]
pub struct HashIndex<K, V> {
    pub buckets: Vec<Vec<(K, V)>>,
    pub size: usize,
    pub capacity: usize,
}

impl<K: Hash + Eq + Clone, V: Clone> HashIndex<K, V> {
    pub fn new(capacity: usize) -> Self {
        HashIndex {
            buckets: vec![Vec::new(); capacity],
            size: 0,
            capacity,
        }
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let index = self.hash(&key);
        let bucket = &mut self.buckets[index];

        // 检查是否已存在相同的键
        for (i, (existing_key, _)) in bucket.iter().enumerate() {
            if existing_key == &key {
                let old_value = bucket[i].1.clone();
                bucket[i] = (key, value);
                return Some(old_value);
            }
        }

        // 插入新键值对
        bucket.push((key, value));
        self.size += 1;

        // 检查是否需要重新哈希
        if self.size > self.capacity * 3 / 4 {
            self.rehash();
        }

        None
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        let index = self.hash(key);
        let bucket = &self.buckets[index];

        for (existing_key, value) in bucket {
            if existing_key == key {
                return Some(value);
            }
        }

        None
    }

    pub fn remove(&mut self, key: &K) -> Option<V> {
        let index = self.hash(key);
        let bucket = &mut self.buckets[index];

        for (i, (existing_key, _)) in bucket.iter().enumerate() {
            if existing_key == key {
                let (_, value) = bucket.remove(i);
                self.size -= 1;
                return Some(value);
            }
        }

        None
    }

    fn hash(&self, key: &K) -> usize {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        key.hash(&mut hasher);
        (hasher.finish() as usize) % self.capacity
    }

    fn rehash(&mut self) {
        let old_buckets = std::mem::replace(&mut self.buckets, vec![Vec::new(); self.capacity * 2]);
        self.capacity *= 2;
        self.size = 0;

        for bucket in old_buckets {
            for (key, value) in bucket {
                self.insert(key, value);
            }
        }
    }
}
```

### 4.3 索引管理器实现

```rust
use std::collections::HashMap;

#[derive(Debug)]
pub struct IndexManager<K, V> {
    pub indexes: HashMap<String, Box<dyn Index<K, V>>>,
}

pub trait Index<K, V> {
    fn insert(&mut self, key: K, value: V) -> Option<V>;
    fn get(&self, key: &K) -> Option<&V>;
    fn remove(&mut self, key: &K) -> Option<V>;
    fn range_query(&self, start: &K, end: &K) -> Vec<&V>;
}

impl<K: Ord + Clone + Hash, V: Clone> IndexManager<K, V> {
    pub fn new() -> Self {
        IndexManager {
            indexes: HashMap::new(),
        }
    }

    pub fn create_btree_index(&mut self, name: String) {
        let index = BTreeIndex::new();
        self.indexes.insert(name, Box::new(index));
    }

    pub fn create_hash_index(&mut self, name: String, capacity: usize) {
        let index = HashIndex::new(capacity);
        self.indexes.insert(name, Box::new(index));
    }

    pub fn insert(&mut self, index_name: &str, key: K, value: V) -> Result<Option<V>, String> {
        if let Some(index) = self.indexes.get_mut(index_name) {
            Ok(index.insert(key, value))
        } else {
            Err(format!("Index '{}' not found", index_name))
        }
    }

    pub fn get(&self, index_name: &str, key: &K) -> Result<Option<&V>, String> {
        if let Some(index) = self.indexes.get(index_name) {
            Ok(index.get(key))
        } else {
            Err(format!("Index '{}' not found", index_name))
        }
    }

    pub fn remove(&mut self, index_name: &str, key: &K) -> Result<Option<V>, String> {
        if let Some(index) = self.indexes.get_mut(index_name) {
            Ok(index.remove(key))
        } else {
            Err(format!("Index '{}' not found", index_name))
        }
    }
}

// 为B树索引实现Index trait
impl<K: Ord + Clone, V: Clone> Index<K, V> for BTreeNode<K, V> {
    fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.insert(key, value)
    }

    fn get(&self, key: &K) -> Option<&V> {
        self.search(key)
    }

    fn remove(&mut self, _key: &K) -> Option<V> {
        // 简化的删除实现
        None
    }

    fn range_query(&self, start: &K, end: &K) -> Vec<&V> {
        let mut results = Vec::new();
        self.range_query_recursive(start, end, &mut results);
        results
    }
}

impl<K: Ord + Clone, V: Clone> BTreeNode<K, V> {
    fn range_query_recursive(&self, start: &K, end: &K, results: &mut Vec<&V>) {
        if self.is_leaf {
            for (i, key) in self.keys.iter().enumerate() {
                if key >= start && key <= end {
                    results.push(&self.values[i]);
                }
            }
        } else {
            for (i, key) in self.keys.iter().enumerate() {
                if key >= start {
                    self.children[i].range_query_recursive(start, end, results);
                }
                if key > end {
                    break;
                }
            }
            if self.children.len() > self.keys.len() {
                self.children[self.keys.len()].range_query_recursive(start, end, results);
            }
        }
    }
}

// 为哈希索引实现Index trait
impl<K: Hash + Eq + Clone, V: Clone> Index<K, V> for HashIndex<K, V> {
    fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.insert(key, value)
    }

    fn get(&self, key: &K) -> Option<&V> {
        self.get(key)
    }

    fn remove(&mut self, key: &K) -> Option<V> {
        self.remove(key)
    }

    fn range_query(&self, _start: &K, _end: &K) -> Vec<&V> {
        // 哈希索引不支持范围查询
        Vec::new()
    }
}
```

## 5. 相关理论与交叉引用

- **数学基础**：树论、哈希理论在索引设计中的应用
- **形式语言理论**：索引查询的形式化描述
- **类型理论**：索引的类型安全保证
- **控制论**：索引性能的反馈控制机制
- **人工智能理论**：智能化的索引选择和优化

## 6. 参考文献

1. Bayer, R., & McCreight, E. M. (1972). "Organization and maintenance of large ordered indices"
2. Comer, D. (1979). "The ubiquitous B-tree"
3. Knuth, D. E. (1998). "The art of computer programming, volume 3: Sorting and searching"
4. O'Neil, P. E., & O'Neil, E. J. (2001). "Database: Principles, programming, and performance"

## 批判性分析

### 主要理论观点梳理

- 结构与代价：B+树/LSM/哈希/倒排/位图索引在更新/查询/范围/聚合/空间等维度的取舍；与存储介质/压缩/并行执行紧耦合。
- 运行时反馈：基于查询画像与执行反馈的自适应索引/自动索引建议，形成“优化—执行—回馈”的闭环。

### 理论优势与局限性

**优势**：

- 显著降低查询I/O与CPU代价，支持范围/排序/聚合等操作加速
- 与物理设计（分区、聚簇、覆盖索引）协同，提升整体吞吐

**局限性**：

- 维护开销：写放大/空间放大；数据分布变化引起效益退化
- 自适应不足：静态策略难应对负载/分布漂移；多目标（延时/吞吐/成本）难统一

### 学科交叉融合

- 与算法/数据结构：平衡树、跳表、布隆过滤器、压缩编码
- 与系统结构：存储分层（NVMe/PMem）、向量化/GPU 加速、日志结构存储
- 与学习方法：学习索引、代价/风险评估模型、回退策略

### 创新批判与未来展望

- 云/成本感知索引：引入资源与货币成本维度，进行全局优化
- 自适应与鲁棒：不确定性量化、鲁棒优化与在线重配置；黑盒学习索引的稳定性与治理
