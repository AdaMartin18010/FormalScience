use std::collections::HashMap;
use std::time::{Duration, Instant};

/// 数据结构性能指标
#[derive(Debug, Clone)]
pub struct DataStructureMetrics {
    pub structure_name: String,
    pub operation: String,
    pub input_size: usize,
    pub time_complexity: f64,
    pub space_complexity: f64,
    pub actual_runtime: Duration,
    pub memory_usage: usize,
    pub correctness_score: f64,
}

/// 数据结构基准测试特征
pub trait DataStructureBenchmark {
    fn name(&self) -> &str;
    fn insert(&mut self, key: i32, value: String);
    fn get(&self, key: i32) -> Option<&String>;
    fn delete(&mut self, key: i32) -> Option<String>;
    fn benchmark(&self, operations: &[Operation]) -> DataStructureMetrics;
}

/// 操作类型
#[derive(Debug, Clone)]
pub enum Operation {
    Insert(i32, String),
    Get(i32),
    Delete(i32),
}

/// 二叉搜索树实现
pub struct BinarySearchTree {
    root: Option<Box<TreeNode>>,
}

#[derive(Debug)]
struct TreeNode {
    key: i32,
    value: String,
    left: Option<Box<TreeNode>>,
    right: Option<Box<TreeNode>>,
}

impl BinarySearchTree {
    pub fn new() -> Self {
        Self { root: None }
    }
    
    pub fn insert(&mut self, key: i32, value: String) {
        self.root = Some(Self::insert_recursive(self.root.take(), key, value));
    }
    
    fn insert_recursive(node: Option<Box<TreeNode>>, key: i32, value: String) -> Box<TreeNode> {
        match node {
            None => Box::new(TreeNode {
                key,
                value,
                left: None,
                right: None,
            }),
            Some(mut node) => {
                if key < node.key {
                    node.left = Some(Self::insert_recursive(node.left.take(), key, value));
                } else if key > node.key {
                    node.right = Some(Self::insert_recursive(node.right.take(), key, value));
                } else {
                    node.value = value;
                }
                node
            }
        }
    }
    
    pub fn get(&self, key: i32) -> Option<&String> {
        Self::get_recursive(&self.root, key)
    }
    
    fn get_recursive(node: &Option<Box<TreeNode>>, key: i32) -> Option<&String> {
        match node {
            None => None,
            Some(node) => {
                if key < node.key {
                    Self::get_recursive(&node.left, key)
                } else if key > node.key {
                    Self::get_recursive(&node.right, key)
                } else {
                    Some(&node.value)
                }
            }
        }
    }
    
    pub fn delete(&mut self, key: i32) -> Option<String> {
        let mut result = None;
        self.root = Self::delete_recursive(self.root.take(), key, &mut result);
        result
    }
    
    fn delete_recursive(node: Option<Box<TreeNode>>, key: i32, result: &mut Option<String>) -> Option<Box<TreeNode>> {
        match node {
            None => None,
            Some(mut node) => {
                if key < node.key {
                    node.left = Self::delete_recursive(node.left.take(), key, result);
                } else if key > node.key {
                    node.right = Self::delete_recursive(node.right.take(), key, result);
                } else {
                    *result = Some(node.value);
                    match (node.left.take(), node.right.take()) {
                        (None, None) => None,
                        (Some(left), None) => Some(left),
                        (None, Some(right)) => Some(right),
                        (Some(left), Some(right)) => {
                            let mut successor = right;
                            while let Some(ref mut left_child) = successor.left {
                                successor = successor.left.take().unwrap();
                            }
                            successor.left = Some(left);
                            Some(successor)
                        }
                    }
                }
                Some(node)
            }
        }
    }
}

impl DataStructureBenchmark for BinarySearchTree {
    fn name(&self) -> &str {
        "BinarySearchTree"
    }
    
    fn insert(&mut self, key: i32, value: String) {
        self.insert(key, value);
    }
    
    fn get(&self, key: i32) -> Option<&String> {
        self.get(key)
    }
    
    fn delete(&mut self, key: i32) -> Option<String> {
        self.delete(key)
    }
    
    fn benchmark(&self, operations: &[Operation]) -> DataStructureMetrics {
        let mut tree = BinarySearchTree::new();
        let memory_before = std::mem::size_of_val(&tree);
        
        let start = Instant::now();
        let mut correctness_score = 0.0;
        let mut correct_operations = 0;
        
        for operation in operations {
            match operation {
                Operation::Insert(key, value) => {
                    tree.insert(*key, value.clone());
                    correct_operations += 1;
                }
                Operation::Get(key) => {
                    if tree.get(*key).is_some() {
                        correct_operations += 1;
                    }
                }
                Operation::Delete(key) => {
                    if tree.delete(*key).is_some() {
                        correct_operations += 1;
                    }
                }
            }
        }
        
        let runtime = start.elapsed();
        let memory_after = std::mem::size_of_val(&tree);
        correctness_score = correct_operations as f64 / operations.len() as f64;
        
        DataStructureMetrics {
            structure_name: self.name().to_string(),
            operation: "Mixed".to_string(),
            input_size: operations.len(),
            time_complexity: (operations.len() as f64) * (operations.len() as f64).log2(),
            space_complexity: operations.len() as f64,
            actual_runtime: runtime,
            memory_usage: memory_after - memory_before,
            correctness_score,
        }
    }
}

/// 哈希表实现
pub struct HashMap {
    buckets: Vec<Vec<(i32, String)>>,
    size: usize,
}

impl HashMap {
    pub fn new() -> Self {
        Self {
            buckets: vec![Vec::new(); 16],
            size: 0,
        }
    }
    
    fn hash(&self, key: i32) -> usize {
        (key as usize) % self.buckets.len()
    }
    
    pub fn insert(&mut self, key: i32, value: String) {
        let hash = self.hash(key);
        
        // 检查是否已存在
        for (k, v) in &mut self.buckets[hash] {
            if *k == key {
                *v = value;
                return;
            }
        }
        
        // 插入新元素
        self.buckets[hash].push((key, value));
        self.size += 1;
        
        // 如果负载因子过高，重新哈希
        if self.size > self.buckets.len() * 2 {
            self.rehash();
        }
    }
    
    pub fn get(&self, key: i32) -> Option<&String> {
        let hash = self.hash(key);
        for (k, v) in &self.buckets[hash] {
            if *k == key {
                return Some(v);
            }
        }
        None
    }
    
    pub fn delete(&mut self, key: i32) -> Option<String> {
        let hash = self.hash(key);
        for (i, (k, v)) in self.buckets[hash].iter().enumerate() {
            if *k == key {
                self.size -= 1;
                return Some(self.buckets[hash].remove(i).1);
            }
        }
        None
    }
    
    fn rehash(&mut self) {
        let old_buckets = std::mem::replace(&mut self.buckets, vec![Vec::new(); self.buckets.len() * 2]);
        self.size = 0;
        
        for bucket in old_buckets {
            for (key, value) in bucket {
                self.insert(key, value);
            }
        }
    }
}

impl DataStructureBenchmark for HashMap {
    fn name(&self) -> &str {
        "HashMap"
    }
    
    fn insert(&mut self, key: i32, value: String) {
        self.insert(key, value);
    }
    
    fn get(&self, key: i32) -> Option<&String> {
        self.get(key)
    }
    
    fn delete(&mut self, key: i32) -> Option<String> {
        self.delete(key)
    }
    
    fn benchmark(&self, operations: &[Operation]) -> DataStructureMetrics {
        let mut map = HashMap::new();
        let memory_before = std::mem::size_of_val(&map);
        
        let start = Instant::now();
        let mut correctness_score = 0.0;
        let mut correct_operations = 0;
        
        for operation in operations {
            match operation {
                Operation::Insert(key, value) => {
                    map.insert(*key, value.clone());
                    correct_operations += 1;
                }
                Operation::Get(key) => {
                    if map.get(*key).is_some() {
                        correct_operations += 1;
                    }
                }
                Operation::Delete(key) => {
                    if map.delete(*key).is_some() {
                        correct_operations += 1;
                    }
                }
            }
        }
        
        let runtime = start.elapsed();
        let memory_after = std::mem::size_of_val(&map);
        correctness_score = correct_operations as f64 / operations.len() as f64;
        
        DataStructureMetrics {
            structure_name: self.name().to_string(),
            operation: "Mixed".to_string(),
            input_size: operations.len(),
            time_complexity: operations.len() as f64,
            space_complexity: operations.len() as f64,
            actual_runtime: runtime,
            memory_usage: memory_after - memory_before,
            correctness_score,
        }
    }
}

/// 数据结构基准测试运行器
pub struct DataStructureBenchmarkRunner;

impl DataStructureBenchmarkRunner {
    pub fn generate_operations(size: usize) -> Vec<Operation> {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        let mut operations = Vec::new();
        
        for i in 0..size {
            let operation_type = rng.gen_range(0..3);
            let key = rng.gen_range(0..1000);
            let value = format!("value_{}", i);
            
            match operation_type {
                0 => operations.push(Operation::Insert(key, value)),
                1 => operations.push(Operation::Get(key)),
                2 => operations.push(Operation::Delete(key)),
                _ => unreachable!(),
            }
        }
        
        operations
    }
    
    pub fn run_benchmarks() -> Vec<DataStructureMetrics> {
        let structures: Vec<Box<dyn DataStructureBenchmark>> = vec![
            Box::new(BinarySearchTree::new()),
            Box::new(HashMap::new()),
        ];
        
        let operation_sizes = vec![100, 1000, 10000];
        let mut results = Vec::new();
        
        for structure in structures {
            for &size in &operation_sizes {
                let operations = Self::generate_operations(size);
                let metrics = structure.benchmark(&operations);
                results.push(metrics);
            }
        }
        
        results
    }
    
    pub fn print_results(results: &[DataStructureMetrics]) {
        println!("Data Structure Benchmark Results:");
        println!("{:<20} {:<10} {:<15} {:<15} {:<10}", 
                "Structure", "Size", "Runtime(ms)", "Memory(bytes)", "Correctness");
        println!("{}", "-".repeat(75));
        
        for result in results {
            println!("{:<20} {:<10} {:<15.2} {:<15} {:<10.2}", 
                    result.structure_name,
                    result.input_size,
                    result.actual_runtime.as_millis(),
                    result.memory_usage,
                    result.correctness_score);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_binary_search_tree() {
        let mut tree = BinarySearchTree::new();
        tree.insert(1, "one".to_string());
        tree.insert(2, "two".to_string());
        tree.insert(3, "three".to_string());
        
        assert_eq!(tree.get(1), Some(&"one".to_string()));
        assert_eq!(tree.get(2), Some(&"two".to_string()));
        assert_eq!(tree.get(3), Some(&"three".to_string()));
        assert_eq!(tree.get(4), None);
        
        assert_eq!(tree.delete(2), Some("two".to_string()));
        assert_eq!(tree.get(2), None);
    }
    
    #[test]
    fn test_hash_map() {
        let mut map = HashMap::new();
        map.insert(1, "one".to_string());
        map.insert(2, "two".to_string());
        map.insert(3, "three".to_string());
        
        assert_eq!(map.get(1), Some(&"one".to_string()));
        assert_eq!(map.get(2), Some(&"two".to_string()));
        assert_eq!(map.get(3), Some(&"three".to_string()));
        assert_eq!(map.get(4), None);
        
        assert_eq!(map.delete(2), Some("two".to_string()));
        assert_eq!(map.get(2), None);
    }
    
    #[test]
    fn test_benchmark() {
        let results = DataStructureBenchmarkRunner::run_benchmarks();
        assert!(!results.is_empty());
        
        for result in &results {
            assert!(result.correctness_score > 0.0);
            assert!(result.actual_runtime.as_millis() < 1000);
        }
    }
}

fn main() {
    let results = DataStructureBenchmarkRunner::run_benchmarks();
    DataStructureBenchmarkRunner::print_results(&results);
} 