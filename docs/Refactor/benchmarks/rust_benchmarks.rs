//! FormalScience Rust 性能基准测试
//!
//! 测试内容：
//! 1. 调度算法性能对比
//! 2. 类型检查器性能
//! 3. 网络同步性能
//! 4. 内存分配性能
//!
//! 运行方式:
//!   cargo bench --features benchmark

#![cfg_attr(feature = "benchmark", feature(test))]

#[cfg(all(feature = "benchmark", test))]
extern crate test;

use std::time::{Duration, Instant};
use std::collections::{HashMap, VecDeque, BTreeMap};

// ============================================
// 基准测试框架
// ============================================

/// 计时结果
#[derive(Debug, Clone)]
pub struct BenchmarkResult {
    pub name: String,
    pub mean_time: Duration,
    pub min_time: Duration,
    pub max_time: Duration,
    pub iterations: usize,
    pub throughput: f64, // ops/sec
}

impl BenchmarkResult {
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            mean_time: Duration::ZERO,
            min_time: Duration::MAX,
            max_time: Duration::ZERO,
            iterations: 0,
            throughput: 0.0,
        }
    }
    
    pub fn print(&self) {
        println!(
            "  {:<25} │ 平均: {:>8.3}ms │ 吞吐量: {:>10.1} ops/sec",
            self.name,
            self.mean_time.as_secs_f64() * 1000.0,
            self.throughput
        );
    }
}

/// 运行基准测试
pub fn run_benchmark<F>(name: &str, iterations: usize, mut f: F) -> BenchmarkResult
where
    F: FnMut(),
{
    // Warmup
    for _ in 0..iterations.min(100) {
        f();
    }
    
    let mut times = Vec::with_capacity(iterations);
    
    for _ in 0..iterations {
        let start = Instant::now();
        f();
        let elapsed = start.elapsed();
        times.push(elapsed);
    }
    
    let total: Duration = times.iter().sum();
    let mean = total / iterations as u32;
    let min = *times.iter().min().unwrap_or(&Duration::ZERO);
    let max = *times.iter().max().unwrap_or(&Duration::ZERO);
    let throughput = iterations as f64 / total.as_secs_f64();
    
    BenchmarkResult {
        name: name.to_string(),
        mean_time: mean,
        min_time: min,
        max_time: max,
        iterations,
        throughput,
    }
}

/// 对比两个算法的性能
pub fn compare_benchmarks<F1, F2>(
    name: &str,
    baseline_name: &str,
    baseline: F1,
    candidate_name: &str,
    candidate: F2,
    iterations: usize,
) where
    F1: FnMut(),
    F2: FnMut(),
{
    println!("\n📊 {} 性能对比:", name);
    
    let r1 = run_benchmark(baseline_name, iterations, baseline);
    let r2 = run_benchmark(candidate_name, iterations, candidate);
    
    r1.print();
    r2.print();
    
    let improvement = (r1.mean_time.as_secs_f64() - r2.mean_time.as_secs_f64()) 
        / r1.mean_time.as_secs_f64() * 100.0;
    
    if improvement > 0.0 {
        println!("  → {} 比 {} 快 {:.1}%", candidate_name, baseline_name, improvement);
    } else {
        println!("  → {} 比 {} 慢 {:.1}%", candidate_name, baseline_name, -improvement);
    }
}

// ============================================
// 测试 1: 调度算法性能
// ============================================

/// 调度任务
#[derive(Debug, Clone)]
struct Task {
    id: u64,
    priority: u32,
    deadline: Instant,
    workload: Duration,
}

/// 简单调度器（基准实现）
mod simple_scheduler {
    use super::*;
    
    pub fn schedule(tasks: &mut [Task]) -> Vec<u64> {
        tasks.sort_by_key(|t| t.priority);
        tasks.iter().map(|t| t.id).collect()
    }
    
    pub fn find_earliest_deadline(tasks: &[Task]) -> Option<u64> {
        tasks.iter().min_by_key(|t| t.deadline).map(|t| t.id)
    }
}

/// 优化调度器（候选实现）
mod optimized_scheduler {
    use super::*;
    use std::collections::BinaryHeap;
    
    #[derive(Debug, Clone, Eq, PartialEq)]
    struct TaskWrapper(Task);
    
    impl Ord for TaskWrapper {
        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
            other.0.priority.cmp(&self.0.priority)
        }
    }
    
    impl PartialOrd for TaskWrapper {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            Some(self.cmp(other))
        }
    }
    
    pub fn schedule(tasks: &[Task]) -> Vec<u64> {
        let mut heap: BinaryHeap<TaskWrapper> = tasks
            .iter()
            .cloned()
            .map(TaskWrapper)
            .collect();
        
        let mut result = Vec::with_capacity(tasks.len());
        while let Some(t) = heap.pop() {
            result.push(t.0.id);
        }
        result
    }
    
    pub fn find_earliest_deadline(tasks: &[Task]) -> Option<u64> {
        tasks.iter().enumerate()
            .min_by_key(|(_, t)| t.deadline)
            .map(|(idx, _)| tasks[idx].id)
    }
}

fn generate_tasks(count: usize) -> Vec<Task> {
    (0..count)
        .map(|i| Task {
            id: i as u64,
            priority: (i % 100) as u32,
            deadline: Instant::now() + Duration::from_millis((i * 100) as u64),
            workload: Duration::from_millis(10),
        })
        .collect()
}

pub fn benchmark_scheduling() {
    println!("\n🔵 调度算法性能测试");
    println!("═══════════════════════════════════════════════════════════════");
    
    // 测试 1: 优先级调度
    let tasks_100 = generate_tasks(100);
    let tasks_1000 = generate_tasks(1000);
    let tasks_10000 = generate_tasks(10000);
    
    compare_benchmarks(
        "优先级调度 (100 任务)",
        "简单排序",
        || {
            let mut t = tasks_100.clone();
            let _ = simple_scheduler::schedule(&mut t);
        },
        "堆优化",
        || {
            let t = tasks_100.clone();
            let _ = optimized_scheduler::schedule(&t);
        },
        10000,
    );
    
    compare_benchmarks(
        "优先级调度 (1000 任务)",
        "简单排序",
        || {
            let mut t = tasks_1000.clone();
            let _ = simple_scheduler::schedule(&mut t);
        },
        "堆优化",
        || {
            let t = tasks_1000.clone();
            let _ = optimized_scheduler::schedule(&t);
        },
        1000,
    );
    
    compare_benchmarks(
        "优先级调度 (10000 任务)",
        "简单排序",
        || {
            let mut t = tasks_10000.clone();
            let _ = simple_scheduler::schedule(&mut t);
        },
        "堆优化",
        || {
            let t = tasks_10000.clone();
            let _ = optimized_scheduler::schedule(&t);
        },
        100,
    );
    
    // 测试 2: 截止时间查找
    let r1 = run_benchmark("最早截止时间查找", 100000, || {
        let _ = simple_scheduler::find_earliest_deadline(&tasks_1000);
    });
    r1.print();
}

// ============================================
// 测试 2: 类型检查器性能
// ============================================

/// 正则表达式类型定义
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum RegexType {
    Empty,
    Epsilon,
    Char(char),
    Concat(Box<RegexType>, Box<RegexType>),
    Union(Box<RegexType>, Box<RegexType>),
    Star(Box<RegexType>),
}

impl RegexType {
    fn size(&self) -> usize {
        match self {
            RegexType::Empty | RegexType::Epsilon | RegexType::Char(_) => 1,
            RegexType::Concat(l, r) => 1 + l.size() + r.size(),
            RegexType::Union(l, r) => 1 + l.size() + r.size(),
            RegexType::Star(r) => 1 + r.size(),
        }
    }
    
    fn nullable(&self) -> bool {
        match self {
            RegexType::Empty => false,
            RegexType::Epsilon | RegexType::Star(_) => true,
            RegexType::Char(_) => false,
            RegexType::Concat(l, r) => l.nullable() && r.nullable(),
            RegexType::Union(l, r) => l.nullable() || r.nullable(),
        }
    }
    
    fn derivative(&self, c: char) -> RegexType {
        match self {
            RegexType::Empty => RegexType::Empty,
            RegexType::Epsilon => RegexType::Empty,
            RegexType::Char(d) if *d == c => RegexType::Epsilon,
            RegexType::Char(_) => RegexType::Empty,
            RegexType::Concat(l, r) => {
                if l.nullable() {
                    RegexType::Union(
                        Box::new(RegexType::Concat(Box::new(l.derivative(c)), r.clone())),
                        Box::new(r.derivative(c)),
                    )
                } else {
                    RegexType::Concat(Box::new(l.derivative(c)), r.clone())
                }
            }
            RegexType::Union(l, r) => {
                RegexType::Union(Box::new(l.derivative(c)), Box::new(r.derivative(c)))
            }
            RegexType::Star(r) => {
                RegexType::Concat(Box::new(r.derivative(c)), Box::new(RegexType::Star(r.clone())))
            }
        }
    }
    
    fn matches(&self, s: &str) -> bool {
        let mut current = self.clone();
        for c in s.chars() {
            current = current.derivative(c);
        }
        current.nullable()
    }
}

fn generate_regex(depth: usize) -> RegexType {
    if depth == 0 {
        RegexType::Char('a')
    } else {
        RegexType::Concat(
            Box::new(generate_regex(depth - 1)),
            Box::new(RegexType::Union(
                Box::new(RegexType::Char('b')),
                Box::new(RegexType::Star(Box::new(RegexType::Char('c')))),
            )),
        )
    }
}

pub fn benchmark_type_checker() {
    println!("\n🔵 类型检查器性能测试");
    println!("═══════════════════════════════════════════════════════════════");
    
    // 测试 1: 正则表达式构建
    let r1 = run_benchmark("正则表达式构建 (深度=5)", 10000, || {
        let _ = generate_regex(5);
    });
    r1.print();
    
    let r2 = run_benchmark("正则表达式构建 (深度=10)", 10000, || {
        let _ = generate_regex(10);
    });
    r2.print();
    
    // 测试 2: 正则表达式匹配
    let regex = generate_regex(5);
    let test_string = "abcccbaccc";
    
    let r3 = run_benchmark("正则表达式匹配", 10000, || {
        let _ = regex.matches(test_string);
    });
    r3.print();
    
    // 测试 3: 导数计算
    let r4 = run_benchmark("正则表达式导数计算", 10000, || {
        let _ = regex.derivative('a');
    });
    r4.print();
    
    // 测试 4: 可空性检查
    let r5 = run_benchmark("可空性检查", 100000, || {
        let _ = regex.nullable();
    });
    r5.print();
    
    println!("\n  正则表达式大小: {} 节点", regex.size());
}

// ============================================
// 测试 3: 数据结构性能
// ============================================

pub fn benchmark_data_structures() {
    println!("\n🔵 数据结构性能测试");
    println!("═══════════════════════════════════════════════════════════════");
    
    // 测试数据
    let n = 10000;
    let keys: Vec<i32> = (0..n).collect();
    let values: Vec<String> = (0..n).map(|i| format!("value_{}", i)).collect();
    
    // HashMap 插入
    let r1 = run_benchmark("HashMap 插入", 1000, || {
        let mut map = HashMap::new();
        for (k, v) in keys.iter().zip(values.iter()) {
            map.insert(*k, v.clone());
        }
    });
    r1.print();
    
    // BTreeMap 插入
    let r2 = run_benchmark("BTreeMap 插入", 1000, || {
        let mut map = BTreeMap::new();
        for (k, v) in keys.iter().zip(values.iter()) {
            map.insert(*k, v.clone());
        }
    });
    r2.print();
    
    // HashMap 查找
    let map: HashMap<i32, String> = keys.iter()
        .zip(values.iter())
        .map(|(k, v)| (*k, v.clone()))
        .collect();
    
    let r3 = run_benchmark("HashMap 查找", 100000, || {
        for k in keys.iter().step_by(10) {
            let _ = map.get(k);
        }
    });
    r3.print();
    
    // VecDeque 操作
    let r4 = run_benchmark("VecDeque push/pop", 100000, || {
        let mut deque = VecDeque::new();
        for i in 0..1000 {
            deque.push_back(i);
        }
        while let Some(_) = deque.pop_front() {}
    });
    r4.print();
}

// ============================================
// 测试 4: 内存分配性能
// ============================================

pub fn benchmark_memory() {
    println!("\n🔵 内存分配性能测试");
    println!("═══════════════════════════════════════════════════════════════");
    
    // 小对象分配
    let r1 = run_benchmark("小对象分配 (Vec<i32>)", 10000, || {
        let mut v = Vec::new();
        for i in 0..100 {
            v.push(i);
        }
        drop(v);
    });
    r1.print();
    
    // 大对象分配
    let r2 = run_benchmark("大对象分配 (Vec<u8> 1MB)", 1000, || {
        let v = vec![0u8; 1024 * 1024];
        drop(v);
    });
    r2.print();
    
    // 字符串操作
    let r3 = run_benchmark("字符串拼接", 10000, || {
        let mut s = String::new();
        for i in 0..100 {
            s.push_str(&format!("item_{} ", i));
        }
        drop(s);
    });
    r3.print();
    
    // Box 分配
    let r4 = run_benchmark("Box 分配/释放", 100000, || {
        let b = Box::new([0u64; 100]);
        drop(b);
    });
    r4.print();
}

// ============================================
// 主程序入口
// ============================================

fn main() {
    println!("╔═══════════════════════════════════════════════════════════════╗");
    println!("║     FormalScience Rust 性能基准测试                           ║");
    println!("╚═══════════════════════════════════════════════════════════════╝");
    
    benchmark_scheduling();
    benchmark_type_checker();
    benchmark_data_structures();
    benchmark_memory();
    
    println!("\n═══════════════════════════════════════════════════════════════");
    println!("✅ 所有基准测试完成!");
}

// ============================================
// 标准库 benchmark 集成
// ============================================

#[cfg(all(feature = "benchmark", test))]
mod benches {
    use super::*;
    use test::Bencher;
    
    #[bench]
    fn bench_scheduler_simple(b: &mut Bencher) {
        let tasks = generate_tasks(1000);
        b.iter(|| {
            let mut t = tasks.clone();
            simple_scheduler::schedule(&mut t)
        });
    }
    
    #[bench]
    fn bench_scheduler_optimized(b: &mut Bencher) {
        let tasks = generate_tasks(1000);
        b.iter(|| optimized_scheduler::schedule(&tasks));
    }
    
    #[bench]
    fn bench_regex_match(b: &mut Bencher) {
        let regex = generate_regex(5);
        b.iter(|| regex.matches("abcccbaccc"));
    }
    
    #[bench]
    fn bench_regex_derivative(b: &mut Bencher) {
        let regex = generate_regex(5);
        b.iter(|| regex.derivative('a'));
    }
    
    #[bench]
    fn bench_hashmap_insert(b: &mut Bencher) {
        b.iter(|| {
            let mut map = HashMap::new();
            for i in 0..1000 {
                map.insert(i, i.to_string());
            }
            map
        });
    }
}
