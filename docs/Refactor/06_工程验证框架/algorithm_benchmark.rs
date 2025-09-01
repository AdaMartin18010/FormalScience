use std::time::{Duration, Instant};
use std::collections::HashMap;

/// 算法性能指标
#[derive(Debug, Clone)]
pub struct AlgorithmMetrics {
    pub algorithm_name: String,
    pub input_size: usize,
    pub time_complexity: f64,
    pub space_complexity: f64,
    pub actual_runtime: Duration,
    pub memory_usage: usize,
    pub correctness_score: f64,
}

/// 算法基准测试特征
pub trait AlgorithmBenchmark {
    fn name(&self) -> &str;
    fn run(&self, input: &[i32]) -> Vec<i32>;
    fn is_correct(&self, input: &[i32], output: &[i32]) -> bool;
    fn benchmark(&self, input_size: usize) -> AlgorithmMetrics;
}

/// 排序算法基准测试
pub struct SortingBenchmark;

impl SortingBenchmark {
    pub fn new() -> Self {
        Self
    }
    
    /// 生成测试数据
    pub fn generate_test_data(size: usize) -> Vec<i32> {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        (0..size).map(|_| rng.gen_range(0..1000)).collect()
    }
    
    /// 验证排序结果
    pub fn verify_sorting(input: &[i32], output: &[i32]) -> bool {
        if input.len() != output.len() {
            return false;
        }
        
        // 检查是否有序
        for i in 1..output.len() {
            if output[i] < output[i-1] {
                return false;
            }
        }
        
        // 检查元素是否一致
        let mut input_count = HashMap::new();
        let mut output_count = HashMap::new();
        
        for &x in input {
            *input_count.entry(x).or_insert(0) += 1;
        }
        
        for &x in output {
            *output_count.entry(x).or_insert(0) += 1;
        }
        
        input_count == output_count
    }
}

/// 快速排序实现
pub struct QuickSort;

impl QuickSort {
    pub fn sort(arr: &mut [i32]) {
        if arr.len() <= 1 {
            return;
        }
        
        let pivot_index = Self::partition(arr);
        Self::sort(&mut arr[..pivot_index]);
        Self::sort(&mut arr[pivot_index + 1..]);
    }
    
    fn partition(arr: &mut [i32]) -> usize {
        let pivot_index = arr.len() - 1;
        let mut i = 0;
        
        for j in 0..pivot_index {
            if arr[j] <= arr[pivot_index] {
                arr.swap(i, j);
                i += 1;
            }
        }
        
        arr.swap(i, pivot_index);
        i
    }
}

impl AlgorithmBenchmark for QuickSort {
    fn name(&self) -> &str {
        "QuickSort"
    }
    
    fn run(&self, input: &[i32]) -> Vec<i32> {
        let mut arr = input.to_vec();
        Self::sort(&mut arr);
        arr
    }
    
    fn is_correct(&self, input: &[i32], output: &[i32]) -> bool {
        SortingBenchmark::verify_sorting(input, output)
    }
    
    fn benchmark(&self, input_size: usize) -> AlgorithmMetrics {
        let input = SortingBenchmark::generate_test_data(input_size);
        let memory_before = std::mem::size_of_val(&input);
        
        let start = Instant::now();
        let output = self.run(&input);
        let runtime = start.elapsed();
        
        let memory_after = std::mem::size_of_val(&output);
        let correctness = if self.is_correct(&input, &output) { 1.0 } else { 0.0 };
        
        AlgorithmMetrics {
            algorithm_name: self.name().to_string(),
            input_size,
            time_complexity: (input_size as f64) * (input_size as f64).log2(),
            space_complexity: input_size as f64,
            actual_runtime: runtime,
            memory_usage: memory_after - memory_before,
            correctness_score: correctness,
        }
    }
}

/// 归并排序实现
pub struct MergeSort;

impl MergeSort {
    pub fn sort(arr: &mut [i32]) {
        if arr.len() <= 1 {
            return;
        }
        
        let mid = arr.len() / 2;
        Self::sort(&mut arr[..mid]);
        Self::sort(&mut arr[mid..]);
        Self::merge(arr, mid);
    }
    
    fn merge(arr: &mut [i32], mid: usize) {
        let left = arr[..mid].to_vec();
        let right = arr[mid..].to_vec();
        
        let mut i = 0;
        let mut j = 0;
        let mut k = 0;
        
        while i < left.len() && j < right.len() {
            if left[i] <= right[j] {
                arr[k] = left[i];
                i += 1;
            } else {
                arr[k] = right[j];
                j += 1;
            }
            k += 1;
        }
        
        while i < left.len() {
            arr[k] = left[i];
            i += 1;
            k += 1;
        }
        
        while j < right.len() {
            arr[k] = right[j];
            j += 1;
            k += 1;
        }
    }
}

impl AlgorithmBenchmark for MergeSort {
    fn name(&self) -> &str {
        "MergeSort"
    }
    
    fn run(&self, input: &[i32]) -> Vec<i32> {
        let mut arr = input.to_vec();
        Self::sort(&mut arr);
        arr
    }
    
    fn is_correct(&self, input: &[i32], output: &[i32]) -> bool {
        SortingBenchmark::verify_sorting(input, output)
    }
    
    fn benchmark(&self, input_size: usize) -> AlgorithmMetrics {
        let input = SortingBenchmark::generate_test_data(input_size);
        let memory_before = std::mem::size_of_val(&input);
        
        let start = Instant::now();
        let output = self.run(&input);
        let runtime = start.elapsed();
        
        let memory_after = std::mem::size_of_val(&output);
        let correctness = if self.is_correct(&input, &output) { 1.0 } else { 0.0 };
        
        AlgorithmMetrics {
            algorithm_name: self.name().to_string(),
            input_size,
            time_complexity: (input_size as f64) * (input_size as f64).log2(),
            space_complexity: input_size as f64,
            actual_runtime: runtime,
            memory_usage: memory_after - memory_before,
            correctness_score: correctness,
        }
    }
}

/// 基准测试运行器
pub struct BenchmarkRunner;

impl BenchmarkRunner {
    pub fn run_benchmarks() -> Vec<AlgorithmMetrics> {
        let algorithms: Vec<Box<dyn AlgorithmBenchmark>> = vec![
            Box::new(QuickSort),
            Box::new(MergeSort),
        ];
        
        let input_sizes = vec![100, 1000, 10000];
        let mut results = Vec::new();
        
        for algorithm in algorithms {
            for &size in &input_sizes {
                let metrics = algorithm.benchmark(size);
                results.push(metrics);
            }
        }
        
        results
    }
    
    pub fn print_results(results: &[AlgorithmMetrics]) {
        println!("Algorithm Benchmark Results:");
        println!("{:<15} {:<10} {:<15} {:<15} {:<10}", 
                "Algorithm", "Size", "Runtime(ms)", "Memory(bytes)", "Correctness");
        println!("{}", "-".repeat(70));
        
        for result in results {
            println!("{:<15} {:<10} {:<15.2} {:<15} {:<10.2}", 
                    result.algorithm_name,
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
    fn test_quick_sort() {
        let mut arr = vec![3, 1, 4, 1, 5, 9, 2, 6];
        QuickSort::sort(&mut arr);
        assert_eq!(arr, vec![1, 1, 2, 3, 4, 5, 6, 9]);
    }
    
    #[test]
    fn test_merge_sort() {
        let mut arr = vec![3, 1, 4, 1, 5, 9, 2, 6];
        MergeSort::sort(&mut arr);
        assert_eq!(arr, vec![1, 1, 2, 3, 4, 5, 6, 9]);
    }
    
    #[test]
    fn test_benchmark() {
        let results = BenchmarkRunner::run_benchmarks();
        assert!(!results.is_empty());
        
        for result in &results {
            assert_eq!(result.correctness_score, 1.0);
            assert!(result.actual_runtime.as_millis() < 1000);
        }
    }
}

fn main() {
    let results = BenchmarkRunner::run_benchmarks();
    BenchmarkRunner::print_results(&results);
} 