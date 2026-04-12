//! # 零成本抽象
//! 
//! 展示 Rust 的零成本抽象特性

use std::ops::{Add, Sub, Mul, Div};

/// 零成本迭代器包装
pub struct ZeroCostIter<I> {
    inner: I,
}

impl<I> ZeroCostIter<I> {
    pub fn new(inner: I) -> Self {
        Self { inner }
    }
}

impl<I: Iterator> Iterator for ZeroCostIter<I> {
    type Item = I::Item;
    
    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
    
    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// 编译期数组大小
pub struct ConstArray<T, const N: usize> {
    data: [T; N],
}

impl<T: Copy + Default, const N: usize> ConstArray<T, N> {
    pub fn new() -> Self {
        Self { data: [T::default(); N] }
    }
    
    pub fn from_array(data: [T; N]) -> Self {
        Self { data }
    }
    
    #[inline(always)]
    pub fn get(&self, index: usize) -> Option<&T> {
        self.data.get(index)
    }
    
    #[inline(always)]
    pub const fn len(&self) -> usize {
        N
    }
    
    pub fn as_slice(&self) -> &[T] {
        &self.data
    }
}

impl<T: Copy + Default, const N: usize> Default for ConstArray<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

/// 编译期计算阶乘
pub const fn const_factorial(n: u64) -> u64 {
    let mut result = 1;
    let mut i = 1;
    while i <= n {
        result *= i;
        i += 1;
    }
    result
}

/// 编译期计算斐波那契数列
pub const fn const_fibonacci(n: u64) -> u64 {
    if n <= 1 {
        return n;
    }
    
    let mut a = 0;
    let mut b = 1;
    let mut i = 2;
    
    while i <= n {
        let temp = a + b;
        a = b;
        b = temp;
        i += 1;
    }
    b
}

/// SIMD-like 向量化操作
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Vec4(f32, f32, f32, f32);

impl Vec4 {
    #[inline(always)]
    pub fn new(x: f32, y: f32, z: f32, w: f32) -> Self {
        Self(x, y, z, w)
    }
    
    #[inline(always)]
    pub fn splat(v: f32) -> Self {
        Self(v, v, v, v)
    }
    
    #[inline(always)]
    pub fn add(&self, other: Self) -> Self {
        Self(self.0 + other.0, self.1 + other.1, self.2 + other.2, self.3 + other.3)
    }
    
    #[inline(always)]
    pub fn mul(&self, other: Self) -> Self {
        Self(self.0 * other.0, self.1 * other.1, self.2 * other.2, self.3 * other.3)
    }
    
    #[inline(always)]
    pub fn scale(&self, scalar: f32) -> Self {
        Self(self.0 * scalar, self.1 * scalar, self.2 * scalar, self.3 * scalar)
    }
    
    #[inline(always)]
    pub fn dot(&self, other: Self) -> f32 {
        self.0 * other.0 + self.1 * other.1 + self.2 * other.2 + self.3 * other.3
    }
    
    #[inline(always)]
    pub fn length_squared(&self) -> f32 {
        self.dot(*self)
    }
    
    #[inline(always)]
    pub fn length(&self) -> f32 {
        self.length_squared().sqrt()
    }
}

/// 编译期字符串哈希
pub const fn const_hash(s: &str) -> u64 {
    let bytes = s.as_bytes();
    let mut hash: u64 = 0xcbf29ce484222325;
    let mut i = 0;
    while i < bytes.len() {
        hash ^= bytes[i] as u64;
        hash = hash.wrapping_mul(0x100000001b3);
        i += 1;
    }
    hash
}

/// 内联优化示例
#[inline(always)]
pub fn fast_sqrt(x: f64) -> f64 {
    if x <= 0.0 {
        return 0.0;
    }
    
    let mut guess = x;
    for _ in 0..10 {
        guess = (guess + x / guess) / 2.0;
    }
    guess
}

/// 缓存友好的矩阵块
pub struct BlockMatrix<T, const BLOCK_SIZE: usize> {
    data: Vec<T>,
    rows: usize,
    cols: usize,
}

impl<T: Default + Copy, const BLOCK_SIZE: usize> BlockMatrix<T, BLOCK_SIZE> {
    pub fn new(rows: usize, cols: usize) -> Self {
        let size = rows * cols;
        Self {
            data: vec![T::default(); size],
            rows,
            cols,
        }
    }
    
    #[inline(always)]
    pub fn get(&self, row: usize, col: usize) -> T {
        assert!(row < self.rows && col < self.cols);
        self.data[row * self.cols + col]
    }
    
    #[inline(always)]
    pub fn set(&mut self, row: usize, col: usize, value: T) {
        assert!(row < self.rows && col < self.cols);
        self.data[row * self.cols + col] = value;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_const_array() {
        let arr: ConstArray<i32, 5> = ConstArray::from_array([1, 2, 3, 4, 5]);
        assert_eq!(arr.len(), 5);
        assert_eq!(arr.get(2), Some(&3));
    }

    #[test]
    fn test_const_factorial() {
        assert_eq!(const_factorial(0), 1);
        assert_eq!(const_factorial(5), 120);
        assert_eq!(const_factorial(10), 3628800);
    }

    #[test]
    fn test_vec4() {
        let v1 = Vec4::new(1.0, 2.0, 3.0, 4.0);
        let v2 = Vec4::new(2.0, 3.0, 4.0, 5.0);
        
        let sum = v1.add(v2);
        assert_eq!(sum.0, 3.0);
        
        let dot = v1.dot(v2);
        assert_eq!(dot, 40.0);
    }

    #[test]
    fn test_block_matrix() {
        let mut m1: BlockMatrix<i32, 2> = BlockMatrix::new(4, 4);
        m1.set(0, 0, 1);
        m1.set(1, 1, 2);
        
        assert_eq!(m1.get(0, 0), 1);
        assert_eq!(m1.get(1, 1), 2);
    }
}
