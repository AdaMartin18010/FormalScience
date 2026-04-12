//! # Trait 系统高级特性

use std::ops::{Add, Mul, Neg};

/// 半群 (Semigroup): 具有结合律的二元运算
pub trait Semigroup {
    fn combine(&self, other: &Self) -> Self;
}

/// 幺半群 (Monoid): 带有单位元的半群
pub trait Monoid: Semigroup {
    fn empty() -> Self;
}

/// 函子 (Functor)
pub trait Functor {
    type Item;
    
    fn map<B, F>(self, f: F) -> Self::Mapped<B>
    where
        F: FnMut(Self::Item) -> B;
    
    type Mapped<B>: Functor<Item = B>;
}

/// 向量空间元素
pub trait VectorSpace {
    type Scalar: Add<Output = Self::Scalar> + Mul<Output = Self::Scalar> + Copy;
    
    fn zero() -> Self;
    fn scale(&self, scalar: Self::Scalar) -> Self;
    fn add(&self, other: &Self) -> Self;
}

/// 范数空间
pub trait Normed: VectorSpace {
    fn norm(&self) -> Self::Scalar;
}

/// 向量实现
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Vector2<T> {
    pub x: T,
    pub y: T,
}

impl<T: Add<Output = T> + Mul<Output = T> + Copy + Default> VectorSpace for Vector2<T> {
    type Scalar = T;
    
    fn zero() -> Self {
        Self {
            x: T::default(),
            y: T::default(),
        }
    }
    
    fn scale(&self, scalar: T) -> Self {
        Self {
            x: self.x * scalar,
            y: self.y * scalar,
        }
    }
    
    fn add(&self, other: &Self) -> Self {
        Self {
            x: self.x + other.x,
            y: self.y + other.y,
        }
    }
}

impl Vector2<f64> {
    pub fn norm(&self) -> f64 {
        (self.x * self.x + self.y * self.y).sqrt()
    }
}

/// 泛型链表
#[derive(Debug, Clone, PartialEq)]
pub enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

impl<T> List<T> {
    pub fn new() -> Self {
        List::Nil
    }
    
    pub fn cons(head: T, tail: Self) -> Self {
        List::Cons(head, Box::new(tail))
    }
}

impl<T> Default for List<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone> Semigroup for List<T> {
    fn combine(&self, other: &Self) -> Self {
        match self {
            List::Nil => other.clone(),
            List::Cons(head, tail) => {
                List::Cons(head.clone(), Box::new(tail.combine(other)))
            }
        }
    }
}

impl<T: Clone> Monoid for List<T> {
    fn empty() -> Self {
        List::Nil
    }
}

/// 运算符重载示例：复数
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Complex<T> {
    pub re: T,
    pub im: T,
}

impl<T> Complex<T> {
    pub fn new(re: T, im: T) -> Self {
        Complex { re, im }
    }
}

impl<T: Add<Output = T>> Add for Complex<T> {
    type Output = Self;
    
    fn add(self, other: Self) -> Self {
        Complex {
            re: self.re + other.re,
            im: self.im + other.im,
        }
    }
}

impl<T: Mul<Output = T> + Add<Output = T> + Sub<Output = T> + Copy> Mul for Complex<T> {
    type Output = Self;
    
    fn mul(self, other: Self) -> Self {
        Complex {
            re: self.re * other.re - self.im * other.im,
            im: self.re * other.im + self.im * other.re,
        }
    }
}

impl<T: Neg<Output = T>> Neg for Complex<T> {
    type Output = Self;
    
    fn neg(self) -> Self {
        Complex {
            re: -self.re,
            im: -self.im,
        }
    }
}

use std::ops::Sub;

/// 显示 trait 示例
pub trait Display {
    fn display(&self) -> String;
}

impl Display for Complex<f64> {
    fn display(&self) -> String {
        format!("{:.2} + {:.2}i", self.re, self.im)
    }
}

/// 默认 trait 实现
pub trait Logger {
    fn log(&self, message: &str);
    
    fn log_error(&self, error: &str) {
        self.log(&format!("ERROR: {}", error));
    }
}

pub struct ConsoleLogger;

impl Logger for ConsoleLogger {
    fn log(&self, message: &str) {
        println!("[LOG] {}", message);
    }
}

/// Trait 边界和 where 子句示例
pub fn sum<T>(values: &[T]) -> T
where
    T: Add<Output = T> + Default + Copy,
{
    values.iter().fold(T::default(), |acc, &x| acc + x)
}

/// 关联类型示例
pub trait Graph {
    type Node;
    type Edge;
    
    fn nodes(&self) -> Vec<Self::Node>;
    fn edges(&self) -> Vec<Self::Edge>;
}

/// 具体图实现
pub struct AdjacencyList {
    adj: Vec<Vec<usize>>,
}

impl AdjacencyList {
    pub fn new(n: usize) -> Self {
        Self {
            adj: vec![Vec::new(); n],
        }
    }
    
    pub fn add_edge(&mut self, from: usize, to: usize) {
        self.adj[from].push(to);
    }
}

impl Graph for AdjacencyList {
    type Node = usize;
    type Edge = (usize, usize);
    
    fn nodes(&self) -> Vec<Self::Node> {
        (0..self.adj.len()).collect()
    }
    
    fn edges(&self) -> Vec<Self::Edge> {
        let mut edges = Vec::new();
        for (from, neighbors) in self.adj.iter().enumerate() {
            for &to in neighbors {
                edges.push((from, to));
            }
        }
        edges
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vector2() {
        let v1 = Vector2 { x: 1.0, y: 2.0 };
        let v2 = Vector2 { x: 3.0, y: 4.0 };
        
        let v3 = v1.add(&v2);
        assert_eq!(v3.x, 4.0);
        assert_eq!(v3.y, 6.0);
    }

    #[test]
    fn test_complex() {
        let c1 = Complex::new(1.0, 2.0);
        let c2 = Complex::new(3.0, 4.0);
        
        let sum = c1 + c2;
        assert_eq!(sum.re, 4.0);
        assert_eq!(sum.im, 6.0);
    }

    #[test]
    fn test_list_semigroup() {
        let list1 = List::cons(1, List::cons(2, List::Nil));
        let list2 = List::cons(3, List::cons(4, List::Nil));
        
        let combined = list1.combine(&list2);
        // 验证结果
        match combined {
            List::Cons(1, _) => assert!(true),
            _ => assert!(false, "Unexpected result"),
        }
    }

    #[test]
    fn test_graph() {
        let mut graph = AdjacencyList::new(3);
        graph.add_edge(0, 1);
        graph.add_edge(1, 2);
        
        assert_eq!(graph.nodes(), vec![0, 1, 2]);
    }

    #[test]
    fn test_sum() {
        let values = vec![1, 2, 3, 4, 5];
        assert_eq!(sum(&values), 15);
    }
}
