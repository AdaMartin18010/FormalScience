//! # 代数数据类型 (ADT) 实现
//! 
//! 展示 Rust 中代数数据类型的实现，包括：
//! - 乘积类型 (Product Types): 结构体
//! - 和类型 (Sum Types): 枚举
//! - 递归类型

/// 乘积类型示例：表示一个点
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Point {
    pub x: f64,
    pub y: f64,
}

impl Point {
    pub fn new(x: f64, y: f64) -> Self {
        Self { x, y }
    }

    pub fn distance_from_origin(&self) -> f64 {
        (self.x.powi(2) + self.y.powi(2)).sqrt()
    }

    pub fn translate(&mut self, dx: f64, dy: f64) {
        self.x += dx;
        self.y += dy;
    }
}

/// 和类型示例：表示可选值
#[derive(Debug, Clone, PartialEq)]
pub enum Option<T> {
    Some(T),
    None,
}

impl<T> Option<T> {
    pub fn is_some(&self) -> bool {
        matches!(self, Option::Some(_))
    }

    pub fn is_none(&self) -> bool {
        matches!(self, Option::None)
    }

    pub fn map<U, F>(self, f: F) -> Option<U>
    where
        F: FnOnce(T) -> U,
    {
        match self {
            Option::Some(x) => Option::Some(f(x)),
            Option::None => Option::None,
        }
    }

    pub fn unwrap_or(self, default: T) -> T {
        match self {
            Option::Some(x) => x,
            Option::None => default,
        }
    }
}

/// 和类型示例：表示结果
#[derive(Debug, Clone, PartialEq)]
pub enum Result<T, E> {
    Ok(T),
    Err(E),
}

impl<T, E> Result<T, E> {
    pub fn is_ok(&self) -> bool {
        matches!(self, Result::Ok(_))
    }

    pub fn is_err(&self) -> bool {
        matches!(self, Result::Err(_))
    }

    pub fn map<U, F>(self, f: F) -> Result<U, E>
    where
        F: FnOnce(T) -> U,
    {
        match self {
            Result::Ok(x) => Result::Ok(f(x)),
            Result::Err(e) => Result::Err(e),
        }
    }

    pub fn unwrap_or(self, default: T) -> T {
        match self {
            Result::Ok(x) => x,
            Result::Err(_) => default,
        }
    }
}

/// 递归类型示例：二叉树
#[derive(Debug, Clone, PartialEq)]
pub enum BinaryTree<T> {
    Empty,
    Node {
        value: T,
        left: Box<BinaryTree<T>>,
        right: Box<BinaryTree<T>>,
    },
}

impl<T: Clone> BinaryTree<T> {
    pub fn new(value: T) -> Self {
        BinaryTree::Node {
            value,
            left: Box::new(BinaryTree::Empty),
            right: Box::new(BinaryTree::Empty),
        }
    }

    pub fn insert_left(&mut self, new_value: T) {
        match self {
            BinaryTree::Empty => {
                *self = BinaryTree::new(new_value);
            }
            BinaryTree::Node { left, .. } => {
                *left = Box::new(BinaryTree::new(new_value));
            }
        }
    }

    pub fn insert_right(&mut self, new_value: T) {
        match self {
            BinaryTree::Empty => {
                *self = BinaryTree::new(new_value);
            }
            BinaryTree::Node { right, .. } => {
                *right = Box::new(BinaryTree::new(new_value));
            }
        }
    }

    pub fn size(&self) -> usize {
        match self {
            BinaryTree::Empty => 0,
            BinaryTree::Node { left, right, .. } => {
                1 + left.size() + right.size()
            }
        }
    }

    pub fn height(&self) -> usize {
        match self {
            BinaryTree::Empty => 0,
            BinaryTree::Node { left, right, .. } => {
                1 + std::cmp::max(left.height(), right.height())
            }
        }
    }

    pub fn inorder_traversal(&self, result: &mut Vec<T>) {
        match self {
            BinaryTree::Empty => {}
            BinaryTree::Node { value, left, right } => {
                left.inorder_traversal(result);
                result.push(value.clone());
                right.inorder_traversal(result);
            }
        }
    }
}

/// 列表类型：另一个递归类型示例
#[derive(Debug, Clone, PartialEq)]
pub enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

impl<T: Clone> List<T> {
    pub fn new() -> Self {
        List::Nil
    }

    pub fn cons(head: T, tail: Self) -> Self {
        List::Cons(head, Box::new(tail))
    }

    pub fn head(&self) -> Option<&T> {
        match self {
            List::Nil => Option::None,
            List::Cons(h, _) => Option::Some(h),
        }
    }

    pub fn tail(&self) -> Option<&List<T>> {
        match self {
            List::Nil => Option::None,
            List::Cons(_, t) => Option::Some(t),
        }
    }

    pub fn length(&self) -> usize {
        match self {
            List::Nil => 0,
            List::Cons(_, t) => 1 + t.length(),
        }
    }

    pub fn to_vec(&self) -> Vec<T> {
        let mut result = Vec::new();
        self.collect(&mut result);
        result
    }

    fn collect(&self, acc: &mut Vec<T>) {
        match self {
            List::Nil => {}
            List::Cons(h, t) => {
                acc.push(h.clone());
                t.collect(acc);
            }
        }
    }
}

impl<T: Clone> Default for List<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_point() {
        let mut p = Point::new(3.0, 4.0);
        assert_eq!(p.distance_from_origin(), 5.0);
        
        p.translate(1.0, 1.0);
        assert_eq!(p.x, 4.0);
        assert_eq!(p.y, 5.0);
    }

    #[test]
    fn test_option() {
        let some_value: Option<i32> = Option::Some(42);
        let none_value: Option<i32> = Option::None;

        assert!(some_value.is_some());
        assert!(none_value.is_none());
        assert_eq!(some_value.unwrap_or(0), 42);
        assert_eq!(none_value.unwrap_or(0), 0);

        let mapped = Option::Some(5).map(|x| x * 2);
        assert_eq!(mapped, Option::Some(10));
    }

    #[test]
    fn test_result() {
        let ok_result: Result<i32, &str> = Result::Ok(42);
        let err_result: Result<i32, &str> = Result::Err("error");

        assert!(ok_result.is_ok());
        assert!(err_result.is_err());
        assert_eq!(ok_result.unwrap_or(0), 42);
        assert_eq!(err_result.unwrap_or(0), 0);
    }

    #[test]
    fn test_binary_tree() {
        let mut tree = BinaryTree::new(10);
        tree.insert_left(5);
        tree.insert_right(15);

        assert_eq!(tree.size(), 3);
        assert_eq!(tree.height(), 2);

        let mut traversal = Vec::new();
        tree.inorder_traversal(&mut traversal);
        assert_eq!(traversal, vec![5, 10, 15]);
    }

    #[test]
    fn test_list() {
        let list = List::cons(1, List::cons(2, List::cons(3, List::new())));
        assert_eq!(list.length(), 3);
        assert_eq!(list.head(), Option::Some(&1));
        assert_eq!(list.to_vec(), vec![1, 2, 3]);
    }
}
