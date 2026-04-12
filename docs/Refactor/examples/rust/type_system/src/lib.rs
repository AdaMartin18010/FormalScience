//! # 类型系统实现
//! 
//! 本模块实现了形式语言中的类型系统概念，包括：
//! - 代数数据类型 (Algebraic Data Types)
//! - 简单类型 lambda 演算
//! - 线性类型系统
//! - 类型推导算法 (Hindley-Milner)

pub mod adt;
pub mod linear_types;
pub mod type_checker;
pub mod lambda_calculus;
