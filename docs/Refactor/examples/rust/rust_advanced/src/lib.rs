//! # Rust 高级特性
//! 
//! 本模块展示 Rust 的高级特性，包括：
//! - Trait 系统和泛型编程
//! - 生命周期和借用检查器
//! - 类型级编程
//! - 零成本抽象

pub mod traits;
pub mod lifetimes;
pub mod zero_cost;

pub use traits::*;
pub use lifetimes::*;
pub use zero_cost::*;
