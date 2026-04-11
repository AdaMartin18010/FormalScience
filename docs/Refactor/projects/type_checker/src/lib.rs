//! Type Checker Library
//! 
//! 一个简单但完整的类型检查器库，支持基础类型、函数类型、泛型和结构化类型。

pub mod ast;
pub mod parser;
pub mod type_checker;

// 重新导出常用类型
pub use ast::{
    Decl, Expr, Program,
    Type,
    BinOperator, UnOperator,
    Position, Located,
    utils as ast_utils,
};
pub use parser::parse;
pub use type_checker::{
    TypeChecker, TypeEnv, TypeError, TypeCheckResult,
    check, print_errors,
};
