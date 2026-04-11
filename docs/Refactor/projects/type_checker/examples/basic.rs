//! 基础类型检查示例

use type_checker::ast::{utils::*, *};
use type_checker::type_checker::{check, print_errors};

fn main() {
    println!("=== 基础类型检查示例 ===\n");

    // 示例 1: 简单的变量声明
    let program1 = vec![
        let_decl("x", int(42)),
        let_decl("y", bool(true)),
        let_decl("z", string("hello")),
    ];

    println!("示例 1: 变量声明");
    match check(&program1) {
        Ok(()) => println!("✓ 类型检查通过\n"),
        Err(errors) => print_errors(&errors),
    }

    // 示例 2: 算术表达式
    let program2 = vec![
        let_decl("a", binop(BinOperator::Add, int(1), int(2))),
        let_decl("b", binop(BinOperator::Mul, int(3), int(4))),
        let_decl("c", binop(BinOperator::Sub, var("a"), var("b"))),
    ];

    println!("示例 2: 算术表达式");
    match check(&program2) {
        Ok(()) => println!("✓ 类型检查通过\n"),
        Err(errors) => print_errors(&errors),
    }

    // 示例 3: 比较表达式
    let program3 = vec![
        let_decl("p", binop(BinOperator::Lt, int(1), int(2))),
        let_decl("q", binop(BinOperator::And, bool(true), var("p"))),
        let_decl("r", binop(BinOperator::Or, var("p"), var("q"))),
    ];

    println!("示例 3: 比较和逻辑表达式");
    match check(&program3) {
        Ok(()) => println!("✓ 类型检查通过\n"),
        Err(errors) => print_errors(&errors),
    }

    // 示例 4: 类型不匹配错误
    let program4 = vec![
        Decl::Let {
            name: "err".to_string(),
            ty: Some(Type::Int),
            value: bool(false), // 类型不匹配！
        },
    ];

    println!("示例 4: 类型不匹配错误");
    match check(&program4) {
        Ok(()) => println!("✓ 类型检查通过\n"),
        Err(errors) => {
            println!("✗ 发现类型错误（预期）:");
            print_errors(&errors);
            println!();
        }
    }

    // 示例 5: 数组
    let program5 = vec![
        Decl::Let {
            name: "arr".to_string(),
            ty: None,
            value: Expr::Array(vec![int(1), int(2), int(3)]),
        },
        Decl::Let {
            name: "first".to_string(),
            ty: Some(Type::Int),
            value: Expr::Index {
                expr: Box::new(var("arr")),
                index: Box::new(int(0)),
            },
        },
    ];

    println!("示例 5: 数组");
    match check(&program5) {
        Ok(()) => println!("✓ 类型检查通过\n"),
        Err(errors) => print_errors(&errors),
    }

    println!("=== 所有示例完成 ===");
}
