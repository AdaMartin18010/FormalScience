//! 函数类型示例

use type_checker::ast::{utils::*, *};
use type_checker::type_checker::{check, print_errors};

fn main() {
    println!("=== 函数类型示例 ===\n");

    // 示例 1: 简单的加法函数
    let program1 = vec![
        Decl::Fun {
            name: "add".to_string(),
            generics: vec![],
            params: vec![
                ("a".to_string(), Type::Int),
                ("b".to_string(), Type::Int),
            ],
            ret_type: Type::Int,
            body: Expr::Block(vec![
                binop(BinOperator::Add, var("a"), var("b"))
            ]),
        },
        let_decl("sum", call(var("add"), vec![int(3), int(4)])),
    ];

    println!("示例 1: 简单加法函数");
    match check(&program1) {
        Ok(()) => println!("✓ 类型检查通过: add: (Int, Int) -> Int\n"),
        Err(errors) => print_errors(&errors),
    }

    // 示例 2: 多参数函数
    let program2 = vec![
        Decl::Fun {
            name: "max3".to_string(),
            generics: vec![],
            params: vec![
                ("a".to_string(), Type::Int),
                ("b".to_string(), Type::Int),
                ("c".to_string(), Type::Int),
            ],
            ret_type: Type::Int,
            body: Expr::If {
                cond: Box::new(binop(BinOperator::And,
                    binop(BinOperator::Ge, var("a"), var("b")),
                    binop(BinOperator::Ge, var("a"), var("c"))
                )),
                then_branch: Box::new(var("a")),
                else_branch: Box::new(Expr::If {
                    cond: Box::new(binop(BinOperator::Ge, var("b"), var("c"))),
                    then_branch: Box::new(var("b")),
                    else_branch: Box::new(var("c")),
                }),
            },
        },
        let_decl("m", call(var("max3"), vec![int(1), int(5), int(3)])),
    ];

    println!("示例 2: 三数最大值函数");
    match check(&program2) {
        Ok(()) => println!("✓ 类型检查通过: max3: (Int, Int, Int) -> Int\n"),
        Err(errors) => print_errors(&errors),
    }

    // 示例 3: 高阶函数（函数作为参数）
    let program3 = vec![
        // 定义 apply 函数
        Decl::Fun {
            name: "apply".to_string(),
            generics: vec![],
            params: vec![
                ("f".to_string(), Type::fun(vec![Type::Int], Type::Int)),
                ("x".to_string(), Type::Int),
            ],
            ret_type: Type::Int,
            body: call(var("f"), vec![var("x")]),
        },
        // 定义 double 函数
        Decl::Fun {
            name: "double".to_string(),
            generics: vec![],
            params: vec![("n".to_string(), Type::Int)],
            ret_type: Type::Int,
            body: binop(BinOperator::Mul, var("n"), int(2)),
        },
        // 使用高阶函数
        let_decl("result", call(var("apply"), vec![var("double"), int(5)])),
    ];

    println!("示例 3: 高阶函数");
    match check(&program3) {
        Ok(()) => println!("✓ 类型检查通过: apply: ((Int) -> Int, Int) -> Int\n"),
        Err(errors) => print_errors(&errors),
    }

    // 示例 4: 参数类型不匹配错误
    let program4 = vec![
        Decl::Fun {
            name: "foo".to_string(),
            generics: vec![],
            params: vec![("x".to_string(), Type::Int)],
            ret_type: Type::Int,
            body: var("x"),
        },
        // 错误：传递 Bool 给期望 Int 的函数
        let_decl("err", call(var("foo"), vec![bool(true)])),
    ];

    println!("示例 4: 参数类型不匹配错误");
    match check(&program4) {
        Ok(()) => println!("✓ 类型检查通过\n"),
        Err(errors) => {
            println!("✗ 发现类型错误（预期）:");
            print_errors(&errors);
            println!();
        }
    }

    // 示例 5: 参数数量不匹配错误
    let program5 = vec![
        Decl::Fun {
            name: "bar".to_string(),
            generics: vec![],
            params: vec![
                ("a".to_string(), Type::Int),
                ("b".to_string(), Type::Int),
            ],
            ret_type: Type::Int,
            body: binop(BinOperator::Add, var("a"), var("b")),
        },
        // 错误：只传递一个参数
        let_decl("err", call(var("bar"), vec![int(1)])),
    ];

    println!("示例 5: 参数数量不匹配错误");
    match check(&program5) {
        Ok(()) => println!("✓ 类型检查通过\n"),
        Err(errors) => {
            println!("✗ 发现类型错误（预期）:");
            print_errors(&errors);
            println!();
        }
    }

    println!("=== 所有示例完成 ===");
}
