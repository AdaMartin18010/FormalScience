//! Type Checker
//! 
//! 一个简单但完整的类型检查器，支持基础类型、函数类型、泛型和结构化类型。

mod ast;
mod parser;
mod type_checker;

use ast::{utils::*, *};
use type_checker::{check, print_errors, TypeChecker, TypeError};

fn main() {
    print_banner();
    
    // 示例 1: 基础类型检查
    println!("\n{:=^60}", " 示例 1: 基础类型检查 ");
    demo_basic_types();
    
    // 示例 2: 函数类型检查
    println!("\n{:=^60}", " 示例 2: 函数类型检查 ");
    demo_function_types();
    
    // 示例 3: 条件表达式
    println!("\n{:=^60}", " 示例 3: 条件表达式 ");
    demo_conditionals();
    
    // 示例 4: 类型错误
    println!("\n{:=^60}", " 示例 4: 类型错误检测 ");
    demo_type_errors();
    
    // 示例 5: 复杂程序
    println!("\n{:=^60}", " 示例 5: 复杂程序 ");
    demo_complex_program();
    
    // 示例 6: 解析和检查源代码
    println!("\n{:=^60}", " 示例 6: 解析源代码 ");
    demo_parsing();
    
    println!("\n{:=^60}", "");
    println!("{:^60}", "所有演示完成！");
    println!("{:=^60}\n", "");
}

fn print_banner() {
    println!("\n{:=^60}", "");
    println!("{:^60}", "Type Checker");
    println!("{:^60}", "Rust 实现的类型检查器");
    println!("{:=^60}\n", "");
}

/// 演示基础类型检查
fn demo_basic_types() {
    let mut checker = TypeChecker::new();
    
    // 测试基本类型
    let exprs = vec![
        ("整数 42", int(42), Type::Int),
        ("布尔 true", bool(true), Type::Bool),
        ("字符串 \"hello\"", string("hello"), Type::String),
        ("单位值", Expr::Unit, Type::Unit),
    ];
    
    for (desc, expr, expected) in &exprs {
        match checker.check_expr(expr) {
            Ok(ty) => {
                let status = if ty == *expected { "✓" } else { "✗" };
                println!("{} {}: {} (期望: {}, 实际: {})", 
                    status, desc, if ty == *expected { "类型正确" } else { "类型错误" }, 
                    expected, ty);
            }
            Err(e) => {
                println!("✗ {}: 错误 - {}", desc, e);
            }
        }
    }
}

/// 演示函数类型检查
fn demo_function_types() {
    let program = vec![
        // 定义 add 函数
        Decl::Fun {
            name: "add".to_string(),
            generics: vec![],
            params: vec![
                ("x".to_string(), Type::Int),
                ("y".to_string(), Type::Int),
            ],
            ret_type: Type::Int,
            body: Expr::Block(vec![
                binop(BinOperator::Add, var("x"), var("y"))
            ]),
        },
        // 定义使用 add 的变量
        Decl::Let {
            name: "result".to_string(),
            ty: Some(Type::Int),
            value: call(var("add"), vec![int(3), int(4)]),
        },
    ];
    
    match check(&program) {
        Ok(()) => {
            println!("✓ 函数类型检查通过");
            println!("  - 定义了 add: (Int, Int) -> Int");
            println!("  - 调用 add(3, 4): Int ✓");
        }
        Err(errors) => {
            println!("✗ 类型检查失败:");
            print_errors(&errors);
        }
    }
}

/// 演示条件表达式
fn demo_conditionals() {
    let mut checker = TypeChecker::new();
    
    // 正确的条件表达式
    let valid_if = Expr::If {
        cond: Box::new(binop(BinOperator::Gt, int(10), int(5))),
        then_branch: Box::new(int(1)),
        else_branch: Box::new(int(0)),
    };
    
    match checker.check_expr(&valid_if) {
        Ok(ty) => println!("✓ 正确的 if 表达式: {}", ty),
        Err(e) => println!("✗ 错误: {}", e),
    }
    
    // 错误的条件表达式（条件不是 Bool）
    let invalid_cond = Expr::If {
        cond: Box::new(int(1)),
        then_branch: Box::new(int(1)),
        else_branch: Box::new(int(0)),
    };
    
    match checker.check_expr(&invalid_cond) {
        Ok(ty) => println!("? 意外成功: {}", ty),
        Err(e) => println!("✓ 正确检测到错误: {}", e),
    }
    
    // 分支类型不匹配
    let mismatched_branches = Expr::If {
        cond: Box::new(bool(true)),
        then_branch: Box::new(int(1)),
        else_branch: Box::new(bool(false)),
    };
    
    match checker.check_expr(&mismatched_branches) {
        Ok(ty) => println!("? 意外成功: {}", ty),
        Err(e) => println!("✓ 正确检测到错误: {}", e),
    }
}

/// 演示类型错误检测
fn demo_type_errors() {
    let mut checker = TypeChecker::new();
    
    let error_cases = vec![
        ("Int + Bool", binop(BinOperator::Add, int(1), bool(true))),
        ("Bool && Int", binop(BinOperator::And, bool(true), int(1))),
        ("!Int", Expr::UnOp { op: UnOperator::Not, operand: Box::new(int(1)) }),
        ("-Bool", Expr::UnOp { op: UnOperator::Neg, operand: Box::new(bool(true)) }),
    ];
    
    for (desc, expr) in &error_cases {
        match checker.check_expr(expr) {
            Ok(ty) => println!("? {}: 意外成功 - {}", desc, ty),
            Err(_) => println!("✓ {}: 正确检测到类型错误", desc),
        }
    }
}

/// 演示复杂程序
fn demo_complex_program() {
    let program = vec![
        // 定义计算阶乘的函数
        Decl::Fun {
            name: "factorial".to_string(),
            generics: vec![],
            params: vec![("n".to_string(), Type::Int)],
            ret_type: Type::Int,
            body: Expr::If {
                cond: Box::new(binop(BinOperator::Le, var("n"), int(1))),
                then_branch: Box::new(int(1)),
                else_branch: Box::new(binop(
                    BinOperator::Mul,
                    var("n"),
                    call(var("factorial"), vec![binop(BinOperator::Sub, var("n"), int(1))])
                )),
            },
        },
        // 计算 5!
        Decl::Let {
            name: "fact5".to_string(),
            ty: Some(Type::Int),
            value: call(var("factorial"), vec![int(5)]),
        },
    ];
    
    match check(&program) {
        Ok(()) => {
            println!("✓ 阶乘函数类型检查通过");
            println!("  - factorial: (Int) -> Int");
            println!("  - factorial(5): Int ✓");
        }
        Err(errors) => {
            println!("✗ 类型检查失败:");
            print_errors(&errors);
        }
    }
}

/// 演示解析源代码
fn demo_parsing() {
    let source = r#"
// 定义常量
let x: Int = 42
let y: Bool = true

// 定义函数
fn add(a: Int, b: Int) -> Int {
    a + b
}

// 使用函数
let sum = add(x, 10)

// 条件表达式
let max = if x > 0 then x else 0
"#;

    println!("源代码:");
    println!("{}", source);
    println!("\n解析结果:");

    match parser::parse(source) {
        Ok(program) => {
            println!("✓ 解析成功，共 {} 个声明", program.len());
            
            for (i, decl) in program.iter().enumerate() {
                match decl {
                    Decl::Let { name, ty, .. } => {
                        let type_str = ty.as_ref().map(|t| format!("{}", t))
                            .unwrap_or_else(|| "<推断>".to_string());
                        println!("  [{}] let {}: {}", i + 1, name, type_str);
                    }
                    Decl::Fun { name, params, ret_type, .. } => {
                        let params_str: Vec<String> = params.iter()
                            .map(|(n, t)| format!("{}: {}", n, t))
                            .collect();
                        println!("  [{}] fn {}({}) -> {}", 
                            i + 1, name, params_str.join(", "), ret_type);
                    }
                    _ => {}
                }
            }
            
            // 类型检查
            println!("\n类型检查:");
            match check(&program) {
                Ok(()) => println!("✓ 类型检查通过！"),
                Err(errors) => {
                    println!("✗ 发现 {} 个类型错误:", errors.len());
                    print_errors(&errors);
                }
            }
        }
        Err(e) => {
            println!("✗ 解析错误: {}", e);
        }
    }
}


