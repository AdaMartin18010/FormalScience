//! 泛型类型示例

use type_checker::ast::{utils::*, *};
use type_checker::type_checker::{check, print_errors};

fn main() {
    println!("=== 泛型类型示例 ===\n");

    // 示例 1: 恒等函数（泛型）
    // 注意：这是一个简化版的泛型示例
    // 实际的泛型实现需要更复杂的类型推断系统
    let program1 = vec![
        // 定义 Int 版本的恒等函数
        Decl::Fun {
            name: "identity_int".to_string(),
            generics: vec![],
            params: vec![("x".to_string(), Type::Int)],
            ret_type: Type::Int,
            body: var("x"),
        },
        // 定义 Bool 版本的恒等函数
        Decl::Fun {
            name: "identity_bool".to_string(),
            generics: vec![],
            params: vec![("x".to_string(), Type::Bool)],
            ret_type: Type::Bool,
            body: var("x"),
        },
        // 使用
        let_decl("a", call(var("identity_int"), vec![int(42)])),
        let_decl("b", call(var("identity_bool"), vec![bool(true)])),
    ];

    println!("示例 1: 类型特定的恒等函数");
    match check(&program1) {
        Ok(()) => println!("✓ 类型检查通过"),
        Err(errors) => print_errors(&errors),
    }

    // 示例 2: 使用类型变量
    let program2 = vec![
        // 使用类型变量 T 的函数
        Decl::Fun {
            name: "first".to_string(),
            generics: vec!["T".to_string()],
            params: vec![
                ("a".to_string(), Type::Var("T".to_string())),
                ("b".to_string(), Type::Var("T".to_string())),
            ],
            ret_type: Type::Var("T".to_string()),
            body: var("a"),
        },
        // 使用 Int 实例化
        let_decl("x", call(var("first"), vec![int(1), int(2)])),
    ];

    println!("\n示例 2: 带类型变量的函数");
    match check(&program2) {
        Ok(()) => println!("✓ 类型检查通过"),
        Err(errors) => print_errors(&errors),
    }

    // 示例 3: 泛型数据结构 - 包装器类型
    let program3 = vec![
        // Box 类型构造器
        Decl::TypeAlias {
            name: "IntBox".to_string(),
            ty: Type::Record({
                let mut fields = std::collections::HashMap::new();
                fields.insert("value".to_string(), Type::Int);
                fields
            }),
        },
        // 创建 Box 的函数
        Decl::Fun {
            name: "make_box".to_string(),
            generics: vec![],
            params: vec![("v".to_string(), Type::Int)],
            ret_type: Type::Var("IntBox".to_string()),
            body: Expr::Record({
                let mut fields = std::collections::HashMap::new();
                fields.insert("value".to_string(), var("v"));
                fields
            }),
        },
        // 解包函数
        Decl::Fun {
            name: "unbox".to_string(),
            generics: vec![],
            params: vec![("b".to_string(), Type::Var("IntBox".to_string()))],
            ret_type: Type::Int,
            body: Expr::FieldAccess {
                expr: Box::new(var("b")),
                field: "value".to_string(),
            },
        },
        // 使用
        let_decl("my_box", call(var("make_box"), vec![int(42)])),
        let_decl("inner", call(var("unbox"), vec![var("my_box")])),
    ];

    println!("\n示例 3: 泛型数据结构");
    match check(&program3) {
        Ok(()) => println!("✓ 类型检查通过"),
        Err(errors) => print_errors(&errors),
    }

    // 示例 4: 泛型数组操作
    let program4 = vec![
        // 数组长度函数
        Decl::Fun {
            name: "length_int".to_string(),
            generics: vec![],
            params: vec![("arr".to_string(), Type::array(Type::Int))],
            ret_type: Type::Int,
            body: int(0), // 简化实现
        },
        // 数组映射函数（Int -> Int）
        Decl::Fun {
            name: "map_int".to_string(),
            generics: vec![],
            params: vec![
                ("arr".to_string(), Type::array(Type::Int)),
                ("f".to_string(), Type::fun(vec![Type::Int], Type::Int)),
            ],
            ret_type: Type::array(Type::Int),
            body: Expr::Array(vec![]), // 简化实现
        },
        // 使用
        Decl::Let {
            name: "nums".to_string(),
            ty: None,
            value: Expr::Array(vec![int(1), int(2), int(3)]),
        },
        Decl::Fun {
            name: "inc".to_string(),
            generics: vec![],
            params: vec![("n".to_string(), Type::Int)],
            ret_type: Type::Int,
            body: binop(BinOperator::Add, var("n"), int(1)),
        },
        let_decl("mapped", call(var("map_int"), vec![var("nums"), var("inc")])),
    ];

    println!("\n示例 4: 泛型数组操作");
    match check(&program4) {
        Ok(()) => println!("✓ 类型检查通过"),
        Err(errors) => print_errors(&errors),
    }

    // 示例 5: 类型不匹配
    let program5 = vec![
        Decl::Fun {
            name: "pair".to_string(),
            generics: vec!["T".to_string()],
            params: vec![
                ("a".to_string(), Type::Var("T".to_string())),
                ("b".to_string(), Type::Var("T".to_string())),
            ],
            ret_type: Type::Tuple(vec![Type::Var("T".to_string()), Type::Var("T".to_string())]),
            body: Expr::Tuple(vec![var("a"), var("b")]),
        },
        // 错误：传递不同类型
        let_decl("p", call(var("pair"), vec![int(1), bool(true)])),
    ];

    println!("\n示例 5: 泛型类型约束错误");
    match check(&program5) {
        Ok(()) => println!("✓ 类型检查通过"),
        Err(errors) => {
            println!("✗ 发现类型错误（预期）:");
            print_errors(&errors);
        }
    }

    println!("\n=== 所有示例完成 ===");
    println!("\n注意：这是一个简化版的泛型系统。");
    println!("完整的泛型实现需要更复杂的类型推断和统一算法。");
}
