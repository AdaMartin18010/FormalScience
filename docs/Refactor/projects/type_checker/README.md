# Type Checker - 类型检查器

一个用 Rust 实现的简单类型检查器，支持基础类型、函数类型、泛型和结构化类型。

## 支持的类型系统

### 基础类型

- `Int` - 整数类型
- `Bool` - 布尔类型
- `String` - 字符串类型
- `Unit` - 单位类型（void）

### 复合类型

- `Function` - 函数类型（参数类型 → 返回类型）
- `Array` - 数组类型
- `Tuple` - 元组类型
- `Record` - 记录类型（结构体）
- `Variant` - 变体类型（枚举）

### 高级特性

- `Generic` - 泛型类型参数
- `TypeVariable` - 类型变量（用于类型推断）
- `Constrained` - 约束类型

## 项目结构

```
type_checker/
├── Cargo.toml
├── README.md
├── src/
│   ├── main.rs          # 程序入口
│   ├── ast.rs           # AST定义
│   ├── parser.rs        # 递归下降解析器
│   └── type_checker.rs  # 类型检查实现
└── examples/
    ├── basic.tc         # 基础类型检查示例
    ├── function.tc      # 函数类型示例
    └── generic.tc       # 泛型示例
```

## 编译运行

```bash
# 编译
cargo build --release

# 运行
cargo run

# 运行测试
cargo test

# 运行示例
cargo run --example basic
cargo run --example function
cargo run --example generic
```

## 示例语言语法

```rust
// 变量声明
let x: Int = 42;
let y: Bool = true;

// 函数定义
fn add(a: Int, b: Int) -> Int {
    a + b
}

// 条件表达式
let max = if x > 0 { x } else { 0 };

// 函数应用
let result = add(x, 10);

// 泛型函数
fn identity<T>(x: T) -> T {
    x
}

// 记录类型
type Point = { x: Int, y: Int };
let p: Point = { x = 10, y = 20 };
```

## 类型检查规则

- **变量使用**：变量必须先声明后使用
- **类型一致性**：赋值和返回必须类型匹配
- **函数调用**：实参类型必须与形参类型匹配
- **条件分支**：if 的两个分支必须返回相同类型
- **泛型实例化**：泛型函数调用时需要正确的类型参数

## 错误报告

类型检查器会提供详细的错误信息，包括：

- 错误类型（类型不匹配、未定义变量等）
- 位置信息（行号、列号）
- 期望类型和实际类型

## 许可证

MIT License
