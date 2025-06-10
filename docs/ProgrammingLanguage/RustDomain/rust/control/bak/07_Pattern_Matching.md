# 模式匹配

在 Rust 中，模式匹配（Pattern Matching）是一种强大的控制流结构，它允许你检查数据的结构，并根据数据的不同形式（模式）来执行不同的代码。
模式匹配最常用于 `match` 表达式，但也可以在其他上下文中使用，比如 `if let` 和 `while let` 表达式。

## 定义

模式匹配的模式可以是：

- 具体的值（如 `1`、`"hello"`）
- 变量名（如 `x`）
- 通配符 `_`，它匹配任何值，通常用于忽略某些分支
- 解构模式，它可以将复合数据类型（如元组、结构体、枚举）分解为其组成部分
- 范围模式，用于匹配一个值是否在某个范围内
- 守卫（Guard），一个模式后面跟着一个 `if` 语句，用于进一步细化模式匹配的条件

## 使用

以下是一些模式匹配的使用示例：

### `match` 表达式

`match` 是 Rust 中最常用的模式匹配结构，它允许你将一个值与多个模式进行比较，并执行相应的代码块。

```rust
let x = 4;

match x {
    1 => println!("One"),
    2 => println!("Two"),
    3..=5 => println!("Three to Five"),
    _ => println!("Something else"),
}
```

### 解构模式

你可以使用模式匹配来解构元组、结构体等复合类型。

```rust
let point = (3, 5);

match point {
    (x, y) if x > y => println!("x is greater than y"),
    (x, y) if x < y => println!("y is greater than x"),
    _ => println!("It's a tie"),
}
```

### `if let` 表达式

`if let` 用于简化只关心一个模式的 `match` 表达式。

```rust
let some_value = Some(10);

if let Some(x) = some_value {
    println!("The value is: {}", x);
}
```

### `while let` 表达式

`while let` 用于在某个模式匹配成功时循环执行代码。

```rust
let mut optional_value: Option<i32> = Some(10);

while let Some(x) = optional_value {
    println!("The value is: {}", x);
    optional_value = None; // Break the loop
}
```

### 范围模式

你可以使用 `..=` 和 `..` 来定义范围模式。

```rust
let num = 7;

match num {
    1..=5 => println!("It's between 1 and 5"),
    6..=10 => println!("It's between 6 and 10"),
    _ => println!("It's out of the range"),
}
```

模式匹配是 Rust 编程中非常强大和灵活的工具，它不仅可以提高代码的可读性，还可以在编译时提供类型安全保证。
