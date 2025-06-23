# Rust 语言基础

## 目录

- [Rust 语言基础](#rust-语言基础)
  - [目录](#目录)
  - [1. 基本语法结构](#1-基本语法结构)
    - [1.1 Items](#11-items)
      - [1.1 示例](#11-示例)
    - [2. 表达式（Expressions）](#2-表达式expressions)
      - [2.1 示例](#21-示例)
    - [3. 语句（Statements）](#3-语句statements)
      - [3.1 示例](#31-示例)
    - [4. 控制流](#4-控制流)
      - [4.1 条件语句](#41-条件语句)
      - [4.1.1 示例](#411-示例)
      - [4.2 循环](#42-循环)
      - [4.2.1 示例](#421-示例)
    - [5. 模块和作用域](#5-模块和作用域)
      - [5.1 示例](#51-示例)
    - [6. 错误处理](#6-错误处理)
      - [6.1 `panic!`](#61-panic)
      - [6.1.1 示例](#611-示例)
      - [6.2 `Result`](#62-result)
      - [6.2.1 示例](#621-示例)
    - [7. 所有权、借用和生命周期](#7-所有权借用和生命周期)
      - [7.1 示例](#71-示例)
    - [8. 特征（Traits）](#8-特征traits)
      - [8.1 示例](#81-示例)
    - [9. 泛型](#9-泛型)
      - [9.1 示例](#91-示例)
    - [总结](#总结)

在 Rust 中，语法和语义结构是理解语言的基础。
以下是对 Rust 语法和语义结构的完整梳理，包括定义和解释。

## 1. 基本语法结构

### 1.1 Items

- **定义**：Items 是 Rust 代码的基本构建块，通常指在模块、函数或其他作用域中定义的元素。
- **类型**：
  - **函数**：使用 `fn` 关键字定义的函数。
  - **结构体**：使用 `struct` 关键字定义的数据结构。
  - **枚举**：使用 `enum` 关键字定义的枚举类型。
  - **特征**：使用 `trait` 关键字定义的特征。
  - **模块**：使用 `mod` 关键字定义的模块。
  - **常量**：使用 `const` 或 `static` 关键字定义的常量。

#### 1.1 示例

```rust
// 结构体定义
struct Point {
    x: i32,
    y: i32,
}

// 函数定义
fn add(a: i32, b: i32) -> i32 {
    a + b
}

// 常量定义
const PI: f64 = 3.14159;
```

### 2. 表达式（Expressions）

- **定义**：表达式是计算并返回值的代码片段。它们可以是简单的值、变量、函数调用、运算符等。
- **特点**：
  - 表达式可以嵌套。
  - 所有函数体的最后一行都是一个表达式，返回该表达式的值。

#### 2.1 示例

```rust
let x = 5; // 赋值表达式
let y = x + 2; // 计算表达式
let z = add(x, y); // 函数调用表达式
```

### 3. 语句（Statements）

- **定义**：语句是执行某种操作的代码片段，但不返回值。它们通常用于控制流、变量声明、函数调用等。
- **特点**：
  - 语句通常以分号结束。
  - 语句的最后一部分可以是一个表达式，但整个语句本身不返回值。

#### 3.1 示例

```rust
let x = 5; // 变量声明语句
let y = 10; // 变量声明语句
let sum = add(x, y); // 函数调用语句
```

### 4. 控制流

Rust 提供了多种控制流结构，用于控制程序的执行顺序。

#### 4.1 条件语句

- **定义**：使用 `if`、`else if` 和 `else` 关键字进行条件判断。
  
#### 4.1.1 示例

```rust
if x > y {
    println!("x is greater than y");
} else if x < y {
    println!("x is less than y");
} else {
    println!("x is equal to y");
}
```

#### 4.2 循环

- **定义**：使用 `loop`、`while` 和 `for` 关键字进行循环。

#### 4.2.1 示例

```rust
// loop
let mut count = 0;
loop {
    count += 1;
    if count == 5 {
        break;
    }
}

// while
while count < 10 {
    count += 1;
}

// for
for i in 0..5 {
    println!("{}", i);
}
```

### 5. 模块和作用域

- **定义**：模块用于组织代码，使用 `mod` 关键字定义。模块可以包含其他模块、函数、结构体等。
- **作用域**：Rust 使用块作用域来限制变量的可见性。

#### 5.1 示例

```rust
mod my_module {
    pub fn my_function() {
        println!("Hello from my_module!");
    }
}

fn main() {
    my_module::my_function(); // 调用模块中的函数
}
```

### 6. 错误处理

Rust 提供了两种主要的错误处理机制：`panic!` 和 `Result`。

#### 6.1 `panic!`

- **定义**：用于处理不可恢复的错误，导致程序崩溃。

#### 6.1.1 示例

```rust
fn main() {
    panic!("This is a panic!");
}
```

#### 6.2 `Result`

- **定义**：用于处理可恢复的错误，返回 `Ok` 或 `Err`。

#### 6.2.1 示例

```rust
fn divide(a: i32, b: i32) -> Result<i32, String> {
    if b == 0 {
        Err(String::from("Cannot divide by zero"))
    } else {
        Ok(a / b)
    }
}

fn main() {
    match divide(10, 0) {
        Ok(result) => println!("Result: {}", result),
        Err(e) => println!("Error: {}", e),
    }
}
```

### 7. 所有权、借用和生命周期

- **所有权**：Rust 的核心特性，确保每个值都有一个唯一的所有者。
- **借用**：允许通过引用访问值，而不获取所有权。分为可变借用和不可变借用。
- **生命周期**：用于标注引用的有效范围，确保引用在有效范围内。

#### 7.1 示例

```rust
fn borrow_example(s: &String) {
    println!("{}", s);
}

fn main() {
    let s = String::from("Hello");
    borrow_example(&s); // 借用
}
```

### 8. 特征（Traits）

- **定义**：特征是 Rust 中的一种抽象机制，定义了一组方法的接口。类型可以实现这些特征。
  
#### 8.1 示例

```rust
trait Shape {
    fn area(&self) -> f64;
}

struct Circle {
    radius: f64,
}

impl Shape for Circle {
    fn area(&self) -> f64 {
        std::f64::consts::PI * self.radius * self.radius
    }
}
```

### 9. 泛型

- **定义**：允许在定义函数、结构体或特征时使用类型参数，提供代码的重用性和灵活性。

#### 9.1 示例

```rust
fn generic_function<T>(value: T) {
    // 使用泛型类型 T
}

struct GenericStruct<T> {
    value: T,
}
```

### 总结

Rust 的语法和语义结构包括：

- **Items**：函数、结构体、枚举、特征等的定义。
- **Expressions**：计算并返回值的代码片段。
- **Statements**：执行操作但不返回值的代码片段。
- **控制流**：条件语句和循环。
- **模块和作用域**：组织代码和限制变量的可见性。
- **错误处理**：使用 `panic!` 和 `Result` 处理错误。
- **所有权、借用和生命周期**：确保内存安全和数据一致性。
- **特征**：定义方法的接口。
- **泛型**：提供代码的重用性和灵活性。

这些结构共同构成了 Rust 的语言特性，使得 Rust 在内存安全、并发编程和性能方面具有显著优势。
