# Rust 类型系统相关概念

## 目录

- [Rust 类型系统相关概念](#rust-类型系统相关概念)
  - [目录](#目录)
  - [1. impl 可以实现的类型方法](#1-impl-可以实现的类型方法)
    - [2. trait（特征）和泛型的关系](#2-trait特征和泛型的关系)
    - [3. 类型组合的方式](#3-类型组合的方式)

## 1. impl 可以实现的类型方法

```rust
// 1. 为结构体实现方法
struct Point {
    x: f64,
    y: f64,
}

impl Point {
    // 构造函数
    fn new(x: f64, y: f64) -> Point {
        Point { x, y }
    }
    
    // 实例方法
    fn distance(&self) -> f64 {
        (self.x.powi(2) + self.y.powi(2)).sqrt()
    }
}

// 2. 为枚举实现方法
enum Message {
    Quit,
    Move { x: i32, y: i32 },
    Write(String),
}

impl Message {
    fn call(&self) {
        match self {
            Message::Quit => println!("退出"),
            Message::Move { x, y } => println!("移动到 ({}, {})", x, y),
            Message::Write(text) => println!("文本消息: {}", text),
        }
    }
}
```

### 2. trait（特征）和泛型的关系

```rust
// 1. 定义一个trait
trait Display {
    fn display(&self) -> String;
}

// 2. 为具体类型实现trait
struct Person {
    name: String,
    age: u32,
}

impl Display for Person {
    fn display(&self) -> String {
        format!("姓名: {}, 年龄: {}", self.name, self.age)
    }
}

// 3. 使用特征约束的泛型函数
fn print_item<T: Display>(item: T) {
    println!("{}", item.display());
}

// 4. 多重特征约束
fn process<T>(item: T) 
where 
    T: Display + Clone,
{
    // 可以同时使用Display和Clone特征的方法
}
```

### 3. 类型组合的方式

```rust
// 1. 泛型结构体
struct Container<T> {
    value: T,
}

// 2. 泛型实现
impl<T> Container<T> {
    fn new(value: T) -> Self {
        Container { value }
    }
}

// 3. 特征约束的泛型实现
impl<T: Display> Container<T> {
    fn print(&self) {
        println!("容器内容: {}", self.value.display());
    }
}

// 4. 组合特征（trait组合）
trait Summary {
    fn summarize(&self) -> String;
}

trait Author {
    fn author(&self) -> String;
}

// 实现多个特征
struct Article {
    content: String,
    author_name: String,
}

impl Summary for Article {
    fn summarize(&self) -> String {
        format!("文章概要: {}", &self.content[..50])
    }
}

impl Author for Article {
    fn author(&self) -> String {
        self.author_name.clone()
    }
}
```

核心概念总结：

1. **impl 的使用场景**：
   - 为结构体实现方法
   - 为枚举实现方法
   - 实现特征(trait)
   - 为泛型类型实现方法

2. **trait 和泛型的关系**：
   - trait定义了类型的行为规范
   - 泛型通过trait约束来限制类型
   - 可以组合多个trait约束
   - 使用where子句来简化复杂的trait约束

3. **类型组合方式**：
   - 结构体组合（包含其他类型）
   - 枚举变体（不同类型的变体）
   - 泛型参数（类型参数化）
   - trait对象（动态分发）
   - trait约束（静态分发）

这些机制让Rust的类型系统非常强大，可以：

- 保证类型安全
- 实现代码复用
- 提供抽象能力
- 在编译时捕获错误
