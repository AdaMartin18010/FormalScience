# 函数

## 目录

- [函数](#函数)
  - [目录](#目录)
  - [函数声明 (Function Declaration)](#函数声明-function-declaration)
  - [函数定义 (Function Definition)](#函数定义-function-definition)
  - [函数实现 (Function Implementation)](#函数实现-function-implementation)
  - [抽象和默认实现](#抽象和默认实现)
  - [默认实现](#默认实现)
  - [分离定义和实现](#分离定义和实现)
  - [示例](#示例)
  - [普通函数](#普通函数)
  - [匿名函数](#匿名函数)
  - [闭包](#闭包)
  - [函数指针](#函数指针)
  - [高阶函数](#高阶函数)
  - [泛型函数](#泛型函数)
  - [可变参数函数](#可变参数函数)
  - [异步函数](#异步函数)

在 Rust 中，函数的声明、定义和实现是密切相关的概念，它们共同构成了 Rust 函数的完整描述。
以下是它们的区别和定义的解释：

## 函数声明 (Function Declaration)

函数声明是指声明函数的名称、参数列表和返回类型，但不提供函数体。
在 Rust 中，通常不需要单独声明函数，因为函数定义时会同时声明和实现。
然而，在某些情况下，例如当使用外部库或在模块中组织代码时，可能会先声明函数，然后在其他地方提供实现。

```rust
// 函数声明（在 Rust 中通常与定义一起完成）
fn add(a: i32, b: i32) -> i32;
```

## 函数定义 (Function Definition)

函数定义是声明和实现的组合。
它包括函数的名称、参数列表、返回类型以及函数体（即函数的代码块）。
在 Rust 中，当你定义一个函数时，你通常也会提供它的实现。

```rust
// 函数定义
fn add(a: i32, b: i32) -> i32 {
    a + b
}
```

## 函数实现 (Function Implementation)

函数实现是指提供函数体的过程，即编写实际执行的代码。
在 Rust 中，函数实现通常与定义一起完成，如上例所示。
然而，如果你使用 trait 或默认方法，可能会有单独的实现。

```rust
// 函数实现是函数定义的一部分
fn add(a: i32, b: i32) -> i32 {
    a + b // 这里是函数实现
}
```

## 抽象和默认实现

在 Rust 中，trait 可以定义一组方法的签名，这些方法可以被抽象出来，不立即提供实现：

```rust
trait Animal {
    fn make_sound(&self);
}

struct Dog;

// 抽象方法，没有提供实现
impl Animal for Dog {
    // 这里可以不实现 make_sound 方法
}
```

## 默认实现

如果需要，可以为 trait 提供默认的实现，这样实现该 trait 的类型可以选择使用默认实现或提供自己的实现：

```rust
trait Animal {
    fn make_sound(&self);
    fn eat(&self) {
        println!("Animal is eating.");
    }
}

impl Animal for Dog {
    fn make_sound(&self) {
        println!("Woof!");
    }

    // Dog 可以不实现 eat 方法，因为它已经有一个默认实现
}
```

## 分离定义和实现

在模块化的 Rust 程序中，有时你可能希望将函数的定义和实现分开，以提高代码的可读性和组织性。
你可以在一个模块中声明函数，然后在另一个模块中实现它：

```rust
// 在 lib.rs 或 mod.rs 中
mod math;
pub use math::add;

// 在 math.rs 中
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}
```

在这个例子中，`add` 函数在 `math.rs` 中被定义和实现，然后在 `lib.rs` 或 `mod.rs` 中被声明和重导出。

总结来说，函数声明是函数的签名，函数定义是声明加上实现，而函数实现是实际的代码块。
在 Rust 中，定义通常包括声明和实现，但在某些情况下，如 trait 的抽象方法或模块化编程，可能会将它们分开。
在 Rust 中，函数声明用于定义函数的名称、参数列表、返回类型以及函数体。
以下是 Rust 函数声明的基本语法规则：

1. **函数名称**:
   - 函数名称应该以小写字母开头，使用 snake_case（下划线命名法）。

2. **参数列表**:
   - 参数列表包括函数接受的输入值，每个参数可以有类型注解和可选的默认值。

3. **返回类型**:
   - 使用 `->` 指定函数的返回类型。如果没有返回值，可以使用 `()` ,`!` 或省略 `->` 和返回类型。

4. **函数体**:
   - 函数体是大括号 `{}` 内的代码块，包含函数的执行逻辑。

5. **可变性**:
   - 参数默认是不可变的。如果需要修改参数，需要在参数前添加 `mut` 关键字。

6. **泛型参数**:
   - 可以使用泛型参数来定义可以接受多种类型的函数。

7. **trait 约束**:
   - 可以在参数或泛型类型中使用 trait 约束来指定必须实现的 trait。

8. **外部函数**:
   - 使用 `extern` 关键字声明外部函数，如 C 语言写的库中的函数。

## 示例

```rust
// 无参数，无返回值的函数
fn do_nothing() {
    println!("Doing nothing...");
}

// 有参数，有返回值的函数
fn add(a: i32, b: i32) -> i32 {
    a + b
}

// 有命名参数的函数
fn print_coordinates(x: i32, y: i32) {
    println!("Current coordinates: ({}, {})", x, y);
}

// 有默认参数值的函数
fn create_point(x: i32, y: i32) -> Point {
    Point { x: x, y: y }
}

// 使用泛型和 trait 约束的函数
fn largest<T: PartialOrd + Copy>(list: &[T]) -> &T {
    let mut largest = &list[0];
    for &item in list.iter() {
        if item > *largest {
            largest = &item;
        }
    }
    largest
}

// 可变参数的函数
fn first_word(s: &str) -> &str {
    let bytes = s.as_bytes();

    for (i, &item) in bytes.iter().enumerate() {
        if item == b' ' {
            return &s[0..i];
        }
    }

    &s[..]
}

// 外部函数声明（例如，C 语言函数）
extern "C" {
    fn abs(input: i32) -> i32;
}
```

函数声明是 Rust 编程中的基础，它们是构建程序逻辑的基本单元。
在 Rust 中，函数是一等公民，这意味着它们可以像其他值一样被存储、传递和返回。
Rust 的函数可以有不同的类型，这些类型由函数的参数和返回值决定。
以下是 Rust 函数类型和定义的一些基本概念：

## 普通函数

普通函数是最常见的函数类型，它们可以定义在模块的顶层或结构体、枚举、trait 等的上下文中：

```rust
fn add(a: i32, b: i32) -> i32 {
    a + b
}
```

这个 `add` 函数接受两个 `i32` 类型的参数，并返回一个 `i32` 类型的值。

## 匿名函数

匿名函数没有名字，通常用于立即执行或作为参数传递给其他函数：

```rust
let add = |a, b| a + b;
let result = add(5, 7); // result is 12
```

这里的 `|a, b| a + b` 是一个匿名函数，它捕获了两个参数 `a` 和 `b` 并返回它们的和。

## 闭包

闭包类似于匿名函数，但它们可以捕获外部环境中的变量：

```rust
let x = 5;
let add_x = |a| a + x;
let result = add_x(3); // result is 8
```

在这个例子中，闭包 `add_x` 捕获了外部变量 `x`。

## 函数指针

函数指针是指向函数的引用，它们有自己的类型：

```rust
fn function_pointer_example(a: i32, b: i32) -> i32 {
    a + b
}

let f: fn(i32, i32) -> i32 = function_pointer_example;
let result = f(5, 7); // result is 12
```

这里的 `f` 是一个函数指针，它指向 `function_pointer_example` 函数。

## 高阶函数

高阶函数是接受函数作为参数或返回函数的函数：

```rust
fn apply<T, F>(f: F, x: T) -> T
where
    F: Fn(T) -> T,
{
    f(x)
}

fn increment(x: i32) -> i32 {
    x + 1
}

let result = apply(increment, 5); // result is 6
```

`apply` 是一个高阶函数，它接受一个函数 `f` 和一个值 `x`，然后应用 `f` 到 `x` 上。

## 泛型函数

泛型函数可以接受不同类型的参数：

```rust
fn identity<T>(value: T) -> T {
    value
}

let string = identity("Hello, world!");
let number = identity(42);
```

`identity` 函数是一个泛型函数，它可以接收任何类型的参数并返回相同类型的值。

## 可变参数函数

Rust 允许定义接受可变数量参数的函数：

```rust
fn sum_all(args: i32...) -> i32 {
    let mut sum = 0;
    for &arg in args.iter() {
        sum += arg;
    }
    sum
}

let result = sum_all(1, 2, 3, 4); // result is 10
```

注意：Rust 标准库中没有直接支持可变参数的语法，但可以通过宏或者其他方式实现类似的功能。

## 异步函数

异步函数允许执行非阻塞操作：

```rust
async fn fetch_data() -> Result<String, std::io::Error> {
    // 模拟异步操作
    Ok("Data".to_string())
}

#[tokio::main]
async fn main() {
    let data = fetch_data().await;
}
```

在这个例子中，`fetch_data` 是一个异步函数，它使用 `async` 关键字定义，并返回一个 `Result` 类型。

Rust 的函数类型非常灵活，支持多种编程范式，包括函数式编程、面向对象编程和过程式编程。
通过这些特性，Rust 允许开发者编写高效、安全且可维护的代码。
