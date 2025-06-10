# From 和 Into

## 目录

- [From 和 Into](#from-和-into)
  - [目录](#目录)
  - [1. `From` Trait](#1-from-trait)
  - [2. `Into` Trait](#2-into-trait)
  - [3. 使用 `From` 和 `Into` 的示例](#3-使用-from-和-into-的示例)
    - [示例 1：基本类型转换](#示例-1基本类型转换)
    - [示例 2：自定义类型转换](#示例-2自定义类型转换)
    - [示例 3：泛型转换](#示例-3泛型转换)
  - [4. 总结](#4-总结)

在 Rust 中，`into` 和 `from` 是两个非常有用的特性，它们允许在不同类型之间进行转换。
这些特性通过实现 `From` 和 `Into` Trait 来定义。
`From` Trait 用于从一种类型创建另一种类型，
而 `Into` Trait 则是 `From` Trait 的逆操作，用于将一种类型转换为另一种类型。

## 1. `From` Trait

`From` Trait 允许你定义如何从一种类型创建另一种类型。它的定义如下：

```rust
pub trait From<T> {
    fn from(t: T) -> Self;
}
```

## 2. `Into` Trait

`Into` Trait 是 `From` Trait 的逆操作，允许你定义如何将一种类型转换为另一种类型。
它的定义如下：

```rust
pub trait Into<T> {
    fn into(self) -> T;
}
```

`Into` Trait 通常通过 `From` Trait 来实现。
如果一个类型 `T` 实现了 `From<U>`，那么 `U` 自动实现了 `Into<T>`。

## 3. 使用 `From` 和 `Into` 的示例

### 示例 1：基本类型转换

```rust
// 将 i32 转换为 String
let num = 123;
let num_str: String = num.to_string();
println!("{}", num_str); // 输出: 123

// 使用 From Trait
let num_str_from: String = String::from(num);
println!("{}", num_str_from); // 输出: 123

// 使用 Into Trait
let num_str_into: String = num.into();
println!("{}", num_str_into); // 输出: 123
```

### 示例 2：自定义类型转换

```rust
struct Point {
    x: f64,
    y: f64,
}

impl From<(f64, f64)> for Point {
    fn from(coords: (f64, f64)) -> Self {
        Point {
            x: coords.0,
            y: coords.1,
        }
    }
}

impl Into<(f64, f64)> for Point {
    fn into(self) -> (f64, f64) {
        (self.x, self.y)
    }
}

fn main() {
    // 使用 From Trait
    let point: Point = Point::from((3.0, 4.0));
    println!("Point: ({}, {})", point.x, point.y); // 输出: Point: (3.0, 4.0)

    // 使用 Into Trait
    let coords: (f64, f64) = point.into();
    println!("Coordinates: ({}, {})", coords.0, coords.1); // 输出: Coordinates: (3.0, 4.0)
}
```

### 示例 3：泛型转换

```rust
struct Wrapper<T>(T);

impl<T> From<T> for Wrapper<T> {
    fn from(value: T) -> Self {
        Wrapper(value)
    }
}

impl<T> Into<T> for Wrapper<T> {
    fn into(self) -> T {
        self.0
    }
}

fn main() {
    let value: i32 = 42;
    let wrapper: Wrapper<i32> = Wrapper::from(value);
    println!("Wrapper: {}", wrapper.0); // 输出: Wrapper: 42

    let value_back: i32 = wrapper.into();
    println!("Value: {}", value_back); // 输出: Value: 42
}
```

## 4. 总结

`From` 和 `Into` Trait 提供了一种标准化的方式来在不同类型之间进行转换。
通过实现这些 Trait，你可以定义如何从一种类型创建另一种类型，以及如何将一种类型转换为另一种类型。
这使得代码更加灵活和可读，特别是在处理不同类型之间的转换时非常有用。
