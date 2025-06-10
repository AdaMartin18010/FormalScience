# Rust 泛型

## 目录

- [Rust 泛型](#rust-泛型)
  - [目录](#目录)
    - [1. 引言](#1-引言)
    - [2. Rust 泛型基础 (Rust Generics Fundamentals)](#2-rust-泛型基础-rust-generics-fundamentals)
      - [2.1 什么是泛型？](#21-什么是泛型)
      - [2.2 泛型语法](#22-泛型语法)
        - [2.2.1 泛型函数](#221-泛型函数)
        - [2.2.2 泛型结构体](#222-泛型结构体)
        - [2.2.3 泛型枚举](#223-泛型枚举)
        - [2.2.4 泛型方法](#224-泛型方法)
      - [2.3 Trait 与 Trait Bounds](#23-trait-与-trait-bounds)
        - [2.3.1 基本约束](#231-基本约束)
        - [2.3.2 `where` 子句](#232-where-子句)
        - [2.3.3 标记 Trait (Marker Traits)](#233-标记-trait-marker-traits)
      - [2.4 类型推导](#24-类型推导)
      - [2.5 单态化 (Monomorphization)](#25-单态化-monomorphization)
      - [2.6 `const` 泛型](#26-const-泛型)
      - [2.7 关联类型 (Associated Types)](#27-关联类型-associated-types)
        - [2.7.1 定义与使用](#271-定义与使用)
        - [2.7.2 与泛型参数对比](#272-与泛型参数对比)
      - [2.8 泛型生命周期](#28-泛型生命周期)
        - [2.8.1 生命周期省略规则 (Lifetime Elision)](#281-生命周期省略规则-lifetime-elision)
        - [2.8.2 显式生命周期](#282-显式生命周期)
        - [2.8.3 生命周期约束](#283-生命周期约束)
        - [2.8.4 高阶 Trait Bounds (HRTBs - Higher-Rank Trait Bounds)](#284-高阶-trait-bounds-hrtbs---higher-rank-trait-bounds)
    - [3. Rust 泛型进阶与应用 (Advanced Rust Generics and Applications)](#3-rust-泛型进阶与应用-advanced-rust-generics-and-applications)
      - [3.1 设计模式](#31-设计模式)
        - [3.1.1 类型状态模式 (Type State Pattern)](#311-类型状态模式-type-state-pattern)
        - [3.1.2 构建器模式 (Builder Pattern)](#312-构建器模式-builder-pattern)
        - [3.1.3 Newtype 模式](#313-newtype-模式)
      - [3.2 编程技巧](#32-编程技巧)
        - [3.2.1 零成本抽象](#321-零成本抽象)
        - [3.2.2 代码复用](#322-代码复用)
        - [3.2.3 静态分发 vs 动态分发](#323-静态分发-vs-动态分发)
      - [3.3 库代码设计](#33-库代码设计)
        - [3.3.1 设计灵活的 API](#331-设计灵活的-api)
        - [3.3.2 平衡泛型与具体实现](#332-平衡泛型与具体实现)
        - [3.3.3 使用关联类型优化 API](#333-使用关联类型优化-api)
      - [3.4 程序应用设计](#34-程序应用设计)
      - [3.5 多线程设计](#35-多线程设计)
        - [3.5.1 `Send` 与 `Sync` 约束](#351-send-与-sync-约束)
        - [3.5.2 泛型并发数据结构](#352-泛型并发数据结构)
      - [3.6 异步/同步设计](#36-异步同步设计)
        - [3.6.1 `async` 中的泛型](#361-async-中的泛型)
        - [3.6.2 泛型 Future](#362-泛型-future)
      - [3.7 算法设计](#37-算法设计)
      - [3.8 迭代与递归](#38-迭代与递归)
        - [3.8.1 泛型迭代器](#381-泛型迭代器)
        - [3.8.2 泛型递归结构与函数](#382-泛型递归结构与函数)
    - [4. 总结 (Conclusion)](#4-总结-conclusion)

---

### 1. 引言

Rust 泛型是一种强大的**参数化多态 (Parametric Polymorphism)** 机制，它允许我们在编写代码时使用抽象的类型占位符，而不是具体的类型。这些占位符（泛型参数）在编译时会被具体的类型替换，从而生成针对特定类型的代码。泛型的核心优势在于**代码复用**和**类型安全**，使得开发者能够编写出既灵活通用又能在编译期进行严格类型检查的代码。

---

### 2. Rust 泛型基础 (Rust Generics Fundamentals)

#### 2.1 什么是泛型？

泛型允许我们定义函数、结构体、枚举和方法，使其能够处理多种不同的数据类型，而无需为每种类型重复编写几乎相同的代码。例如，标准库中的 `Option<T>` 和 `Result<T, E>` 就是泛型枚举，`Vec<T>` 是泛型结构体。

#### 2.2 泛型语法

泛型参数通常使用大写字母表示（如 `T`, `U`, `E`），并放在尖括号 `<>` 中。

##### 2.2.1 泛型函数

函数签名中可以在函数名后声明泛型参数。

```rust
// 定义一个泛型函数 largest，它可以找到任何实现了 PartialOrd trait 的类型切片中的最大值
fn largest<T: PartialOrd>(list: &[T]) -> &T {
    let mut largest = &list[0];
    for item in list {
        // 因为 T: PartialOrd, 所以可以使用 > 运算符
        if item > largest {
            largest = item;
        }
    }
    largest
}

fn main() {
    let number_list = vec![34, 50, 25, 100, 65];
    let result = largest(&number_list);
    println!("The largest number is {}", result); // 输出: The largest number is 100

    let char_list = vec!['y', 'm', 'a', 'q'];
    let result = largest(&char_list);
    println!("The largest char is {}", result); // 输出: The largest char is y
}
```

##### 2.2.2 泛型结构体

结构体定义中可以在结构体名后声明泛型参数，字段类型可以使用这些参数。

```rust
// 定义一个可以存储任何类型 x 和 y 坐标的点
struct Point<T> {
    x: T,
    y: T,
}

// 也可以有多个不同的泛型参数
struct PointMulti<T, U> {
    x: T,
    y: U,
}

fn main() {
    let integer_point = Point { x: 5, y: 10 };
    let float_point = Point { x: 1.0, y: 4.0 };
    // let wont_work = Point { x: 5, y: 4.0 }; // 编译错误！x 和 y 必须是相同类型 T

    let multi_point = PointMulti { x: 5, y: 4.0 }; // 正确，T 是 i32, U 是 f64
}
```

##### 2.2.3 泛型枚举

枚举定义中也可以使用泛型参数。`Option<T>` 和 `Result<T, E>` 是最经典的例子。

```rust
// 标准库 Option<T> 的简化定义
// enum Option<T> {
//     Some(T),
//     None,
// }

// 标准库 Result<T, E> 的简化定义
// enum Result<T, E> {
//     Ok(T),
//     Err(E),
// }

fn main() {
    let some_number: Option<i32> = Some(5);
    let no_number: Option<i32> = None;

    let success: Result<String, std::io::Error> = Ok("Success".to_string());
    // let failure: Result<String, std::io::Error> = Err(std::io::Error::new(...));
}
```

##### 2.2.4 泛型方法

可以在 `impl` 块中使用泛型参数，为泛型类型定义方法。

```rust
struct Point<T> {
    x: T,
    y: T,
}

// 为泛型结构体 Point<T> 实现方法
impl<T> Point<T> {
    fn x(&self) -> &T {
        &self.x
    }
}

// 也可以只为特定类型的 Point 实现方法
impl Point<f32> {
    fn distance_from_origin(&self) -> f32 {
        (self.x.powi(2) + self.y.powi(2)).sqrt()
    }
}

fn main() {
    let p_int = Point { x: 5, y: 10 };
    println!("p_int.x = {}", p_int.x()); // 对所有 Point<T> 都可用

    let p_float = Point { x: 3.0, y: 4.0 };
    println!("p_float.x = {}", p_float.x()); // 对所有 Point<T> 都可用
    println!("Distance from origin = {}", p_float.distance_from_origin()); // 仅对 Point<f32> 可用

    // p_int.distance_from_origin(); // 编译错误！该方法仅为 Point<f32> 定义
}
```

#### 2.3 Trait 与 Trait Bounds

Trait Bounds 用于约束泛型参数必须实现哪些 Trait，从而保证泛型代码内部可以调用这些 Trait 定义的方法或使用其关联类型。

##### 2.3.1 基本约束

使用冒号 `:` 加上 Trait 名称来指定约束。多个约束使用 `+` 连接。

```rust
use std::fmt::Display;

// T 必须实现 Display trait
fn print_item<T: Display>(item: T) {
    println!("{}", item);
}

// T 必须同时实现 Display 和 Debug trait
use std::fmt::Debug;
fn print_item_detailed<T: Display + Debug>(item: T) {
    println!("Display: {}", item);
    println!("Debug: {:?}", item);
}

// T 必须实现 PartialOrd trait (用于比较)
fn compare<T: PartialOrd>(a: T, b: T) {
    if a > b {
        println!("a is greater");
    } else if a < b {
        println!("b is greater");
    } else {
        println!("a equals b");
    }
}
```

##### 2.3.2 `where` 子句

当泛型参数和 Trait Bounds 变得复杂时，可以使用 `where` 子句提高可读性。

```rust
use std::fmt::{Display, Debug};

// 使用 where 子句约束 T, U
fn some_function<T, U>(t: &T, u: &U) -> i32
where
    T: Display + Clone,
    U: Clone + Debug,
{
    println!("t: {}", t);
    println!("u: {:?}", u);
    // ...
    0
}
```

`where` 子句在处理关联类型约束或更复杂的生命周期约束时尤其有用。

##### 2.3.3 标记 Trait (Marker Traits)

一些 Trait 本身没有定义任何方法，它们的存在只是为了给类型添加某种标记或属性。常见的标记 Trait 包括：

- `Copy`: 表示类型的值可以通过简单的内存复制来“克隆”，而不需要复杂的逻辑（如堆分配）。拥有 `Copy` 的类型也必须实现 `Clone`。基本类型（如 `i32`, `f64`, `bool`, `char`）和包含 `Copy` 类型字段的元组/数组都是 `Copy` 的。
- `Send`: 表示类型的所有权可以在线程间安全地转移。
- `Sync`: 表示类型可以安全地被多个线程共享（即 `&T` 是 `Send`）。
- `Sized`: 表示类型在编译时具有固定的大小。几乎所有类型都是 `Sized` 的。`?Sized` 用于表示类型可能是动态大小的（DST），如 `str` 或 `[T]`。函数参数默认带有 `T: Sized` 的约束，可以通过 `T: ?Sized` 放宽。

```rust
// 这个函数要求 T 是可以复制的
fn duplicate<T: Copy>(x: T) -> (T, T) {
    (x, x)
}

fn main() {
    let a = 5; // i32 is Copy
    let pair = duplicate(a);
    println!("{:?}", pair); // 输出: (5, 5)
    println!("{}", a); // a 仍然可用，因为它是 Copy

    // let s = String::from("hello"); // String is not Copy
    // duplicate(s); // 编译错误！
}

// 这个函数要求 T 可以在线程间传递
fn spawn_thread_with_data<T: Send + 'static>(data: T) {
    std::thread::spawn(move || {
        // 使用 data
        println!("Data received in thread.");
    });
}
```

#### 2.4 类型推导

Rust 编译器通常能够根据函数调用时传入的参数或变量赋值时的上下文推导出泛型参数的具体类型，无需显式指定。

```rust
fn identity<T>(x: T) -> T {
    x
}

fn main() {
    let x = 5;
    let y = identity(x); // 编译器推断 T 为 i32

    let s = "hello";
    let t = identity(s); // 编译器推断 T 为 &'static str

    let numbers: Vec<i32> = Vec::new(); // 需要显式指定类型，因为 new() 没有参数让编译器推断
    let mut numbers = Vec::new(); // 或者让编译器稍后推断
    numbers.push(1); // 此时编译器推断出 Vec 的类型是 Vec<i32>
}
```

有时需要使用 `::<Type>` 语法（称为 "turbofish"）来帮助编译器进行类型推导，特别是当函数返回值是泛型且没有输入参数可以推导时。

```rust
fn main() {
    let numbers: Vec<i32> = (0..10).collect(); // collect() 是泛型的，需要知道收集到什么类型中
    let numbers = (0..10).collect::<Vec<i32>>(); // 使用 turbofish 显式指定

    // let result = "123".parse(); // 编译错误！编译器不知道要解析成什么类型 (i32? f64? ...)
    let result: i32 = "123".parse().unwrap(); // 通过类型注解指定
    let result = "123".parse::<i32>().unwrap(); // 通过 turbofish 指定
}
```

#### 2.5 单态化 (Monomorphization)

这是 Rust 实现泛型的关键机制。在编译时，编译器会检查所有泛型代码被使用的具体类型，并为每种具体的类型组合生成一份专门的代码。

例如，对于泛型函数 `fn identity<T>(x: T) -> T`：

```rust
let x: i32 = 5;
identity(x); // 编译器生成 identity_i32(x: i32) -> i32

let s: String = String::from("hello");
identity(s); // 编译器生成 identity_String(x: String) -> String
```

**优点：**

- **性能：** 单态化后的代码与手写针对特定类型的代码具有相同的运行时性能，没有泛型带来的运行时开销（零成本抽象）。函数调用是直接的静态分发。

**缺点：**

- **编译时间：** 需要为每个具体类型生成代码，可能增加编译时间。
- **代码体积：** 生成的二进制文件可能更大，因为同一份泛型逻辑被复制了多次。

编译器会进行优化，例如内联等，可能会减轻代码体积问题。

#### 2.6 `const` 泛型

`const` 泛型允许泛型参数是编译时常量值，而不仅仅是类型。这对于定义固定大小的数据结构（如数组）或需要编译时计算的类型非常有用。

目前 `const` 泛型主要支持整数类型 (`usize`, `i32`, etc.)、`bool` 和 `char`。

```rust
// N 是一个编译时常量泛型参数
fn print_array<T: std::fmt::Debug, const N: usize>(arr: [T; N]) {
    println!("Array of size {}: {:?}", N, arr);
}

// 定义一个固定大小的缓冲区
struct Buffer<T, const SIZE: usize> {
    data: [T; SIZE],
}

impl<T: Default + Copy, const SIZE: usize> Buffer<T, SIZE> {
    fn new() -> Self {
        Buffer {
            data: [T::default(); SIZE], // 使用 const 泛型 SIZE
        }
    }
}

fn main() {
    let arr1 = [1, 2, 3]; // 类型是 [i32; 3]
    let arr2 = [true, false]; // 类型是 [bool; 2]

    print_array(arr1); // 编译器推断 N 为 3
    print_array(arr2); // 编译器推断 N 为 2

    let buffer: Buffer<u8, 1024> = Buffer::new(); // SIZE 是 1024
    println!("Buffer size: {}", buffer.data.len()); // 输出 1024
}
```

`const` 泛型极大地增强了类型系统的表达能力，可以在编译时进行更多检查和计算。

#### 2.7 关联类型 (Associated Types)

关联类型是在 Trait 定义内部声明的类型占位符。它将一个类型与实现该 Trait 的类型关联起来。这与 Trait 本身是泛型（如 `trait MyTrait<T> {}`）不同。

##### 2.7.1 定义与使用

最经典的例子是 `Iterator` Trait：

```rust
// 标准库 Iterator Trait 的简化定义
trait Iterator {
    // Item 是这个 Iterator 产生的元素的类型
    type Item;

    // next 方法返回一个 Option<Self::Item>
    fn next(&mut self) -> Option<Self::Item>;
}

// 为 Vec<T> 实现 IntoIterator (返回一个 Vec 的迭代器)
impl<T> IntoIterator for Vec<T> {
    type Item = T; // 关联类型 Item 被指定为 Vec<T> 中的 T
    type IntoIter = std::vec::IntoIter<T>; // 迭代器本身的类型

    fn into_iter(self) -> Self::IntoIter {
        // ... 返回具体的迭代器实例 ...
        std::vec::IntoIter::new(self) // 假设有这个构造函数
    }
}

// 使用迭代器
fn main() {
    let v = vec![1, 2, 3];
    let mut iterator = v.into_iter(); // iterator 的类型是 std::vec::IntoIter<i32>

    // iterator.next() 返回 Option<i32>，因为 Item 被指定为 i32
    assert_eq!(iterator.next(), Some(1));
    assert_eq!(iterator.next(), Some(2));
    assert_eq!(iterator.next(), Some(3));
    assert_eq!(iterator.next(), None);
}
```

##### 2.7.2 与泛型参数对比

- **泛型参数 (`Trait<T>`):** 一个类型可以为**不同**的泛型参数 `T` 多次实现同一个 Trait。例如，`Add<i32>` 和 `Add<f64>` 可以为同一个类型实现。
- **关联类型 (trait Trait { type Item; }):** 一个类型只能为 Trait 中的**每个**关联类型指定**一个**具体类型。一个类型实现 `Iterator` 时，`Item` 类型是唯一的。

关联类型通常使得 Trait 的使用更简洁，因为调用者不需要在每次使用 Trait 时都指定关联类型（编译器可以从实现中推断）。当一个类型与某个 Trait 强相关且只需要一个对应的辅助类型时，关联类型是更好的选择。

#### 2.8 泛型生命周期

生命周期也是一种泛型参数，但它描述的是**引用**的有效作用域，而不是类型。生命周期参数确保借用的引用不会比它们所引用的数据活得更长。

生命周期参数以撇号 `'` 开头，通常是小写字母（如 `'a`, `'b`）。

##### 2.8.1 生命周期省略规则 (Lifetime Elision)

Rust 编译器有一套省略规则，允许在一些常见模式下省略生命周期标注，使代码更简洁。主要规则：

1. **输入生命周期：** 每个作为输入的引用参数都有自己独立的生命周期参数。
2. **单一输入生命周期：** 如果只有一个输入生命周期参数，那么它会被赋给所有输出生命周期参数。
3. **`&self` 或 `&mut self`：** 如果方法有 `&self` 或 `&mut self` 参数，那么 `self` 的生命周期会被赋给所有输出生命周期参数。

如果这些规则无法明确所有输出引用的生命周期，则必须手动标注。

```rust
// 省略前: fn foo<'a>(x: &'a str) -> &'a str;
// 省略后: fn foo(x: &str) -> &str; // 规则 2

// 省略前: struct Foo<'a> { x: &'a i32 }
// impl<'a> Foo<'a> {
//     fn get_x<'b>(&'b self) -> &'a i32 { self.x } // 返回值的生命周期与 self.x 相同 ('a)
//     fn set_x(&'b mut self, v: &'a i32) { self.x = v; }
// }
// 省略后:
// struct Foo<'a> { x: &'a i32 }
// impl<'a> Foo<'a> {
//     fn get_x(&self) -> &i32 { self.x } // 规则 3: 输出生命周期 = self 的生命周期 ('a)
//     // 注意：set_x 的 v 必须显式标注或满足其他规则，这里省略不了 'a
//     fn set_x(&mut self, v: &'a i32) { self.x = v; }
// }
```

##### 2.8.2 显式生命周期

当省略规则不适用或需要更精确控制时，需要显式标注生命周期。

```rust
// 这个函数返回两个字符串切片中较长的那一个
// 返回的引用必须与输入的两个引用中 *较短* 的那个具有相同的生命周期
// 因此，输入和输出的生命周期必须是相同的 'a
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}

fn main() {
    let string1 = String::from("long string is long");
    let result;
    {
        let string2 = String::from("xyz");
        result = longest(string1.as_str(), string2.as_str()); // result 的生命周期受 string2 限制
        println!("The longest string is {}", result);
    }
    // println!("The longest string is {}", result); // 编译错误！result 引用的 string2 已经失效
}

// 结构体包含引用时，必须标注生命周期
struct ImportantExcerpt<'a> {
    part: &'a str,
}

fn main_struct() {
    let novel = String::from("Call me Ishmael. Some years ago...");
    let first_sentence = novel.split('.').next().expect("Could not find a '.'");
    let i = ImportantExcerpt {
        part: first_sentence, // i 的生命周期不能超过 first_sentence (也就是 novel)
    };
}
```

##### 2.8.3 生命周期约束

可以像约束类型参数一样约束生命周期参数。`'a: 'b` 表示生命周期 `'a` 必须至少和 `'b` 一样长（`'a` outlives `'b`）。这常用于泛型类型包含引用的情况。

```rust
// T 可能包含生命周期为 'b 的引用
// 我们要求 T 本身（及其可能包含的引用）至少活得和 'a 一样长
struct Wrapper<'a, T: 'a> {
    inner: T,
    lifetime_marker: std::marker::PhantomData<&'a ()>, // 仅用于标记生命周期 'a
}

// T 必须实现 Display, 并且 T 包含的任何引用都必须活得比 'a 长
fn print_ref<'a, T>(t: &'a T)
where
    T: std::fmt::Display + 'a, // T: 'a 约束
{
    println!("{}", t);
}

fn main() {
    let s = String::from("hello");
    let r = &s; // r 的生命周期是 'a (假设)
    print_ref(r); // T 是 &String, T 包含的引用生命周期 ('a) 必须活得比 print_ref 调用时的 'a 长，这是满足的

    // let dead_ref: &String;
    // {
    //     let s_inner = String::from("gone");
    //     dead_ref = &s_inner;
    // }
    // print_ref(dead_ref); // 编译错误！dead_ref 指向的数据已经失效，不满足 T: 'a
}
```

`T: 'a` 意味着 `T` 中包含的所有引用生命周期都必须比 `'a` 长。

##### 2.8.4 高阶 Trait Bounds (HRTBs - Higher-Rank Trait Bounds)

HRTBs (`for<'a> ...`) 用于表示一个类型实现了某个 Trait，**对于任意**生命周期 `'a` 都成立。这在处理闭包或函数指针这类需要泛型生命周期的 Trait 时非常有用。

例如，一个函数接受一个闭包，该闭包接受任何生命周期的引用并返回一个引用：

```rust
// F 是一个闭包类型
// 它必须实现 Fn Trait，并且对于 *任何* 生命周期 'a，
// 它都能接受一个 &'a i32 并返回一个 &'a i32
fn apply_to_ref<F>(f: F, value: &i32) -> &i32
where
    F: for<'a> Fn(&'a i32) -> &'a i32,
{
    f(value)
}

fn main() {
    let identity = |x: &i32| x; // 这个闭包满足 for<'a> Fn(&'a i32) -> &'a i32
    let x = 10;
    let y = apply_to_ref(identity, &x);
    println!("{}", y);

    // let mut captured_ref = &0;
    // let closure_with_capture = |x: &i32| -> &i32 {
    //    captured_ref = x; // 尝试捕获外部引用
    //    captured_ref       // 返回捕获的引用，其生命周期固定，不满足 for<'a>
    // };
    // apply_to_ref(closure_with_capture, &x); // 编译错误！
}
```

`for<'a>` 使得 Trait Bound 可以在不同的调用点适用于不同的具体生命周期。

---

### 3. Rust 泛型进阶与应用 (Advanced Rust Generics and Applications)

#### 3.1 设计模式

泛型和 Trait 是 Rust 实现许多设计模式的基础。

##### 3.1.1 类型状态模式 (Type State Pattern)

使用泛型参数（通常是空结构体或枚举作为标记类型）来表示对象所处的状态，并将状态转移逻辑编码到类型系统中。这使得无效的状态转换在编译时就会被捕获。

```rust
struct Post {
    content: String,
}

struct DraftPost {
    content: String,
}

struct PendingReviewPost {
    content: String,
}

impl Post {
    // 开始一个新的草稿
    fn new() -> DraftPost {
        DraftPost {
            content: String::new(),
        }
    }
}

impl DraftPost {
    fn add_text(&mut self, text: &str) {
        self.content.push_str(text);
    }
    // 请求审核，消耗 DraftPost，返回 PendingReviewPost
    fn request_review(self) -> PendingReviewPost {
        PendingReviewPost {
            content: self.content,
        }
    }
}

impl PendingReviewPost {
    // 批准帖子，消耗 PendingReviewPost，返回 Post
    fn approve(self) -> Post {
        Post {
            content: self.content,
        }
    }
    // 拒绝帖子，返回草稿状态
    fn reject(self) -> DraftPost {
        DraftPost {
            content: self.content,
        }
    }
}

fn main() {
    let mut post = Post::new(); // 得到 DraftPost
    post.add_text("I ate salad for lunch today.");
    // post.approve(); // 编译错误！DraftPost 没有 approve 方法

    let post = post.request_review(); // 变成 PendingReviewPost
    // post.add_text("..."); // 编译错误！PendingReviewPost 没有 add_text 方法

    let post = post.approve(); // 变成 Post
    // post.request_review(); // 编译错误！Post 没有 request_review 方法
    // 现在 post 是最终状态，可以发布 (假设有 publish 方法)
    println!("Published content: {}", post.content);
}
```

这里虽然没有显式使用 `<T>` 泛型，但其思想是用不同的类型 (`DraftPost`, `PendingReviewPost`, `Post`) 来代表状态，方法签名控制了状态转换，这与使用泛型标记状态 (`Post<Draft>`, `Post<PendingReview>`, `Post<Published>`) 是等价的思路。

##### 3.1.2 构建器模式 (Builder Pattern)

泛型可以用来创建类型安全的构建器，确保所有必需的字段都已设置，或者以特定顺序设置字段。

```rust
use std::marker::PhantomData;

// 构建器状态标记
struct NoUrl;
struct HasUrl(String);
struct NoMethod;
struct HasMethod(String);

// 泛型构建器，U 代表 URL 状态，M 代表 Method 状态
struct RequestBuilder<U, M> {
    url: U,
    method: M,
    headers: Vec<(String, String)>,
}

// 初始状态：没有 URL，没有 Method
impl RequestBuilder<NoUrl, NoMethod> {
    fn new() -> Self {
        RequestBuilder {
            url: NoUrl,
            method: NoMethod,
            headers: Vec::new(),
        }
    }
}

// 通用方法，适用于任何状态
impl<U, M> RequestBuilder<U, M> {
    fn header(mut self, key: &str, value: &str) -> Self {
        self.headers.push((key.to_string(), value.to_string()));
        self
    }
}

// 从 NoUrl 状态设置 URL
impl RequestBuilder<NoUrl, NoMethod> {
    fn url(self, url: &str) -> RequestBuilder<HasUrl, NoMethod> {
        RequestBuilder {
            url: HasUrl(url.to_string()),
            method: self.method, // 保持 NoMethod 状态
            headers: self.headers,
        }
    }
}

// 从 HasUrl 且 NoMethod 状态设置 Method
impl RequestBuilder<HasUrl, NoMethod> {
    fn method(self, method: &str) -> RequestBuilder<HasUrl, HasMethod> {
        RequestBuilder {
            url: self.url, // 保持 HasUrl 状态
            method: HasMethod(method.to_string()),
            headers: self.headers,
        }
    }
}

// 最终状态，可以构建 Request
impl RequestBuilder<HasUrl, HasMethod> {
    fn build(self) /* -> Request (假设有个 Request 类型) */ {
        println!(
            "Building request: {} {}",
            self.method.0, self.url.0
        );
        // 返回实际的 Request 对象
    }
}

fn main() {
    RequestBuilder::new()
        .url("https://example.com") // 状态变为 RequestBuilder<HasUrl, NoMethod>
        // .build(); // 编译错误！还未设置 Method
        .method("GET") // 状态变为 RequestBuilder<HasUrl, HasMethod>
        .header("Content-Type", "application/json")
        .build(); // 正确，所有必需状态已满足
}
```

##### 3.1.3 Newtype 模式

将现有类型包装在一个只包含该类型的单元组结构体 (`struct Wrapper(InnerType);`) 中。这允许我们：

1. 为外部类型（甚至基本类型）实现本地 Trait。
2. 提供更强的类型抽象和约束。

泛型常与 Newtype 结合，为泛型类型添加特定行为。

```rust
use std::ops::Add;
use std::fmt;

// 为 Vec<i32> 创建一个 Newtype
struct MyIntVector(Vec<i32>);

// 为 Newtype 实现 Display Trait (不能直接为 Vec<i32> 实现)
impl fmt::Display for MyIntVector {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}]", self.0.iter().map(|i| i.to_string()).collect::<Vec<_>>().join(", "))
    }
}

// 为泛型 Newtype 添加约束
struct Sensitive<T>(T); // 包装敏感数据

// 假设我们不想让 Sensitive<String> 被直接打印
// 可以不为它实现 Display 或 Debug

// 泛型 Newtype 例子：只允许特定操作
struct PositiveFloat(f64);

impl PositiveFloat {
    fn new(value: f64) -> Option<Self> {
        if value > 0.0 {
            Some(PositiveFloat(value))
        } else {
            None
        }
    }
    fn value(&self) -> f64 {
        self.0
    }
}

fn main() {
    let v = MyIntVector(vec![1, 2, 3]);
    println!("{}", v); // 输出: [1, 2, 3]

    let password = Sensitive(String::from("secret123"));
    // println!("{}", password); // 如果没实现 Display, 这里会报错

    let val = PositiveFloat::new(10.5).unwrap();
    println!("Positive value: {}", val.value());
    // let invalid = PositiveFloat::new(-1.0); // 返回 None
}
```

#### 3.2 编程技巧

##### 3.2.1 零成本抽象

得益于单态化，Rust 中的泛型（包括 Trait Bounds）通常不会引入运行时开销。编译器生成专门的代码，使得调用泛型函数或方法与调用具体类型的函数或方法一样高效。这允许开发者使用高层抽象（如迭代器、集合、智能指针）而不用担心性能损失。

##### 3.2.2 代码复用

泛型的核心目的。编写一次泛型函数或数据结构，就可以用于多种不同的类型，只要它们满足指定的 Trait Bounds。例如，`sort` 算法只需要实现一次，就可以用于任何实现了 `Ord` Trait 的 `Vec<T>`。

##### 3.2.3 静态分发 vs 动态分发

- **静态分发 (Static Dispatch):**
  - 通过泛型和单态化实现。
  - 在编译时确定具体调用哪个函数实现。
  - 性能高，因为是直接函数调用，且可能被内联优化。
  - 导致代码体积增大。
  - 示例：`fn process<T: Display>(item: T)`

- **动态分发 (Dynamic Dispatch):**
  - 通过 Trait 对象 (`dyn Trait`) 实现。
  - 在运行时通过虚函数表 (vtable) 查找并调用具体实现。
  - 有轻微的运行时开销（指针解引用和 vtable 查找）。
  - 允许在集合中存储不同类型但实现相同 Trait 的对象。
  - 代码体积较小，因为泛型代码不被复制。
  - 示例：`fn process(item: &dyn Display)`

```rust
use std::fmt::Display;

// 静态分发
fn print_statically<T: Display>(item: T) {
    println!("Static: {}", item);
}

// 动态分发
fn print_dynamically(item: &dyn Display) {
    println!("Dynamic: {}", item);
}

struct Foo;
impl Display for Foo { fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "Foo") } }
struct Bar;
impl Display for Bar { fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "Bar") } }

fn main() {
    let foo = Foo;
    let bar = Bar;

    print_statically(foo); // 编译器生成 print_statically_Foo
    print_statically(bar); // 编译器生成 print_statically_Bar

    print_dynamically(&Foo); // 运行时查找 Foo 的 Display 实现
    print_dynamically(&Bar); // 运行时查找 Bar 的 Display 实现

    // 动态分发允许异构集合
    let items: Vec<&dyn Display> = vec![&Foo, &Bar];
    for item in items {
        print_dynamically(item);
    }

    // 静态分发通常不能直接用于异构集合 (除非使用 Enum 或其他技巧)
    // let items_static: Vec<???> = vec![Foo, Bar]; // 类型不同，无法放入 Vec
}
```

选择静态还是动态分发取决于具体需求：追求极致性能时选静态；需要运行时灵活性或存储异构类型时选动态。

#### 3.3 库代码设计

泛型是设计健壮、灵活、可复用 Rust 库的核心。

##### 3.3.1 设计灵活的 API

使用泛型参数和 Trait Bounds 可以让库的用户传入自定义的数据类型，只要它们满足接口要求。

```rust
// 一个通用的事件处理器，可以处理任何实现了 EventHandler Trait 的类型
trait EventHandler {
    type Event; // 事件类型
    fn handle(&mut self, event: &Self::Event);
}

// 一个事件分发器，接受一个 EventHandler
struct EventDispatcher<H: EventHandler> {
    handler: H,
}

impl<H: EventHandler> EventDispatcher<H> {
    fn new(handler: H) -> Self {
        EventDispatcher { handler }
    }

    fn dispatch(&mut self, event: &H::Event) {
        self.handler.handle(event);
    }
}

// --- 用户代码 ---
struct MyEvent { id: u32, data: String }
struct MyHandler { counter: u32 }

impl EventHandler for MyHandler {
    type Event = MyEvent; // 指定事件类型
    fn handle(&mut self, event: &Self::Event) {
        println!("Handling event {}: {}", event.id, event.data);
        self.counter += 1;
    }
}

fn main() {
    let my_handler = MyHandler { counter: 0 };
    let mut dispatcher = EventDispatcher::new(my_handler); // 传入自定义的 Handler

    dispatcher.dispatch(&MyEvent { id: 1, data: "First event".into() });
    dispatcher.dispatch(&MyEvent { id: 2, data: "Second event".into() });

    println!("Handler counter: {}", dispatcher.handler.counter); // 输出 2
}
```

##### 3.3.2 平衡泛型与具体实现

过度泛型化可能导致 API 难以理解和使用，编译时间增加，错误信息复杂。库设计者需要在通用性与易用性、编译性能之间找到平衡。

- **提供具体类型别名：** 为常用的泛型组合提供类型别名。
- **提供具体实现：** 除了泛型版本，也提供针对常见类型的非泛型函数或方法。
- **合理使用 Trait Bounds：** 只要求必要的 Trait，避免不必要的约束。
- **考虑动态分发：** 在某些场景下，接受 `Box<dyn Trait>` 可能比复杂的泛型约束更简单。

##### 3.3.3 使用关联类型优化 API

如前所述，关联类型可以使 Trait 实现更内聚，API 调用更简洁。当一个 Trait 逻辑上与某个特定类型紧密相关时，使用关联类型通常比泛型参数更好。例如，`Iterator::Item` 比 `Iterator<ItemType>` 更自然。

#### 3.4 程序应用设计

泛型有助于构建模块化、可测试和可维护的应用程序。

- **依赖注入：** 使用 Trait 和泛型来定义服务接口，并在构造时注入具体的实现（可以是真实的实现或测试用的 mock 对象）。
- **配置管理：** 定义泛型的配置结构体或 Trait，允许应用程序的不同部分或部署环境使用不同的配置类型。
- **数据模型：** 设计泛型数据容器或适配器，使其能处理应用中不同种类的数据。

```rust
// 示例：泛型化的存储库接口
trait Repository<T, Id> {
    fn find(&self, id: Id) -> Option<T>;
    fn save(&mut self, entity: T) -> Result<(), String>;
    // ... 其他方法
}

// 应用程序服务，依赖于一个实现了 Repository 的类型
struct UserService<R: Repository<User, UserId>> {
    repo: R,
    // ... 其他依赖
}

impl<R: Repository<User, UserId>> UserService<R> {
    fn get_user_name(&self, id: UserId) -> Option<String> {
        self.repo.find(id).map(|user| user.name)
    }
}

// --- 定义具体类型 ---
struct User { id: UserId, name: String }
struct UserId(u64);

// --- 实现 Repository (例如，内存实现) ---
use std::collections::HashMap;
struct InMemoryUserRepository {
    users: HashMap<u64, User>,
}
impl Repository<User, UserId> for InMemoryUserRepository {
    fn find(&self, id: UserId) -> Option<User> {
        self.users.get(&id.0).cloned() // 假设 User 可克隆
    }
    fn save(&mut self, entity: User) -> Result<(), String> {
        self.users.insert(entity.id.0, entity);
        Ok(())
    }
}
// (User 需要 Clone trait)
#[derive(Clone)]
struct User { id: UserId, name: String }
#[derive(Clone, Copy, PartialEq, Eq, Hash)] // UserId 也需要相应 traits
struct UserId(u64);


fn main() {
    // 可以注入 InMemoryUserRepository 或将来实现的 DatabaseUserRepository
    let repo = InMemoryUserRepository { users: HashMap::new() };
    let user_service = UserService { repo };

    // ... 使用 user_service ...
}
```

#### 3.5 多线程设计

泛型与 Rust 的所有权和借用系统结合，特别是在多线程编程中，用于保证线程安全。

##### 3.5.1 `Send` 与 `Sync` 约束

- `T: Send`: 表明类型 `T` 的所有权可以安全地从一个线程转移到另一个线程。
- `T: Sync`: 表明类型 `T` 的引用 (`&T`) 可以安全地在多个线程之间共享。如果 `&T` 是 `Send`，那么 `T` 就是 `Sync`。

当编写接受泛型参数的并发代码（如创建线程、使用 `Arc`, `Mutex`）时，通常需要添加 `Send` 和/或 `Sync` 约束。

```rust
use std::sync::{Arc, Mutex};
use std::thread;

// 这个函数接受一个数据 T，将其放入 Arc<Mutex<>> 中，并在新线程中修改它
// T 必须是 Send (因为所有权移入闭包，闭包可能在新线程执行)
// T 必须是 'static (因为新线程可能比当前函数活得长)
fn process_in_thread<T: Send + 'static>(data: T) {
    let shared_data = Arc::new(Mutex::new(data));
    let shared_data_clone = Arc::clone(&shared_data);

    thread::spawn(move || {
        let mut locked_data = shared_data_clone.lock().unwrap();
        // 对 locked_data (即 T) 进行操作
        println!("Processing data in thread...");
        // *locked_data = ...; // 如果需要修改
    });

    // 主线程仍然可以访问 shared_data (如果需要)
    // let main_access = shared_data.lock().unwrap();
}

fn main() {
    let my_data = vec![1, 2, 3]; // Vec<i32> is Send
    process_in_thread(my_data);

    let my_string = String::from("hello"); // String is Send
    process_in_thread(my_string);

    // let rc_ptr = std::rc::Rc::new(5); // Rc is NOT Send
    // process_in_thread(rc_ptr); // 编译错误！Rc 不能跨线程传递
}
```

##### 3.5.2 泛型并发数据结构

标准库提供了泛型的并发原语，如 `Arc<T>` (原子引用计数指针，允许多线程共享所有权) 和 `Mutex<T>` / `RwLock<T>` (提供互斥访问内部数据 `T`)。这些结构本身是泛型的，需要内部数据 `T` 满足 `Send` 和 `Sync`（对于 `Mutex` 和 `RwLock`，`T` 只需要 `Send`）。

#### 3.6 异步/同步设计

泛型在 `async/await` 语法和异步生态中扮演重要角色。

##### 3.6.1 `async` 中的泛型

`async fn` 和 `async` 块可以像普通函数一样使用泛型参数和 Trait Bounds。

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
use std::fmt::Display;

// 异步函数可以使用泛型
async fn process_item<T: Display + Send>(item: T) {
    println!("Processing item asynchronously: {}", item);
    // 模拟异步操作
    // tokio::time::sleep(std::time::Duration::from_millis(100)).await;
    println!("Finished processing: {}", item);
}

// 返回 Future 的函数也可以是泛型的
fn fetch_data<T: Send + 'static>(url: String) -> impl Future<Output = Result<T, String>> + Send {
    async move {
        println!("Fetching data from {}", url);
        // 实际的异步网络请求...
        // Ok(T::deserialize(...)) // 假设 T 可以反序列化
        Err("Not implemented".to_string()) // 示例
    }
}
```

注意，在 `async` 代码中跨 `await` 点使用的变量（被 Future 捕获的）通常需要是 `Send`，因为 Future 可能在不同的线程上恢复执行。

##### 3.6.2 泛型 Future

`Future` Trait 本身是泛型的，定义了异步操作最终产生的输出类型：

```rust
trait Future {
    type Output; // 关联类型，表示 Future 完成时返回的值的类型
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
}
```

异步函数和库经常返回 `impl Future<Output = SomeType>`，这里的 `SomeType` 可以是具体的，也可以是泛型的。泛型使得可以编写通用的异步组合器或中间件。

#### 3.7 算法设计

泛型使得可以编写与具体数据类型无关的通用算法。标准库的排序、搜索、迭代器适配器等都是泛型算法的例子。

```rust
// 泛型二分查找 (需要有序切片)
fn binary_search<T: Ord>(slice: &[T], target: &T) -> Option<usize> {
    let mut low = 0;
    let mut high = slice.len();

    while low < high {
        let mid = low + (high - low) / 2;
        match slice[mid].cmp(target) {
            std::cmp::Ordering::Less => low = mid + 1,
            std::cmp::Ordering::Greater => high = mid,
            std::cmp::Ordering::Equal => return Some(mid),
        }
    }
    None
}

fn main() {
    let numbers = [2, 3, 5, 7, 11, 13];
    assert_eq!(binary_search(&numbers, &7), Some(3));
    assert_eq!(binary_search(&numbers, &6), None);

    let words = ["apple", "banana", "grape", "orange"];
    assert_eq!(binary_search(&words, &"grape"), Some(2));
}
```

通过要求 `T: Ord` Trait Bound，`binary_search` 函数可以用于任何实现了全序比较的类型切片。

#### 3.8 迭代与递归

##### 3.8.1 泛型迭代器

Rust 的 `Iterator` Trait 是泛型的典范。它定义了一个通用的序列处理接口，并通过关联类型 `Item` 指定序列元素的类型。大量的迭代器适配器（`map`, `filter`, `zip`, `collect` 等）都是泛型方法，它们接受并返回 `impl Iterator<Item = ...>`，允许以链式调用的方式组合操作。

```rust
fn main() {
    let numbers = vec![1, 2, 3, 4, 5];

    // 链式调用泛型迭代器适配器
    let sum_of_squares_of_evens: i32 = numbers
        .into_iter() // -> impl Iterator<Item = i32>
        .filter(|&x| x % 2 == 0) // -> impl Iterator<Item = i32> (filter 也是泛型的)
        .map(|x| x * x) // -> impl Iterator<Item = i32> (map 也是泛型的)
        .sum(); // -> i32 (sum 是泛型的，作用于 Iterator<Item = N> where N: Sum)

    println!("Sum: {}", sum_of_squares_of_evens); // 输出: Sum: 20 (4 + 16)
}
```

##### 3.8.2 泛型递归结构与函数

泛型常用于定义递归数据结构，如链表、树等。

```rust
// 泛型链表
enum List<T> {
    Cons(T, Box<List<T>>), // 包含一个 T 类型的值和一个指向下一节点的 Box<List<T>>
    Nil,                  // 空列表
}

// 泛型树节点
struct TreeNode<T> {
    value: T,
    children: Vec<TreeNode<T>>,
}

// 泛型递归函数示例：计算链表长度
impl<T> List<T> {
    fn len(&self) -> usize {
        match self {
            List::Cons(_, tail) => 1 + tail.len(), // 递归调用
            List::Nil => 0,
        }
    }
}

fn main() {
    let list: List<i32> = List::Cons(1, Box::new(List::Cons(2, Box::new(List::Nil))));
    println!("List length: {}", list.len()); // 输出: List length: 2
}
```

---

### 4. 总结 (Conclusion)

Rust 泛型是其类型系统和编程范式的基石之一。它们通过**参数化多态**提供了强大的代码复用能力，同时借助 **Trait Bounds** 和**生命周期**保证了类型安全和内存安全。**单态化**机制确保了泛型抽象的零成本性能。

从基础的泛型函数、结构体、枚举，到高级的 `const` 泛型、关联类型、HRTBs，再到结合 Trait 实现的各种设计模式、并发控制、异步编程和算法设计，泛型贯穿于 Rust 编程的方方面面。

掌握 Rust 泛型对于编写高效、安全、可维护的 Rust 代码至关重要，无论是开发应用程序还是设计库，泛型都是不可或缺的工具。理解泛型的工作原理（特别是单态化与静态/动态分发的权衡）有助于做出更好的设计决策。
