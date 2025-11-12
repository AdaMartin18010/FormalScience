# Rust 的函数式编程模式

Rust 作为一种多范式编程语言，支持函数式编程，并提供了多种函数式编程模式。
以下是一些常见的函数式编程模式及其在 Rust 中的应用：

1. **闭包 (Closures)**：
   - 闭包是 Rust 中的匿名函数，可以捕获其上下文中的变量。
   闭包可以用于封装状态和行为，提供代码封装和复用。
   - **示例代码**：
  
     ```rust
     fn main() {
         let text = "Hello".to_string();
         // 不可变引用闭包
         let print = || println!("{}", text);
         print();

         let mut count = 0;
         // 可变引用闭包
         let mut increment = || count += 1;
         increment();
         println!("Count: {}", count);

         let value = 10;
         // 值拷贝闭包
         let square = || value * value;
         println!("Square: {}", square());
     }
     ```

2. **柯里化 (Currying)**：
   - 柯里化是将一个多参数的函数转换成多个单参数函数的过程。
     柯里化可以增加函数的灵活性和复用性。

   - **示例代码**：

     ```rust
     fn add(x: i32) -> Box<dyn Fn(i32) -> i32> {
         Box::new(move |y| x + y)
     }

     fn main() {
         let add_five = add(5);
         println!("Result of add_five(3): {}", add_five(3));
     }
     ```

3. **部分施用 (Partial Application)**：
   - 部分施用是固定函数的某些参数，返回一个新的函数。
     部分施用允许函数参数的部分应用，提供延迟执行的能力。

   - **示例代码**：

     ```rust
     fn multiply(x: i32, y: i32) -> i32 {
         x * y
     }

     fn partially_apply<F>(f: F, x: i32) -> Box<dyn Fn(i32) -> i32>
     where
         F: Fn(i32, i32) -> i32,
     {
         Box::new(move |y| f(x, y))
     }

     fn main() {
         let multiply_by_three = partially_apply(multiply, 3);
         println!("Result of multiply_by_three(4): {}", multiply_by_three(4));
     }
     ```

4. **组合 (Function Composition)**：
   - 组合是将多个函数组合成一个新函数，其中每个函数的输出成为下一个函数的输入。
     组合可以将多个简单函数组合成复杂操作。

   - **示例代码**：

     ```rust
     fn double(x: i32) -> i32 {
         x * 2
     }

     fn increment(x: i32) -> i32 {
         x + 1
     }

     fn compose(functions: Vec<Box<dyn Fn(i32) -> i32>>) -> Box<dyn Fn(i32) -> i32> {
         let mut result = Box::new(|_| 0); // 初始函数，不进行任何操作
         for f in functions.into_iter().rev() {
             result = Box::new(move |x| f((*result)(x)));
         }
         result
     }

     fn main() {
         let composed = compose(vec![Box::new(double), Box::new(increment), Box::new(increment)]);
         println!("Result of composed(5): {}", composed(5));
     }
     ```

5. **高阶函数 (Higher-order Functions)**：
   - 高阶函数是指接受函数作为参数或返回函数的函数。
     高阶函数可以增加代码的抽象能力，使函数能够操作其他函数。

   - **示例代码**：

     ```rust
     fn apply<F, T>(f: F, x: T) -> T
     where
         F: FnOnce(T),
     {
         f(x)
     }

     fn square(x: i32) -> i32 {
         x * x
     }

     fn main() {
         let result = apply(square, 4);
         println!("Result of square: {}", result);
     }
     ```

6. **迭代器 (Iterators)**：
   - 迭代器是 Rust 中处理元素序列的一种方式。
     迭代器可以用于遍历集合、过滤数据、映射数据等。

   - **示例代码**：

     ```rust
     fn main() {
         let numbers = vec![1, 2, 3, 4, 5];
         let even_numbers: Vec<_> = numbers.iter()
             .filter(|&x| x % 2 == 0)
             .map(|x| x * 2)
             .collect();
         println!("Even numbers: {:?}", even_numbers);
     }
     ```

## 📋 目录

- [1 热门的 Rust 函数式编程库](#1-热门的-rust-函数式编程库)
  - [1.1 年更新的软件库](#11-年更新的软件库)
  - [1.2 思维总结](#12-思维总结)
  - [1.3 闭包 (Closures)](#13-闭包-closures)
  - [1.4 迭代器 (Iterators)](#14-迭代器-iterators)
  - [1.5 高阶函数 (Higher-order Functions)](#15-高阶函数-higher-order-functions)
  - [1.6 不可变性 (Immutability)](#16-不可变性-immutability)
  - [1.7 纯函数 (Pure Functions)](#17-纯函数-pure-functions)
  - [1.8 模式匹配 (Pattern Matching)](#18-模式匹配-pattern-matching)
  - [1.9 枚举 (Enums)](#19-枚举-enums)
  - [1.10 总结](#110-总结)
  - [1.11 Definition and Characteristics](#111-definition-and-characteristics)
  - [1.12 Benefits of Pure Functions](#112-benefits-of-pure-functions)
  - [1.13 Examples of Pure Functions](#113-examples-of-pure-functions)
  - [1.14 Writing Pure Functions in Rust](#114-writing-pure-functions-in-rust)
  - [1.15 Pitfalls and Considerations](#115-pitfalls-and-considerations)
  - [1.16 Optimization and Performance](#116-optimization-and-performance)
  - [1.17 Conclusion](#117-conclusion)
  - [1.18 Avoid Mutating External State](#118-avoid-mutating-external-state)
  - [1.19 Restrict InputOutput Operations](#119-restrict-inputoutput-operations)
  - [1.20 Eliminate Mutable State Mutations](#120-eliminate-mutable-state-mutations)
  - [1.21 Avoid Concurrency Primitives](#121-avoid-concurrency-primitives)
  - [1.22 Use Immutability and Ownership](#122-use-immutability-and-ownership)
  - [1.23 Leverage Type System and Compiler](#123-leverage-type-system-and-compiler)
  - [1.24 Use Tools and Lints](#124-use-tools-and-lints)
  - [1.25 Testing](#125-testing)
  - [1.26 Example Pure Rust Function](#126-example-pure-rust-function)
  - [1.27 Summary](#127-summary)

---

## 1 热门的 Rust 函数式编程库

1. **fp-core.rs**：
   - `fp-core.rs` 是一个专门为 Rust 语言设计的函数式编程库，提供了丰富的纯函数式数据结构和高阶函数。它旨在补充标准库中功能编程方面的需求，让开发者能够更优雅地在 Rust 中实践函数式编程范式。
   - **项目地址**：[fp-core.rs](https://gitcode.com/gh_mirrors/fp/fp-core.rs)

2. **higher**：
   - `higher` 是一个为 Rust 语言设计的开源库，旨在实现函数式编程中的高阶抽象，如函子（Functor）、应用函子（Applicative）和单子（Monad）。这个库受到了 PureScript 和 Scala 的 Cats 库的启发，提供了一系列细粒度的 trait。
   - **项目地址**：[higher](https://gitcode.com/gh_mirrors/hig/higher)

### 1.1 年更新的软件库

截至 2025 年，Rust 语言本身和其生态系统仍在不断更新和发展。以下是一些 2025 年更新的软件库和工具：

1. **Rust 1.85.0**：
   - Rust 1.85.0 稳定版主要更新内容包括：
     - **Rust 2024 版**：Rust 2024 版正式稳定发布，带来多项语言、标准库、Cargo、Rustdoc 和 Rustfmt 的更新。
     - **异步闭包**：Rust 现在支持异步闭包 `async || {}`，调用时返回 `futures`。
     - **隐藏 trait 实现诊断信息**：新增 `#[diagnostic::do_not_recommend]` 属性，可让编译器在诊断消息中不显示注解的 trait 实现。

2. **fastembed-rs**：
   - `fastembed-rs` 是一个 AI 嵌入库，提供了快速的文本嵌入、图像嵌入和候选项重新排序功能。它具有以下主要特性：
     - 支持同步使用，无需依赖 Tokio。
     - 使用 `@pykeio/ort` 进行高性能的 ONNX 推理。
     - 使用 `@huggingface/tokenizers` 进行快速编码。
     - 支持使用 `@rayon-rs/rayon` 进行批量嵌入生成和并行计算。
   - **项目地址**：[fastembed-rs](https://github.com/Anush008/fastembed-rs)

### 1.2 思维总结

1. **函数式编程模式**：
   - Rust 提供了多种函数式编程模式，如闭包、柯里化、部分施用、组合和高阶函数。这些模式可以提高代码的可读性和灵活性，使代码更加简洁和易于维护。

2. **热门库**：
   - `fp-core.rs` 和 `higher` 是两个热门的 Rust 函数式编程库，提供了丰富的函数式数据结构和高阶抽象，适合在 Rust 中实践函数式编程。

3. **2025 年更新**：
   - Rust 1.85.0 和 `fastembed-rs` 是 2025 年更新的软件库，提供了新的功能和改进，适合在 Rust 项目中使用。

通过这些模式和库，Rust 开发者可以更有效地编写函数式代码，提高代码的可维护性和性能。

Rust 支持函数式编程范式，并提供了多种特性来实现函数式编程。
以下是 Rust 中函数式编程支持的特性及其核心概念的定义解释：

### 1.3 闭包 (Closures)

**定义**：
闭包是 Rust 中的匿名函数，可以捕获其定义环境中的变量。
闭包可以存储在变量中，作为参数传递给其他函数，或者作为函数的返回值。

**特性**：

- 闭包可以捕获定义时的作用域中的变量。
- 闭包的参数类型和返回值类型可以由 Rust 自动推断。
- 闭包可以使用 `move` 关键字将捕获的变量的所有权转移到闭包中。

**示例代码**：

```rust
fn main() {
    let name = "Rustacean";
    let greet = || {
        println!("Hello, {}!", name);
    };
    greet();
}
```

在这个例子中，闭包 `greet` 捕获了变量 `name`，并在执行时使用它。

### 1.4 迭代器 (Iterators)

**定义**：
迭代器是 Rust 中处理元素序列的一种方式。
迭代器允许对集合中的每个元素执行某些操作，而不需要显式地遍历集合。

**特性**：

- 迭代器是惰性的，即创建迭代器后不会立即执行操作，只有在调用方法时才会执行。
- 迭代器可以使用多种适配器方法（如 `filter`、`map`、`fold` 等）来处理元素。
- 迭代器可以生成不可变引用、可变引用或获取所有权的迭代器。

**示例代码**：

```rust
fn main() {
    let numbers = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    let result: i32 = numbers
        .iter()
        .filter(|&&x| x % 2 == 0)
        .map(|&x| x * x)
        .sum();
    println!("Sum of squares of even numbers: {}", result);
}
```

在这个例子中，我们使用迭代器的 `filter` 方法筛选出偶数，使用 `map` 方法对每个偶数进行平方操作，最后使用 `sum` 方法计算总和。

### 1.5 高阶函数 (Higher-order Functions)

**定义**：
高阶函数是指接受其他函数作为参数或返回函数作为结果的函数。
高阶函数可以增加代码的抽象能力和灵活性。

**特性**：

- 高阶函数可以接受闭包或函数指针作为参数。
- 高阶函数可以返回闭包或函数指针作为结果。
- 高阶函数可以用于实现通用的算法和操作。

**示例代码**：

```rust
fn apply<F, T>(f: F, x: T) -> T
where
    F: FnOnce(T) -> T,
{
    f(x)
}

fn main() {
    let result = apply(|x| x * 2, 5);
    println!("Result: {}", result);
}
```

在这个例子中，`apply` 函数接受一个闭包 `f` 和一个值 `x`，并返回 `f(x)` 的结果。

### 1.6 不可变性 (Immutability)

**定义**：
不可变性是指数据一旦被初始化后，就不能被修改。
不可变性有助于减少错误和提高代码的可维护性。

**特性**：

- 在 Rust 中，变量默认是不可变的，需要使用 `mut` 关键字来声明可变变量。
- 不可变性可以减少副作用，使代码更加安全和可预测。

**示例代码**：

```rust
fn main() {
    let x = 5; // 不可变变量
    println!("x is {}", x);
}
```

在这个例子中，变量 `x` 是不可变的，不能被修改。

### 1.7 纯函数 (Pure Functions)

**定义**：
纯函数是指没有副作用的函数，其输出只依赖于输入参数，而不依赖于任何外部状态。

**特性**：

- 纯函数的输出是可预测的，因为它们不依赖于外部状态。
- 纯函数更容易测试和维护，因为它们的行为是确定的。

**示例代码**：

```rust
fn add(a: i32, b: i32) -> i32 {
    a + b
}

fn main() {
    let result = add(2, 3);
    println!("Result: {}", result);
}
```

在这个例子中，`add` 函数是一个纯函数，其输出只依赖于输入参数 `a` 和 `b`。

### 1.8 模式匹配 (Pattern Matching)

**定义**：
模式匹配是 Rust 中的一种强大工具，用于匹配和解构数据结构。
模式匹配可以用于 `match` 表达式和 `if let` 语句中。

**特性**：

- 模式匹配可以用于匹配枚举、结构体、元组等数据结构。
- 模式匹配可以用于解构复杂的数据结构，提取其中的值。

**示例代码**：

```rust
enum TrafficLight {
    Red,
    Yellow,
    Green,
}

fn main() {
    let light = TrafficLight::Green;
    match light {
        TrafficLight::Red => println!("Stop"),
        TrafficLight::Yellow => println!("Caution"),
        TrafficLight::Green => println!("Go"),
    }
}
```

在这个例子中，我们使用 `match` 表达式来匹配 `TrafficLight` 枚举的值，并根据匹配结果执行不同的操作。

### 1.9 枚举 (Enums)

**定义**：
枚举是 Rust 中的一种数据类型，用于表示一组命名的值。
枚举可以包含数据，也可以不包含数据。

**特性**：

- 枚举可以用于表示一组相关的值，如状态、错误类型等。
- 枚举可以包含数据，用于存储额外的信息。

**示例代码**：

```rust
enum TrafficLight {
    Red,
    Yellow,
    Green,
}

fn main() {
    let light = TrafficLight::Green;
    match light {
        TrafficLight::Red => println!("Stop"),
        TrafficLight::Yellow => println!("Caution"),
        TrafficLight::Green => println!("Go"),
    }
}
```

在这个例子中，我们定义了一个 `TrafficLight` 枚举，用于表示交通灯的状态。

### 1.10 总结

Rust 提供了多种函数式编程特性，包括闭包、迭代器、高阶函数、不可变性、纯函数、模式匹配和枚举。
这些特性使得 Rust 代码更加简洁、可读和可维护，同时提高了代码的安全性和性能。
通过这些特性，Rust 开发者可以编写出高效、可靠的函数式代码。

In Rust, pure functions are functions that have no side effects and whose output depends only on their input parameters. Here are some key points about pure functions in Rust:

### 1.11 Definition and Characteristics

- **No Side Effects**: A pure function does not modify any external state, such as global variables or static variables. It only operates on its input parameters and returns a result based on those inputs.
- **Deterministic Output**: For a given set of input parameters, a pure function will always return the same output. This predictability makes pure functions easier to reason about and test.

### 1.12 Benefits of Pure Functions

- **Easier to Test**: Since pure functions do not rely on external state, they can be tested in isolation without worrying about setup or teardown of external resources.
- **Concurrency-Friendly**: Pure functions are thread-safe because they do not modify shared state, making them suitable for concurrent programming.
- **Cacheable**: The results of pure functions can be cached, as the output is solely determined by the input. This can lead to performance optimizations.

### 1.13 Examples of Pure Functions

- **Simple Arithmetic Operations**:

  ```rust
  fn add(x: i32, y: i32) -> i32 {
      x + y
  }
  ```

  This function is pure because it only depends on its input parameters and does not modify any external state.

- **String Manipulation**:

  ```rust
  fn to_uppercase(s: &str) -> String {
      s.to_uppercase()
  }
  ```

  This function is pure as it only operates on the input string and returns a new string without modifying any external state.

### 1.14 Writing Pure Functions in Rust

- **Avoiding Mutable State**: To write pure functions, avoid using `mut` keywords for variables that are not intended to be modified. If mutation is necessary, ensure it is limited to local variables within the function.
- **Using Immutability**: By default, variables in Rust are immutable. This encourages the use of immutable data and helps in writing pure functions.

### 1.15 Pitfalls and Considerations

- **Avoiding `unsafe` Code**: Using `unsafe` blocks can introduce side effects and violate the purity of a function. Therefore, pure functions should avoid `unsafe` code unless absolutely necessary.
- **Handling External Dependencies**: Functions that depend on external resources (e.g., file I/O, network requests) are generally not pure. To maintain purity, consider abstracting these dependencies behind interfaces or using mocking in tests.

### 1.16 Optimization and Performance

- **Compiler Optimizations**: Pure functions allow the compiler to perform optimizations such as common subexpression elimination and loop optimizations, as it can assume that the function's behavior is consistent across calls.
- **Memoization**: Since pure functions produce the same output for the same input, their results can be memoized, which can significantly improve performance in scenarios with repeated computations.

### 1.17 Conclusion

Pure functions are a fundamental concept in functional programming and are well-supported in Rust. By adhering to the principles of no side effects and deterministic output, developers can write code that is easier to understand, test, and maintain. Rust's strict ownership model and emphasis on immutability make it well-suited for implementing pure functions, contributing to the language's reputation for safety and performance.

Ensuring your Rust functions are pure involves several key practices and considerations. Here's a structured approach:

### 1.18 Avoid Mutating External State

- **No Global/Static Variables**: Pure functions shouldn't modify or rely on global/static mutable state. Use `const` or `immutable static` for constants.
- **Interior Mutability**: Avoid `std::cell` types (e.g., `RefCell`, `Cell`) unless necessary for safe mutable statics, and ensure their usage doesn’t affect purity.

### 1.19 Restrict InputOutput Operations

- **No I/O**: Functions that read/write files, network, or console (e.g., `std::fs`, `std::io`, `println!`) are impure. Isolate such logic outside pure functions.
- **External Systems**: Avoid system calls, time/date functions (unless parametersized), or external randomness.

### 1.20 Eliminate Mutable State Mutations

- **Parameters and Transforms**: Pure functions should only transform inputs into outputs. Example:

     ```rust
     fn double(x: i32) -> i32 {
         x * 2
     }
     ```

- **No `mut` or `unsafe`**: Avoid `mut` for parameters unless adapting to external libraries. Avoid `unsafe` unless essential, and ensure it doesn’t introduce side effects.

### 1.21 Avoid Concurrency Primitives

- **No Shared State**: Locks, channels (`std::sync::Mutex`, `std::sync::mpsc`), or thread-unsafe mutable data make a function impure. Use atomic primitives only if their operations are predictable (e.g., atomic reads).

### 1.22 Use Immutability and Ownership

- **Immutable Parameters**: Functions with `&self` methods (immutably borowed) are more likely pure.
- **Ownership**: Transferring ownership (e.g., `Vec<T>` passed by value) can retain purity if the function doesn’t mutate externally visible state.

### 1.23 Leverage Type System and Compiler

- **`const fn`**: Mark functions `const fn` if they can be evaluated at compile time, enforcing purity.
- **Compiler Checks**: Rust’s borrow checker detects modifications to owned/borrowed data, helping avoid unintended mutability.

### 1.24 Use Tools and Lints

- **Clippy**: Use `cargo clippy` with lints like `clippy::unnecessary_mut_passed` to catch impure patterns.
- **Documentation**: Annotate pure functions with `#[must_use]` to signal they’re intended for their return value, not side effects.

### 1.25 Testing

- **Deterministic Behavior**: Test functions with multiple inputs to ensure outputs are consistent.
- **Property-Based Testing**: Tools like `proptest` help verify functions behave predictably under various inputs.

### 1.26 Example Pure Rust Function

```rust
// A pure Rust function
fn add(a: i32, b: i32) -> i32 {
    a + b
}

// Using it:
fn main() {
    assert_eq!(add(2, 3), 5); // Always returns 5
}
```

### 1.27 Summary

To ensure purity in Rust:

- Design functions to depend only on input parameters.
- Avoid mutable state, I/O, and concurrency.
- Use immutable types and ownership.
- Leverage `const fn`, Clippy, and testing.
- Document and restrict side effects in interfaces.
