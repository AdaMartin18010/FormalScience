# Rust 1.86.0 特性分析

## 目录

- [Rust 1.86.0 特性分析](#rust-1860-特性分析)
  - [目录](#目录)
  - [引言](#引言)
  - [主要特性](#主要特性)
    - [`impl Trait` in Associated Types](#impl-trait-in-associated-types)
    - [新的 Lint: `INCOMPATIBLE_FRAGMENT_MATCH`](#新的-lint-incompatible_fragment_match)
    - [稳定的 API](#稳定的-api)
  - [思维导图](#思维导图)
  - [总结](#总结)

## 引言

Rust 1.86.0 版本于 2024 年 2 月 29 日发布。
此版本带来了一些重要的语言和库特性稳定化，以及一些编译器和 Cargo 的改进。
本分析将重点介绍几个关键特性，并提供示例和论证。

## 主要特性

### `impl Trait` in Associated Types

- **特性描述:**
    此版本稳定了在 `trait` 关联类型（Associated Types）中使用 `impl Trait` 的能力。
    这意味着你可以在 `trait` 实现中，为关联类型指定一个实现了特定 `trait` 的“不透明”类型，而无需显式命名该类型。
    这对于返回复杂或未命名类型（如闭包或迭代器）特别有用。

- **示例:**

    ```rust
    use std::future::Future;

    // 定义一个异步任务执行器的 Trait
    trait Executor {
        // 关联类型 TaskFuture 使用 impl Trait
        // 它表示一个实现了 Future<Output = ()> 的类型
        type TaskFuture: Future<Output = ()>;

        // 定义一个执行任务的方法，返回 TaskFuture
        fn execute(&self, id: usize) -> Self::TaskFuture;
    }

    // 实现 Executor Trait
    struct MyExecutor;

    impl Executor for MyExecutor {
        // 使用 async 块，其返回类型是匿名的，但实现了 Future<Output = ()>
        // 通过 `impl Trait`，我们可以轻松地将其赋给关联类型
        type TaskFuture = impl Future<Output = ()>;

        fn execute(&self, id: usize) -> Self::TaskFuture {
            // 返回一个 async 块，它符合 Future<Output = ()> 的约束
            async move {
                println!("Executing task {id}");
                // 模拟异步工作
                tokio::time::sleep(std::time::Duration::from_millis(100)).await;
                println!("Task {id} finished");
            }
        }
    }

    // 使用示例 (需要 Tokio 或其他异步运行时)
    // #[tokio::main]
    // async fn main() {
    //     let executor = MyExecutor;
    //     let future1 = executor.execute(1);
    //     let future2 = executor.execute(2);
    //     future1.await;
    //     future2.await;
    // }
    ```

- **论证:**
  - **简化代码:** 在关联类型必须返回复杂类型（如 `async fn` 返回的 `Future` 或迭代器适配器链）时，无需手动定义一个 `struct` 或 `enum` 来包装它们，代码更简洁。
  - **隐藏实现细节:** 调用者只知道关联类型实现了某个 `trait`，而不需要关心具体的返回类型，提高了封装性。
  - **提升表达能力:** 使得在 `trait` 定义和实现中处理 `async/await` 和迭代器更加自然和符合人体工程学。

### 新的 Lint: `INCOMPATIBLE_FRAGMENT_MATCH`

- **特性描述:**
    引入了一个新的 `warn-by-default` lint，名为 `INCOMPATIBLE_FRAGMENT_MATCH`。
    此 lint 会检测宏规则中可能无法匹配所有可能输入的片段说明符（fragment specifiers）。
    例如，当一个宏接受 `$:expr` 但在实现中试图将其与 `$:literal` 匹配时，这个 lint 会发出警告，因为并非所有表达式都是字面量。

- **示例:**

    ```rust
    macro_rules! check_expr {
        // 这个宏接受任何表达式 $:expr
        ($e:expr) => {
            // 但内部尝试将其与字面量 $:literal 匹配
            // 这可能导致问题，因为 $e 不一定是字面量
            match $e {
                // 如果 $e 不是字面量（例如 x + 1），这里会编译失败
                // Rust 1.86 会对此情况发出 INCOMPATIBLE_FRAGMENT_MATCH 警告
                // macro_rules! _internal { ($l:literal) => { println!("Literal: {}", $l); } }
                // _internal!($e) // 潜在问题点

                // 更安全的做法可能是直接处理表达式
                 _ => println!("Expression: {}", stringify!($e))
            }
        };
    }

    fn main() {
        let x = 5;
        check_expr!(10); // OK，10 是字面量
        check_expr!(x + 1); // 以前可能编译失败，现在会有 lint 警告
    }
    ```

- **论证:**
  - **提高宏的健壮性:** 帮助宏作者在编译时发现潜在的类型不匹配问题，避免运行时错误或意外行为。
  - **改善开发者体验:** 及早发现宏定义中的逻辑错误，减少调试时间。
  - **促进最佳实践:** 鼓励更精确地使用片段说明符，编写更可靠的宏。

### 稳定的 API

Rust 1.86.0 稳定了多个之前在 `nightly` 版本中可用的 API。以下是一些值得注意的例子：

- **`Option::contains`**: `Option<T>` 现在有了一个 `contains` 方法，用于检查 `Option` 是否为 `Some` 并且其内部值等于给定值。

  - **示例:**

```rust
let opt1 = Some(5);
let opt2: Option<i32> = None;

assert!(opt1.contains(&5));
assert!(!opt1.contains(&6));
assert!(!opt2.contains(&0)); // 对于 None，总是返回 false
```

- **论证:** 提供了一种更简洁、更易读的方式来检查 `Option` 是否包含特定值，替代了常见的 `map_or(false, |v| v == expected)` 模式。

- **`Duration` formatting with `%N`**: `Duration` 类型在格式化时可以使用 `%N` 来表示纳秒部分。

  - **示例:**

    ```rust
    // (需要 nightly 或等待 chrono 等库更新以支持此格式)
    // 概念示例:
    // let d = std::time::Duration::new(1, 123_456_789);
    // let formatted = format!("Duration: {}.{:09}s", d.as_secs(), d.subsec_nanos()); // 旧方式
    // let formatted_new = format!("Duration: {}.%Ns", d.as_secs(), d.subsec_nanos()); // 概念上的新方式 (具体实现依赖库)
    // println!("{}", formatted);
    // 实际稳定的是 std::fmt 对 Duration 的底层支持，让库可以使用这个特性
    ```

  - **论证:** 为处理高精度时间戳的库（如 `chrono`）提供了更灵活和标准的格式化选项。

- **其他:** 还包括一些内存操作、I/O 安全性和其他方面的 API 稳定化。

- **总体论证:**
  - **增强标准库功能:** 为开发者提供了更多开箱即用的工具，减少了对第三方库或自定义实现的依赖。
  - **提升代码质量:** 提供了更符合人体工程学、更不易出错的 API。
  - **保持生态一致性:** 稳定常用功能，使整个 Rust 生态系统受益。

## 思维导图

```text
Rust 1.86.0
├── 语言特性
│   └── impl Trait in Associated Types
│       ├── 描述: 允许在 trait 的关联类型中使用 impl Trait
│       ├── 优点:
│       │   ├── 简化代码 (处理 Future, Iterator 等)
│       │   ├── 隐藏实现细节
│       │   └── 提升表达能力
│       └── 示例: 异步 Executor trait
├── Lints
│   └── INCOMPATIBLE_FRAGMENT_MATCH
│       ├── 描述: 检测宏中不兼容的片段说明符匹配
│       ├── 优点:
│       │   ├── 提高宏健壮性
│       │   ├── 改善开发者体验
│       │   └── 促进最佳实践
│       └── 示例: 宏接受 expr 但内部匹配 literal
├── 库特性 (API 稳定化)
│   ├── Option::contains(&T)
│   │   ├── 描述: 检查 Option<T> 是否为 Some(v) 且 v == &T
│   │   └── 优点: 更简洁、易读
│   ├── Duration formatting (%N)
│   │   ├── 描述: 支持使用 %N 格式化纳秒
│   │   └── 优点: 更灵活的时间格式化
│   └── 其他 API
│       ├── 内存操作
│       └── I/O 安全性
└── 其他改进
    ├── 编译器性能/错误信息
    └── Cargo 功能增强
```

## 总结

Rust 1.86.0 继续在语言表达能力、开发者体验和标准库功能方面进行稳步改进。
`impl Trait` 在关联类型中的稳定化显著提升了处理异步代码和迭代器的便利性。
新的 `INCOMPATIBLE_FRAGMENT_MATCH` lint 则有助于编写更健壮的宏。
一系列稳定的 API 进一步丰富了标准库，使得常见任务的实现更加简洁和高效。
这些改进共同推动了 Rust 向着更强大、更易用的方向发展。
