# 1. Rust haskell

## 目录

- [1. Rust haskell](#1-rust-haskell)
  - [目录](#目录)
  - [1.1 Rust 与 Haskell 在范畴论支持上的对比](#11-rust-与-haskell-在范畴论支持上的对比)
    - [1.1.1 Rust 2024 的异步特性与范畴论](#111-rust-2024-的异步特性与范畴论)
      - [1.1.1.1 示例：异步单子](#1111-示例异步单子)
      - [1.1.1.2 示例：异步函子](#1112-示例异步函子)
    - [1.1.2 总结与思维导图](#112-总结与思维导图)
      - [1.1.2.1 思维导图总结](#1121-思维导图总结)
    - [1.1.3 编程建议](#113-编程建议)
    - [1.1.4 核心标准库类型和概念](#114-核心标准库类型和概念)
    - [1.1.5 类型之间的关系、转换、约束和限制](#115-类型之间的关系转换约束和限制)
    - [1.1.6 错误和异常处理规范](#116-错误和异常处理规范)
    - [1.1.7 思维导图](#117-思维导图)
    - [1.1.8 总结](#118-总结)

## 1.1 Rust 与 Haskell 在范畴论支持上的对比

1. **函子（Functor）**
   - **Haskell**: 通过 `Functor` 类型类实现，提供 `fmap` 函数。
   - **Rust**: 可以通过实现 `map` 方法的 trait 来模拟。

   ```rust
   trait Functor<T> {
       fn map<U, F: FnOnce(T) -> U>(self, f: F) -> Self::Output;
   }
   ```

2. **单子（Monad）**
   - **Haskell**: 通过 `Monad` 类型类实现，提供 `bind`（`>>=`）和 `return`。
   - **Rust**: 使用 `and_then` 和 `map` 方法来模拟。

   ```rust
   trait Monad<T>: Functor<T> {
       fn bind<U, F: FnOnce(T) -> Self::Output>(self, f: F) -> Self::Output;
   }
   ```

3. **应用函子（Applicative Functor）**
   - **Haskell**: 通过 `Applicative` 类型类实现，提供 `<*>` 和 `pure`。
   - **Rust**: 可以通过组合 `map` 和 `and_then` 来实现类似功能。

### 1.1.1 Rust 2024 的异步特性与范畴论

Rust 的异步特性主要用于处理并发和异步操作，而不是直接用于范畴论的抽象。
然而，异步特性可以与范畴论的概念结合，提供更强大的抽象能力。

#### 1.1.1.1 示例：异步单子

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

struct AsyncMonad<T> {
    value: T,
}

impl<T> AsyncMonad<T> {
    fn new(value: T) -> Self {
        AsyncMonad { value }
    }

    async fn bind<U, F>(self, f: F) -> AsyncMonad<U>
    where
        F: FnOnce(T) -> AsyncMonad<U>,
    {
        f(self.value)
    }
}

async fn example() {
    let monad = AsyncMonad::new(5);
    let result = monad.bind(|x| AsyncMonad::new(x + 1)).await;
    // 使用 result
}
```

#### 1.1.1.2 示例：异步函子

```rust
impl<T> AsyncMonad<T> {
    async fn map<U, F>(self, f: F) -> AsyncMonad<U>
    where
        F: FnOnce(T) -> U,
    {
        AsyncMonad::new(f(self.value))
    }
}

async fn example_map() {
    let monad = AsyncMonad::new(5);
    let result = monad.map(|x| x * 2).await;
    // 使用 result
}
```

### 1.1.2 总结与思维导图

Rust 的异步特性可以与范畴论的概念结合，提供强大的抽象能力，但由于语言设计的不同，Rust 并不能完全实现 Haskell 的所有范畴论特性。
Rust 更适合在系统编程和性能关键的场景中使用，而 Haskell 则在纯函数式编程和数学抽象中表现出色。

#### 1.1.2.1 思维导图总结

```text
Rust 2024 Edition
├── 异步特性
│   ├── gen
│   ├── async
│   ├── yield
│   ├── next
│   └── await
├── 范畴论概念
│   ├── Functor
│   │   └── map
│   ├── Monad
│   │   ├── bind
│   │   └── return
│   └── Applicative
│       ├── pure
│       └── apply
└── 结合与应用
    ├── 异步单子
    ├── 异步函子
    └── 编程建议
```

### 1.1.3 编程建议

1. **理解异步与同步的区别**: 在 Rust 中，异步特性主要用于处理 I/O 密集型任务。
2. **结合范畴论概念**: 使用 Rust 的 trait 系统模拟范畴论的概念。
3. **关注性能**: Rust 的设计初衷是高性能和安全性，使用异步特性时要注意性能优化。
4. **学习 Haskell**: 如果对范畴论有深入兴趣，学习 Haskell 可以提供更好的理解。

通过这些特性和建议，开发者可以在 Rust 中实现更复杂的抽象和异步操作，同时保持代码的高效和安全。

在 Rust 2024 版本中，核心标准库提供了许多类型和概念，这些类型和概念构成了 Rust 语言的基础。
以下是一些关键类型和概念的定义、最佳使用示例，以及它们之间的关系、转换、约束、限制和错误处理规范。

### 1.1.4 核心标准库类型和概念

1. **基本类型**
   - **整数类型**: `i8`, `i16`, `i32`, `i64`, `i128`, `u8`, `u16`, `u32`, `u64`, `u128`
   - **浮点类型**: `f32`, `f64`
   - **布尔类型**: `bool`
   - **字符类型**: `char`
   - **字符串类型**: `&str`, `String`

   **示例**:

   ```rust
   let x: i32 = 42;
   let y: f64 = 3.14;
   let is_active: bool = true;
   let letter: char = 'A';
   let name: &str = "Rust";
   let greeting: String = String::from("Hello, Rust!");
   ```

2. **集合类型**
   - **数组**: `[T; N]`
   - **向量**: `Vec<T>`
   - **哈希映射**: `HashMap<K, V>`
   - **哈希集合**: `HashSet<T>`

   **示例**:

   ```rust
   let numbers: [i32; 3] = [1, 2, 3];
   let mut vec = Vec::new();
   vec.push(1);
   let mut map = HashMap::new();
   map.insert("key", "value");
   ```

3. **枚举和结构体**
   - **枚举**: `enum`
   - **结构体**: `struct`

   **示例**:

   ```rust
   enum Direction {
       North,
       South,
       East,
       West,
   }

   struct Point {
       x: i32,
       y: i32,
   }
   ```

4. **错误处理**
   - **Result**: `Result<T, E>`
   - **Option**: `Option<T>`

   **示例**:

   ```rust
   fn divide(a: i32, b: i32) -> Result<i32, String> {
       if b == 0 {
           Err(String::from("Division by zero"))
       } else {
           Ok(a / b)
       }
   }

   let result = divide(10, 2);
   match result {
       Ok(value) => println!("Result: {}", value),
       Err(e) => println!("Error: {}", e),
   }
   ```

5. **智能指针**
   - **Box**: `Box<T>`
   - **Rc**: `Rc<T>`
   - **Arc**: `Arc<T>`
   - **RefCell**: `RefCell<T>`

   **示例**:

   ```rust
   use std::rc::Rc;

   let a = Rc::new(5);
   let b = Rc::clone(&a);
   ```

6. **并发**
   - **线程**: `std::thread`
   - **通道**: `std::sync::mpsc`
   - **互斥锁**: `Mutex<T>`
   - **读写锁**: `RwLock<T>`

   **示例**:

   ```rust
   use std::thread;
   use std::sync::mpsc;
   use std::sync::Mutex;
   use std::sync::Arc;

   let (tx, rx) = mpsc::channel();
   let data = Arc::new(Mutex::new(0));

   let tx1 = tx.clone();
   let data1 = Arc::clone(&data);
   thread::spawn(move || {
       let mut num = data1.lock().unwrap();
       *num += 1;
       tx1.send(*num).unwrap();
   });

   println!("Received: {}", rx.recv().unwrap());
   ```

### 1.1.5 类型之间的关系、转换、约束和限制

- **转换**: 使用 `as` 关键字进行基本类型转换。
- **约束**: 使用 trait bounds 限制泛型类型。
- **限制**: Rust 的所有权和借用系统限制了数据的使用方式，确保内存安全。

### 1.1.6 错误和异常处理规范

- **Result 和 Option**: 使用 `match` 或 `?` 操作符处理。
- **Panic**: 使用 `panic!` 宏引发运行时错误，通常用于不可恢复的错误。

### 1.1.7 思维导图

```text
Rust 2024 Core Library
├── 基本类型
│   ├── 整数
│   ├── 浮点
│   ├── 布尔
│   ├── 字符
│   └── 字符串
├── 集合类型
│   ├── 数组
│   ├── 向量
│   ├── 哈希映射
│   └── 哈希集合
├── 枚举和结构体
│   ├── 枚举
│   └── 结构体
├── 错误处理
│   ├── Result
│   └── Option
├── 智能指针
│   ├── Box
│   ├── Rc
│   ├── Arc
│   └── RefCell
└── 并发
    ├── 线程
    ├── 通道
    ├── 互斥锁
    └── 读写锁
```

### 1.1.8 总结

Rust 2024 的核心标准库提供了丰富的类型和概念，支持高效、安全的系统编程。
通过理解这些类型的关系、转换、约束和限制，开发者可以编写出高性能且安全的代码。
错误处理规范确保了程序的健壮性，而并发特性则提供了强大的多线程支持。
