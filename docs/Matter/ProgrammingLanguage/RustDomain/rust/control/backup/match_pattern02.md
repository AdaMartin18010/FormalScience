# Rust Pattern Matching Syntax

Here is a comprehensive summary of Rust's pattern matching syntax,
including detailed examples for each concept and a mind map:

## 📋 目录

- [1 Match Expressions](#1-match-expressions)
- [2 Pattern Types](#2-pattern-types)
- [3 Pattern Matching Examples](#3-pattern-matching-examples)
- [4 Mind Map](#4-mind-map)
  - [4.1 错误处理](#41-错误处理)
  - [4.2 可选值处理](#42-可选值处理)
  - [4.3 循环和流处理](#43-循环和流处理)
  - [4.4 特定业务逻辑](#44-特定业务逻辑)
  - [4.5 数据解析](#45-数据解析)
  - [4.6 总结](#46-总结)
  - [4.7 解释](#47-解释)
    - [7.7.1 Trait Object 的定义和使用](#771-trait-object-的定义和使用)
    - [7.7.2 解构语法的限制](#772-解构语法的限制)
  - [4.8 解决方案](#48-解决方案)
  - [4.9 总结](#49-总结)

---

## 1 Match Expressions

- `match` expression
  - Syntax: `match scrutinee { patterns => expressions, ... }`
  - Example:

    ```rust
    let x = 1;
    match x {
        1 => println!("one"),
        2 => println!("two"),
        _ => println!("other"),
    }
    ```

## 2 Pattern Types

- Literal Patterns
  - Match specific values
  - Example: `1`, `true`, `"string"`

- Variable Patterns
  - Bind values to variables
  - Example: `x`, `y`

- Wildcard Pattern
  - Match any value
  - Example: `_`

- Rest Pattern
  - Match remaining elements in a tuple or slice
  - Example: `..`

- Struct Patterns
  - Match struct fields
  - Example:

    ```rust
    struct Point {
        x: i32,
        y: i32,
    }
    let p = Point { x: 10, y: 20 };
    match p {
        Point { x: 10, y: 20 } => println!("Matched point (10, 20)"),
        Point { .. } => println!("Matched some point"),
    }
    ```

- Tuple Patterns
  - Match tuple elements
  - Example:

    ```rust
    let pair = (1, 2);
    match pair {
        (1, 2) => println!("Matched (1, 2)"),
        _ => println!("Matched some other tuple"),
    }
    ```

- Slice Patterns
  - Match slice elements
  - Example:

    ```rust
    let numbers = [1, 2, 3];
    match numbers {
        [1, 2, 3] => println!("Matched the exact slice"),
        [.., 3] => println!("Matched a slice ending with 3"),
        _ => println!("Matched some other slice"),
    }
    ```

- Enum Patterns
  - Match enum variants
  - Example:

    ```rust
    enum Message {
        Quit,
        Move { x: i32, y: i32 },
    }
    let msg = Message::Move { x: 10, y: 20 };
    match msg {
        Message::Quit => println!("Quit"),
        Message::Move { x, y } => println!("Move to ({}, {})", x, y),
    }
    ```

- Range Patterns
  - Match values within a range
  - Example:

    ```rust
    let x = 10;
    match x {
        1..=5 => println!("Between 1 and 5"),
        6..=10 => println!("Between 6 and 10"),
        _ => println!("Outside the range"),
    }
    ```

- Reference Patterns
  - Match references to values
  - Example:

    ```rust
    let x = 10;
    match &x {
        &10 => println!("Matched 10"),
        _ => println!("Matched some other value"),
    }
    ```

- Guarded Patterns
  - Add additional conditions to patterns
  - Example:

    ```rust
    let x = 10;
    match x {
        n if n > 0 => println!("Positive number"),
        n if n < 0 => println!("Negative number"),
        _ => println!("Zero"),
    }
    ```

## 3 Pattern Matching Examples

- Basic Match

  ```rust
  let x = 1;
  match x {
      1 => println!("one"),
      2 => println!("two"),
      _ => println!("other"),
  }
  ```

- Enum Match

  ```rust
  enum Message {
      Quit,
      Move { x: i32, y: i32 },
  }
  let msg = Message::Move { x: 10, y: 20 };
  match msg {
      Message::Quit => println!("Quit"),
      Message::Move { x, y } => println!("Move to ({}, {})", x, y),
  }
  ```

- Struct Match

  ```rust
  struct Point {
      x: i32,
      y: i32,
  }
  let p = Point { x: 10, y: 20 };
  match p {
      Point { x: 10, y: 20 } => println!("Matched point (10, 20)"),
      Point { .. } => println!("Matched some point"),
  }
  ```

- Slice Match

  ```rust
  let numbers = [1, 2, 3];
  match numbers {
      [1, 2, 3] => println!("Matched the exact slice"),
      [.., 3] => println!("Matched a slice ending with 3"),
      _ => println!("Matched some other slice"),
  }
  ```

- Guarded Match

  ```rust
  let x = 10;
  match x {
      n if n > 0 => println!("Positive number"),
      n if n < 0 => println!("Negative number"),
      _ => println!("Zero"),
  }
  ```

## 4 Mind Map

```mermaid
graph TD
    A[Pattern Matching] --> B[Match Expressions]
    A --> C[Pattern Types]
    B --> D[match scrutinee { patterns => expressions, ... }]
    C --> E[Literal Patterns]
    C --> F[Variable Patterns]
    C --> G[Wildcard Pattern]
    C --> H[Rest Pattern]
    C --> I[Struct Patterns]
    C --> J[Tuple Patterns]
    C --> K[Slice Patterns]
    C --> L[Enum Patterns]
    C --> M[Range Patterns]
    C --> N[Reference Patterns]
    C --> O[Guarded Patterns]
    I --> P[Struct { field1: value1, field2: value2 }]
    J --> Q[(value1, value2)]
    K --> R[[value1, value2, ..]]
    L --> S[EnumVariant { field1: value1 }]
    M --> T[1..=5]
    N --> U[&value]
    O --> V[n if n > 0]
```

This comprehensive summary covers the syntax and usage of Rust's pattern matching,
including detailed examples for each type of pattern.
The mind map provides a visual representation of the different aspects of pattern matching in Rust.

Rust 的模式匹配在项目中应用广泛，主要用于以下场景：

### 4.1 错误处理

- **`match` 与 `Result`**：
  用于处理可能失败的操作，如文件操作、网络请求等。
  当函数返回 `Result<T, E>` 类型时，可以用 `match` 来处理 `Ok` 和 `Err` 情况。

  ```rust
  use std::fs::File;
  use std::io::Read;

  fn read_file(path: &str) -> std::io::Result<String> {
      let mut file = File::open(path)?;
      let mut content = String::new();
      file.read_to_string(&mut content)?;
      Ok(content)
  }

  fn main() {
      match read_file("example.txt") {
          Ok(content) => println!("File content: {}", content),
          Err(err) => println!("Error reading file: {}", err),
      }
  }
  ```

### 4.2 可选值处理

- **`Option` 与 `if let`**：
  处理可能存在或不存在的值。
  当函数返回 `Option<T>` 类型时，可以使用 `if let` 来处理 `Some` 和 `None` 情况。

  ```rust
  fn divide(numerator: f64, denominator: f64) -> Option<f64> {
      if denominator == 0.0 {
          None
      } else {
          Some(numerator / denominator)
      }
  }

  fn main() {
      let result = divide(10.0, 2.0);
      if let Some(value) = result {
          println!("Result: {}", value);
      } else {
          println!("Division by zero");
      }
  }
  ```

### 4.3 循环和流处理

- **`while let`**：
  用于处理连续的值，如迭代器、网络流等。

  ```rust
  fn main() {
      let numbers = vec![1, 2, 3, 4, 5];
      let mut iter = numbers.iter();

      while let Some(num) = iter.next() {
          println!("Current number: {}", num);
      }
  }
  ```

### 4.4 特定业务逻辑

- **枚举匹配**：
  用于处理特定业务对象的不同状态。
  如一个订单系统：

  ```rust
  enum OrderStatus {
      Pending,
      Processing,
      Completed,
  }

  fn process_order(status: OrderStatus) {
      match status {
          OrderStatus::Pending => println!("Processing pending order"),
          OrderStatus::Processing => println!("Order is being processed"),
          OrderStatus::Completed => println!("Order has been completed"),
      }
  }

  fn main() {
      process_order(OrderStatus::Pending);
  }
  ```

### 4.5 数据解析

- **结构体匹配**：
  用于解析复杂的嵌套数据结构。
  如解析一个配置文件：

  ```rust
  #[derive(Debug)]
  struct Config {
      debug: bool,
      port: u16,
      database: String,
  }

  fn load_config(s: &str) -> Config {
      let mut debug = false;
      let mut port = 3000;
      let mut database = String::new();
      let parts = s.split_whitespace();

      for part in parts {
          match part.split_once(':') {
              Some(("debug", _)) => debug = true,
              Some(("port", p)) => port = p.parse().unwrap(),
              Some(("database", d)) => database = d.to_string(),
              _ => {}
          }
      }

      Config { debug, port, database }
  }

  fn main() {
      let config = load_config("debug: true port:8080 database:mysql");
      println!("{:?}", config);
  }
  ```

### 4.6 总结

这些模式匹配的应用在项目中可以使代码更加清晰、简洁和安全，同时也提高了代码的可维护性。

在 Rust 中，解构语法主要用于匹配和解构数据结构，例如枚举、结构体等。
然而，对于 trait object，解构语法并不能直接用于匹配，因为 trait object 的具体类型在编译时是未知的。
trait object 是一种动态类型，其具体类型信息在运行时才确定。
因此，不能直接使用解构语法来匹配 trait object。

### 4.7 解释

#### 7.7.1 Trait Object 的定义和使用

Trait object 是一种动态类型，用于表示实现了特定 trait 的任何类型。
Trait object 通常通过 `dyn` 关键字来定义，例如 `dyn Trait`。
Trait object 的主要用途是实现多态，即在编译时不知道具体类型的情况下，调用 trait 中定义的方法。

```rust
trait Draw {
    fn draw(&self) -> String;
}

impl Draw for u8 {
    fn draw(&self) -> String {
        format!("u8: {}", *self)
    }
}

impl Draw for f64 {
    fn draw(&self) -> String {
        format!("f64: {}", *self)
    }
}

fn draw1(x: Box<dyn Draw>) {
    x.draw();
}

fn draw2(x: &dyn Draw) {
    x.draw();
}

fn main() {
    let x = 1.1f64;
    let y = 8u8;

    draw1(Box::new(x));
    draw1(Box::new(y));
    draw2(&x);
    draw2(&y);
}
```

在上面的代码中，`draw1` 和 `draw2` 函数接受 `Box<dyn Draw>` 和 `&dyn Draw` 形式的 trait object。
这些函数可以在运行时调用 `draw` 方法，而不需要知道具体的类型。

#### 7.7.2 解构语法的限制

Rust 的解构语法主要用于匹配和解构数据结构，例如枚举、结构体等。
对于 trait object，由于其具体类型在编译时是未知的，解构语法不能直接用于匹配 trait object。
例如，以下代码是无效的：

```rust
match x {
    SomeType => { /* 处理 SomeType */ },
    _ => { /* 处理其他类型 */ },
}
```

在上面的代码中，`SomeType` 是一个具体的类型，而 trait object 的具体类型在编译时是未知的，因此不能直接使用解构语法来匹配 trait object。

### 4.8 解决方案

虽然不能直接使用解构语法来匹配 trait object，但可以通过其他方式来实现类似的功能。
例如，可以使用 `Any` 和 `downcast_ref` 方法来检查 trait object 的具体类型：

```rust
use std::any::Any;

trait Draw {
    fn draw(&self) -> String;
}

impl Draw for u8 {
    fn draw(&self) -> String {
        format!("u8: {}", *self)
    }
}

impl Draw for f64 {
    fn draw(&self) -> String {
        format!("f64: {}", *self)
    }
}

fn draw1(x: &dyn Draw) {
    if let Some(u8_value) = x.downcast_ref::<u8>() {
        println!("u8: {}", u8_value);
    } else if let Some(f64_value) = x.downcast_ref::<f64>() {
        println!("f64: {}", f64_value);
    } else {
        println!("Unknown type");
    }
}

fn main() {
    let x = 1.1f64;
    let y = 8u8;

    draw1(&x);
    draw1(&y);
}
```

在上面的代码中，`downcast_ref` 方法用于尝试将 trait object 转换为具体的类型。
如果转换成功，则可以使用具体的类型进行操作。

### 4.9 总结

Rust 的解构语法不能直接用于匹配 trait object，因为 trait object 的具体类型在编译时是未知的。
然而，可以通过使用 `Any` 和 `downcast_ref` 方法来检查 trait object 的具体类型，并进行相应的处理。
这种方法在需要处理多种不同类型的 trait object 时非常有用。
