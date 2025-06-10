# Rust 中的 async 和 await

在 Rust 中，`async` 和 `await` 是用于编写异步代码的关键字，它们使得异步代码的编写更加直观和简洁。以下是这些关键字的使用和解释：

## `async`

- `async` 关键字用于定义一个异步函数（也称为异步块）。异步函数返回一个实现了 `Future` trait 的类型。
- 异步函数可以包含 `.await` 表达式，用于等待其他异步操作完成。

## `await`

- `await` 关键字用于等待一个 `Future` 或 `Stream` 完成。
- 当一个 `await` 表达式被执行时，它会暂停当前的异步函数的执行，直到被等待的 `Future` 或 `Stream` 完成。
- `await` 只能在异步函数中使用。

## 使用示例

以下是一个简单的示例，展示了如何使用 `async` 和 `await`：

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
use std::time::Duration;
use tokio::time::sleep;

struct MyFuture {
    value: i32,
}

impl Future for MyFuture {
    type Output = i32;

    fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        Poll::Ready(self.value)
    }
}

async fn async_function() {
    let future = MyFuture { value: 42 };
    let result = await!(future);
    println!("Future 的结果是：{}", result);
}

#[tokio::main]
async fn main() {
    async_function().await;
}
```

在这个示例中：

1. `MyFuture` 结构体实现了 `Future` trait。
2. `async_function` 是一个异步函数，它使用 `await` 等待 `MyFuture` 完成。
3. `main` 函数是一个标记为 `#[tokio::main]` 的异步入口点，它调用 `async_function` 并等待其完成。

### 解释

- **`async` 函数**：使用 `async` 关键字定义的函数会返回一个实现了 `Future` trait 的类型。这意味着这些函数可以被 `await`。
- **`await` 表达式**：`await` 关键字用于等待一个 `Future` 或 `Stream` 完成。它只能在异步函数中使用。
- **异步运行时**：Rust 的异步代码需要在一个异步运行时（如 Tokio）中执行。`#[tokio::main]` 宏用于设置一个异步运行时，并作为程序的入口点。

### 异步运行时的作用

异步运行时负责：

- 调度和管理异步任务。
- 处理事件循环和任务的唤醒。
- 提供异步 I/O、定时器等基础设施。

### 错误处理

在异步代码中，错误处理通常使用 `Result` 类型和 `?` 操作符。例如：

```rust
async fn fetch_data() -> Result<String, Box<dyn std::error::Error>> {
    let client = reqwest::Client::new();
    let response = client.get("https://www.example.com").send().await?;
    let html = response.text().await?;
    Ok(html)
}

#[tokio::main]
async fn main() {
    match fetch_data().await {
        Ok(html) => println!("网页内容：{}", html),
        Err(e) => println!("发生错误：{}", e),
    }
}
```

在这个示例中：

- `fetch_data` 是一个异步函数，它使用 `reqwest` 库发送 HTTP 请求并获取响应。
- 使用 `?` 操作符处理可能的错误，并将错误传递给调用者。

通过这种方式，Rust 的 `async` 和 `await` 关键字使得异步代码的编写更加直观和易于理解。
