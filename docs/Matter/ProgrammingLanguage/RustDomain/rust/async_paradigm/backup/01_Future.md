# rust Future

在 Rust 中，`Future` 是一个核心的异步编程概念。
它代表了一个可能尚未完成的异步操作，但最终会返回一个结果。
`Future` trait 定义了 `Future` 类型必须实现的方法，使得它们可以被异步运行时管理和调度。

## `Future` Trait 定义

`Future` trait 定义在 Rust 的标准库中，主要包含以下内容：

- **关联类型 `Output`**：表示 `Future` 完成时返回的结果类型。
- **方法 `poll`**：这是一个异步方法，由异步运行时调用，用以检查 `Future` 是否已经完成。

以下是 `Future` trait 的定义：

```rust
trait Future {
    type Output;
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
}
```

- **`type Output`**：这是一个关联类型，定义了 `Future` 完成时返回的结果类型。
- **`fn poll`**：这个方法是异步运行时调用的，用来检查 `Future` 是否已经完成。它接受一个 `Context` 对象和一个 `Pin` 包装的 `self` 引用。

### `Context` 和 `Poll`

- **`Context`**：这是一个由异步运行时提供的上下文对象，用于传递 `Waker`。`Waker` 是一个用于唤醒当前任务的句柄。
- **`Poll`**：这是一个枚举类型，表示 `Future` 的当前状态：
  - `Poll::Ready(T)`：表示 `Future` 已经完成，返回结果 `T`。
  - `Poll::Pending`：表示 `Future` 尚未完成，需要继续等待。

### 使用 `Future`

要使用 `Future`，你需要：

1. 实现 `Future` trait。
2. 使用 `.await` 来等待 `Future` 完成。

#### 示例：实现一个简单的 `Future`

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

struct MyFuture {
    value: i32,
}

impl Future for MyFuture {
    type Output = i32;

    fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        Poll::Ready(self.value)
    }
}

fn main() {
    let future = MyFuture { value: 42 };
    let result = future.await;
    println!("Future 的结果是：{}", result);
}
```

在这个示例中：

- `MyFuture` 结构体实现了 `Future` trait。
- `poll` 方法返回 `Poll::Ready(self.value)`，表示 `Future` 立即完成并返回值 `42`。
- 在 `main` 函数中，使用 `.await` 等待 `MyFuture` 完成，并打印结果。

### 解释

- **`Pin`**：`Pin` 是一个包装器，用于确保 `Future` 在其生命周期内不会被移动。这是必要的，因为异步运行时可能会多次调用 `poll` 方法，而 `Future` 需要保持在同一个内存位置。
- **`Waker`**：`Waker` 是 `Context` 中的一个字段，用于通知异步运行时当前任务需要被唤醒。当 `Future` 需要继续执行时，它会通过 `Waker` 来通知运行时。

通过这种方式，Rust 的异步编程模型能够高效地管理异步任务的执行，确保资源的合理利用和程序的响应性。
