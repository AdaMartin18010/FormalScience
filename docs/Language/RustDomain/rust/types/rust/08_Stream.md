# Sream

在 Rust 中，`Stream` 是异步编程的一个核心概念，它代表了一个异步的、连续的数据序列。
与同步编程中的迭代器不同，`Stream` 不是一次性返回所有数据，而是在异步运行时中逐步产生数据项。

以下是 Rust 中 `Stream` 的一些关键特性和用法：

1. **异步迭代**：`Stream` 提供了一种异步迭代数据集合的方式，每次迭代都会等待数据可用。

2. **懒加载**：`Stream` 本身是懒加载的，它不会立即产生所有元素，而是在需要时才产生下一个元素。

3. **链式调用**：`Stream` 可以与其他 `Stream` 操作组合使用，形成链式调用，对数据流进行过滤、映射、合并等操作。

4. **无阻塞**：`Stream` 的迭代通常是无阻塞的，这意味着它不会阻塞当前线程，而是在数据可用时自动继续执行。

5. **`Stream` trait**：`Stream` 是一个 trait，定义了 `poll_next` 方法，这个方法会被异步运行时调用以尝试获取流中的下一个元素。

6. **`Future` 类型**：每一个 `Stream` 实例也是一个 `Future`，它最终会完成（`Complete`）或发生错误（`Error`）。

7. **使用 `async`/`await`**：使用 `async` 关键字定义异步函数，可以 `await` 一个 `Stream`，以异步迭代其元素。

8. **流操作**：Rust 的异步库（如 `tokio` 或 `async-std`）提供了多种流操作，例如 `map`、`filter`、`fold`、`for_each` 等。

9. **错误处理**：`Stream` 可以产生错误，通常通过 `poll_next` 返回 `Poll::Ready(Err(e))` 来表示。

10. **并发流处理**：可以同时对多个 `Stream` 进行操作，利用 Rust 的并发特性来提高性能。

11. **资源管理**：`Stream` 可以用于管理需要异步访问的资源，例如文件、网络连接等。

12. **实用性**：`Stream` 在实际应用中非常有用，例如在处理文件流、网络请求、实时数据流等场景。

以下是一个简单的使用 `Stream` 的示例：

```rust
use tokio_stream::{Stream, StreamExt}; // 来自 tokio 或 async-std
use tokio::net::TcpStream;

#[tokio::main]
async fn main() {
    // 假设我们有一个 TCP 连接流
    let mut stream = TcpStream::connect("127.0.0.1:8080").await.unwrap();

    // 创建一个 Stream，用于读取数据
    let mut lines = stream.map(|result| result.unwrap())
                          .bytes() // 将结果转换为字节流
                          .map(|c| c.unwrap()) // 处理可能的错误
                          .fold(String::new(), |mut acc, byte| {
                              if byte == b'\n' {
                                  // 处理完一行后输出
                                  println!("Received: {}", acc);
                                  acc.clear();
                              } else {
                                  acc.push(byte as char);
                              }
                              acc
                          });

    // 异步迭代 Stream
    while let Some(line) = lines.next().await {
        // 处理每一行数据
    }
}
```

在这个例子中，我们创建了一个 `Stream` 来异步地从 TCP 连接中读取数据，并逐行处理它们。
通过 `StreamExt` trait，我们可以使用各种便捷的方法来操作 `Stream`。
