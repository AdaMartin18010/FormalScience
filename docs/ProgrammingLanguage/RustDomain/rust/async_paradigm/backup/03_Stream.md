# Rust Stream

在 Rust 中，`Stream` 是一种特殊的 `Future`，它用于异步地生成一系列值。
与普通的 `Future` 不同，`Stream` 可以多次被 `await`，每次都会生成一个新的值，直到流结束。

## `Stream` Trait 定义

`Stream` trait 定义在 `futures` crate 中，它是一个生成器，可以连续产生值。以下是 `Stream` trait 的基本定义：

```rust
trait Stream: Future<Output = ()> {
    type Item;
    // 尝试从 Stream 中取出下一个值，如果没有值可用，则返回 Poll::Pending。
    fn poll_next(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Option<Self::Item>>;
}
```

- `type Item`：这是一个关联类型，定义了 `Stream` 产生的值的类型。
- `fn poll_next`：这个方法尝试从 `Stream` 中取出下一个值。如果 `Stream` 已经结束，则返回 `Poll::Ready(None)`；如果还有值，但当前不能立即提供，则返回 `Poll::Pending`；如果当前有一个值可用，则返回 `Poll::Ready(Some(item))`。

### 使用 `Stream`

使用 `Stream` 通常涉及以下步骤：

1. 实现 `Stream` trait。
2. 使用 `await` 循环地从 `Stream` 中获取值。

#### 示例：实现一个简单的 `Stream`

```rust
use futures::Stream;
use std::pin::Pin;
use std::task::{Context, Poll};
use std::stream::StreamExt; // 用于简化 Stream 的使用

struct MyStream {
    items: Vec<i32>,
    index: usize,
}

impl Stream for MyStream {
    type Item = i32;

    fn poll_next(
        mut self: Pin<&mut Self>,
        _cx: &mut Context<'_>,
    ) -> Poll<Option<Self::Item>> {
        if self.index >= self.items.len() {
            Poll::Ready(None)
        } else {
            let item = self.items[self.index].take();
            self.index += 1;
            Poll::Ready(Some(item))
        }
    }
}

#[tokio::main]
async fn main() {
    let stream = MyStream {
        items: vec![1, 2, 3, 4, 5],
        index: 0,
    };

    // 使用 StreamExt 简化 Stream 的使用
    let results: Vec<i32> = stream.collect().await;
    println!("Stream 产生的值： {:?}", results);
}
```

在这个示例中：

- `MyStream` 结构体实现了 `Stream` trait。
- `poll_next` 方法返回 `Stream` 的下一个值，如果没有更多值，则返回 `None`。
- 在 `main` 函数中，我们创建了一个 `MyStream` 实例，并使用 `.collect().await` 来收集所有的值到一个 `Vec<i32>` 中。

### 解释

- `Stream` 可以被看作是一个可以多次 `await` 的 `Future`。每次 `await` `Stream` 时，它都会尝试产生一个新的值。
- `Stream` 的 `poll_next` 方法被设计为可以被多次调用，每次调用都可能产生一个新的 `Poll`。
- 使用 `StreamExt` 中的方法（如 `collect`）可以简化对 `Stream` 的处理，使得代码更加易读。

### 异步运行时

与 `Future` 一样，`Stream` 也需要在异步运行时中执行。例如，Tokio 提供了这样的运行时环境，允许 `Stream` 被有效地调度和执行。

通过 `Stream`，Rust 的异步编程模型可以处理复杂的异步数据流，使得编写高性能的异步 I/O 应用程序成为可能。

下面介绍 Rust 异步编程中 Stream 的主要用途、代码示例、背后的设计思想，并给出一些典型的反例说明常见错误的用法。

---

## 1. Stream 的主要用途

在 Rust 的 async 生态中，**Stream** 类似于同步程序里的 Iterator，但它用于按需异步产生一系列值。主要用途包括：

- **处理渐进式数据流**  
  从网络 socket、文件、数据库、消息队列等异步数据源中连续接收数据，例如：一行一行地读取日志文件，或者不断接收网络数据包。

- **事件流与消息流**  
  用于处理 GUI 事件、异步信道的消息（例如 Tokio 的 mpsc 等）或其它触发器产生的离散事件。

- **数据管道与转换**  
  将一系列异步数据按一定的规则进行转换、过滤、聚合等操作，类似于在 Iterator 上使用诸如 map、filter、fold 等组合器。

使用 Stream 可以在不阻塞执行器的情况下，利用异步算子链动态处理源源不断的数据，同时支持背压机制（back pressure），保证消费者按需消费数据。

---

## 2. 典型的代码示例

以下示例使用 `futures` 和 `tokio` 提供的 stream 工具，展示如何创建并消费一个异步 stream。

### 2.1 示例：通过 `futures::stream::iter` 模拟数据流

**文件路径：** `src/async_stream_example.rs`

```rust:src/async_stream_example.rs
use futures::stream::{self, StreamExt};
use tokio::time::{sleep, Duration};

#[tokio::main]
async fn main() {
    // 模拟一个数据流，产生 1 到 5 的数字，每个数字产生前延时 200 毫秒
    let my_stream = stream::iter(1..=5).then(|num| async move {
        // 模拟异步 IO 操作
        sleep(Duration::from_millis(200)).await;
        num
    });

    // 消费 stream 的过程中，数据将按顺序异步产生
    tokio::pin!(my_stream);
    while let Some(value) = my_stream.next().await {
        println!("Received value: {}", value);
    }
}
```

### 2.2 示例：使用 `async_stream` 宏构建 Stream

使用 [async-stream](https://crates.io/crates/async-stream) crate 可更方便地书写异步 stream。

**文件路径：** `src/async_stream_macro_example.rs`

```rust:src/async_stream_macro_example.rs
use async_stream::stream;
use tokio::time::{sleep, Duration};
use futures::StreamExt;

#[tokio::main]
async fn main() {
    // 使用 stream! 宏将异步逻辑写得更自然
    let my_stream = stream! {
        for i in 0..5 {
            // 模拟每个数据项产生前的等待
            sleep(Duration::from_millis(150)).await;
            yield i;
        }
    };

    tokio::pin!(my_stream);
    while let Some(item) = my_stream.next().await {
        println!("Yielded: {}", item);
    }
}
```

在以上两个示例中，stream 用于异步产生数据，消费端通过 `.next().await` 按顺序取得每个值，并可与其它异步操作并发协作。

---

## 3. 分析

- **异步数据处理**  
  Stream 允许在异步环境中按需拉取数据，而不是一次性全部加载。这样既节省内存，又能应对数据源延迟或不确定性。

- **事件链与转换**  
  类似迭代器，Stream 提供诸如 `map`, `filter`, `fold` 等组合器函数，通过函数链可以方便地对数据流进行转换和归纳计算。

- **背压机制**  
  当生产者不断产生数据时，消费者可以根据实际处理速度控制流量，避免过多未消费的数据堆积，从而更好地利用异步任务调度器。

- **与异步运行时的配合**  
  与 Tokio 或 async-std 等运行时结合，stream 允许在等待 IO 的同时调度其他任务，当数据就绪时通过 `.next().await` 得到对应的值。

---

## 4. 常见的“反例”及误区

下面给出两个常见反例说明不正确的用法，帮助避免常见问题。

### 4.1 反例 1：在异步 Stream 内运行密集计算导致阻塞

**问题描述：**  
如果在 stream 的生成过程中进行长时间密集计算而不进行异步等待操作，会阻塞当前任务，影响整个异步运行时。例如：

```rust:src/stream_blocking_example.rs
use futures::stream::{self, StreamExt};

fn heavy_computation(x: u32) -> u32 {
    // 模拟密集计算（无任何 await）
    let mut sum = 0;
    for i in 0..1_000_000 {
        sum = sum.wrapping_add(i);
    }
    x + sum
}

#[tokio::main]
async fn main() {
    // 这里直接迭代并在同步代码中调用 heavy_computation
    // 将导致任务在异步执行器中长时间占用 CPU，阻塞其它任务。
    let my_stream = stream::iter(1..=5).map(|num| heavy_computation(num));
    tokio::pin!(my_stream);
    while let Some(result) = my_stream.next().await {
        println!("Result: {}", result);
    }
}
```

**问题分析：**  
上例中，`heavy_computation` 是一个同步耗时任务，直接在 stream 中调用后没有任何 `.await` 或者异步调度，被阻塞的部分会延迟其它异步任务的执行，失去了异步编程的优势。此时应考虑放到 [`tokio::task::spawn_blocking`] 中或引入适当的 yield 操作。

---

### 4.2 反例 2：错误使用同步 Iterator 替代 Stream

**问题描述：**  
在异步场景下，错误地使用同步 Iterator 进行数据处理会使得程序不能正确利用异步特性。例如：

```rust:src/sync_iterator_wrong.rs
fn sync_iter() -> impl Iterator<Item = u32> {
    // 直接产生一个同步迭代器（非异步数据流）
    (1..=5).into_iter()
}

#[tokio::main]
async fn main() {
    // 错误：这里使用同步 Iterator，并试图在异步函数中等待
    // 这无法正确切换任务，也不会在异步上下文中贡献背压特性。
    for value in sync_iter() {
        // 如果企图调用 async 操作必须调用 .await，但这里没有 await 点
        println!("Sync value: {}", value);
    }
    // 正确做法是使用 Stream 来生成并异步消费数据
}
```

**问题分析：**  
上例中使用的 Iterator 无法插入异步等待点，既不释放异步任务执行权，也不支持异步组合器。如果数据源本身是异步（例如网络 I/O），应使用 Stream 来建模，确保异步任务能够按需调度和等待。

---

## 5. 思维导图总结

下面提供一个 Mermaid 思维导图，概括了 Rust async 中 Stream 的主要用途、正确用法以及常见错误场景：

```mermaid:diagram/rust_async_stream.mmd
flowchart TD
    A[Async Stream]
    A --> B[主要用途]
    B --> B1[渐进式数据处理]
    B --> B2[事件/消息流]
    B --> B3[数据管道转换]
    
    A --> C[正确使用]
    C --> C1[按需产生数据]
    C --> C2[插入异步等待，避免阻塞]
    C --> C3[使用组合器(map/filter/fold)]
    
    A --> D[代码示例]
    D --> D1[使用 futures::stream::iter & then]
    D --> D2[使用 async_stream::stream 宏]
    
    A --> E[常见反例]
    E --> E1[在 Stream 内进行阻塞式密集计算]
    E --> E2[错误使用同步 Iterator 替代 Stream]
```

---

## 6. 总结

- **主要用途：**  
  Stream 在异步通信中用于按需异步产生一系列数据，适用于网络、文件 I/O、事件处理等场景。

- **正确用法：**  
  利用异步等待（例如 sleep、I/O 等）来产生数据，使用组合器函数对数据流进行转换，并通过 `.next().await` 按顺序消费数据。

- **反例警示：**  
  避免在 stream 中进行耗时的同步计算；不要将普通的 Iterator 当作异步流使用，否则将失去异步编程的好处。

通过正确理解和使用 async Stream，可以充分发挥异步编程的优势，从而构建高效、响应及时的数据处理系统。
