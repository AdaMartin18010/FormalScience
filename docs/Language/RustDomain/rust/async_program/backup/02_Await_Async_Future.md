# Await、Async 和 Future

在 Rust 中，`async`、`await` 和 `Future` 是异步编程的核心概念，它们共同构成了 Rust 的异步编程模型。
以下是它们的定义和联系：

1. **Future**：
   - `Future` 是 Rust 中的一个核心异步概念，代表了一个可能还没有完成的计算，它将在未来的某个时刻完成，并返回一个结果或者一个错误。
   `Future` 是一个实现了 `Future` trait 的类型，这个 trait 定义了一个 `poll` 方法，该方法会被异步运行时调用以推动异步任务的执行。

2. **async**：
   - `async` 是一个关键字，用于定义一个异步函数。与普通函数不同，异步函数会返回一个实现了 `Future` trait 的值，而不是直接返回一个结果。
   这意味着 `async` 函数的执行不会阻塞当前线程，它允许其他任务在等待当前任务完成时继续执行。

3. **await**：
   - `await` 是一个关键字，用于等待一个 `Future` 完成。在异步函数中，可以使用 `await` 来暂停当前函数的执行，直到被等待的 `Future` 完成。
   `await` 表达式只能在异步函数或异步块中使用。

## 联系

- `async` 函数定义了一个异步的执行路径，它返回的是一个 `Future`。
- `await` 用于在异步函数中等待 `Future` 的结果，它允许 Rust 的异步运行时在 `Future` 等待 I/O 操作或其他异步任务完成时，切换到其他任务。
- `Future` 是异步操作的表示，它可以被 `await` 表达式等待，也可以在异步运行时中被轮询（通过 `poll` 方法）。

## 异步任务的执行流程

1. 开发者使用 `async` 关键字定义一个异步函数，该函数执行体中可能包含多个 `await` 表达式。
2. 当调用这个异步函数时，它不会立即执行，而是立即返回一个 `Future` 对象。
3. 这个 `Future` 对象随后被一个异步运行时（如 `tokio` 或 `async-std`）所管理。
4. 异步运行时负责调度 `Future` 的执行，它会周期性地调用 `Future` 的 `poll` 方法来尝试推进 `Future` 的完成。
5. 当 `Future` 遇到需要等待的操作（如 I/O）时，它会返回 `Pending` 状态，告诉运行时当前任务尚未完成。
6. 运行时会将 `Future` 挂起，并继续执行其他 `Future`。
7. 当导致挂起的事件（如 I/O 操作完成）发生时，运行时会再次调用该 `Future` 的 `poll` 方法。
8. 如果 `Future` 完成，它会返回 `Ready` 状态，并提供最终结果或错误。

通过 `async`、`await` 和 `Future` 的协同工作，Rust 的异步编程模型允许开发者以接近同步代码的方式编写异步逻辑，同时保持了高效的非阻塞性能。

在 Rust 中，`Future` 是一个实现了 `std::future::Future` trait 的类型。
这个 trait 定义了一个核心方法 `poll`，它被异步运行时（如 `tokio` 或 `async-std`）用来推动 `Future` 的执行。
以下是 `Future` 的基本实现细节：

### 定义 `Future` Trait

`Future` trait 通常定义如下：

```rust
use std::pin::Pin;
use std::task::{Context, Poll};

pub trait Future {
    type Output;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
}
```

- `Output`：是一个与 `Future` 关联的类型，表示 `Future` 完成时产生的结果。
- `poll` 方法：尝试推动 `Future` 向前执行。这个方法会返回一个 `Poll` 类型，它可以是 `Poll::Ready(output)` 或 `Poll::Pending`。

### `Poll` 类型

- `Poll::Ready(T)`：表示 `Future` 已经完成，并返回了结果 `T`。
- `Poll::Pending`：表示 `Future` 尚未完成，需要在未来再次被轮询。

### `Context` 类型

- `Context` 是一个包含 `Waker` 的结构体，`Waker` 是一个当 `Future` 可以再次被轮询时，能够唤醒当前任务的句柄。

### 实现 `Future`

要实现一个 `Future`，你需要定义一个结构体和一个 `poll` 方法。以下是一个简单的示例：

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

struct MyFuture {
    // 这里可以添加状态，例如计数器或 I/O 任务
    state: i32,
}

impl Future for MyFuture {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        if self.state < 5 {
            self.state += 1;
            Poll::Pending
        } else {
            Poll::Ready(())
        }
    }
}
```

在这个例子中，`MyFuture` 结构体包含一个简单的计数器 `state`。
`poll` 方法检查计数器是否达到 5，如果没有，它返回 `Poll::Pending` 并增加计数器。一旦计数器达到 5，它返回 `Poll::Ready(())` 表示 `Future` 完成。

### 使用 `Future`

要使用 `Future`，通常你需要将其传递给异步运行时，例如使用 `tokio::spawn`：

```rust
#[tokio::main]
async fn main() {
    let future = MyFuture { state: 0 };
    let result = future.await;
    // 使用 result
}
```

在这个例子中，`MyFuture` 实例被 `await`，这会导致当前异步任务在 `MyFuture` 完成之前挂起。当 `MyFuture` 完成时，`await` 表达式的执行会继续。

### 注意事项

- `Future` 必须能够被 `Pin`，因为 `poll` 方法接受 `Pin<&mut Self>` 作为参数。这意味着 `Future` 可能需要分配在堆上以允许安全地移动内部指针。
- `poll` 方法的实现应该小心处理 `Waker`，确保在 `Future` 可以继续执行时能够正确唤醒任务。

通过这种方式，Rust 的 `Future` 允许开发者编写非阻塞的异步代码，同时保持了 Rust 的安全性和性能。

在 Rust 中，`Pin` trait 是 `std::pin::Pin` 的别名，它用于保证一个值在内存中的位置（地址）在其生命周期内保持不变。
这对于保证某些数据结构的内存布局和行为至关重要，特别是在异步编程和手动内存管理中。

### `Pin` Trait 的定义

`Pin` trait 定义了一种新的指针，称为“pin pointer”，它不允许移动它所指向的值。
`Pin` trait 包含如下方法：

```rust
pub trait Pin<T> {
    fn new(value: T) -> Self;
    fn as_ref(self: Pin<&T>) -> &T;
    fn as_mut(self: Pin<&mut T>) -> &mut T;
    unsafe fn get_unchecked(self: Pin<&Self>) -> *const T;
    unsafe fn get_unchecked_mut(self: Pin<&mut Self>) -> *mut T;
}
```

- `new`：创建一个新的 `Pin<T>` 包装器，它包含了类型 `T` 的值。
- `as_ref` 和 `as_mut`：允许访问 `Pin` 内部的值的不可变或可变引用。
- `get_unchecked`：提供了一种方式来获取内部值的原始指针，这需要开发者确保使用时的安全性。

### 使用 `Pin`

`Pin` 通常与实现了 `!Unpin` 的类型一起使用，`!Unpin` 是 `Pin` trait 的负特征（negative trait bound），表示一个类型不能被 `Pin` 固定在某个位置。
如果一个类型没有实现 `!Unpin`，那么它就可以被 `Pin`。

以下是 `Pin` 的一个使用示例：

```rust
use std::pin::Pin;
use std::marker::PhantomPinned;

struct MyStruct {
    data: String,
    // 使用 PhantomPinned 来表明这个结构体可以被 Pinning
    _pinned: PhantomPinned,
}

impl MyStruct {
    fn new(data: String) -> Self {
        MyStruct { data, _pinned: PhantomPinned }
    }
}

fn main() {
    let mut my_struct = MyStruct::new("Hello, world!".to_string());
    let mut my_struct_pin = Pin::new(&mut my_struct);

    // 使用 as_mut 来获取可变引用
    let my_string_pin = my_struct_pin.as_mut().data.as_mut_str();
    
    // 现在 my_string_pin 不能被移动，它的地址是固定的
}
```

在这个例子中，`MyStruct` 结构体包含了一个 `String` 和一个 `PhantomPinned` 类型，后者是一个空的标记类型，用来指示这个结构体可以被 `Pin`。
然后我们使用 `Pin::new` 来创建一个 `Pin` 包装器，并通过 `as_mut` 来获取内部数据的可变引用。

### 解释和用途

`Pin` trait 的主要用途是确保在 Rust 的生命周期内，某些值的地址不会被改变。这对于以下情况非常重要：

- **异步编程**：在异步任务中，`Future` 可能需要在不同的状态之间切换，如果 `Future` 被 `Pin`，则可以保证其状态在内存中的位置不变，这对于状态机的实现非常有用。
- **手动内存管理**：在某些低级编程中，可能需要手动管理内存，`Pin` 可以用来保证某些资源（如分配在堆上的数组）的地址固定。

使用 `Pin` 时，开发者需要保证不对 `Pin` 内部的值进行移动操作，因为这可能会导致未定义行为。`Pin` 通过提供 `as_ref` 和 `as_mut` 方法来安全地访问内部值，而不破坏其固定的状态。
同时，`get_unchecked` 方法允许开发者在确保安全的情况下，获取内部值的原始指针。
