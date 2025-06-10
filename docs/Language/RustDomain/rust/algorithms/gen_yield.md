# Rust中使用生成器(Generator)和yield实现基本算法

Rust目前没有直接的`yield`关键字，
但我们可以使用`async/await`和第三方库如`genawaiter`来模拟生成器行为。
下面我将展示如何在同步和异步模式下实现一些基本算法，并使用泛型容器。

## 目录

- [Rust中使用生成器(Generator)和yield实现基本算法](#rust中使用生成器generator和yield实现基本算法)
  - [目录](#目录)
  - [同步模式下的生成器实现](#同步模式下的生成器实现)
    - [斐波那契数列生成器](#斐波那契数列生成器)
    - [使用泛型容器的素数筛选](#使用泛型容器的素数筛选)
  - [异步模式下的生成器实现](#异步模式下的生成器实现)
    - [异步斐波那契数列生成器](#异步斐波那契数列生成器)
    - [使用泛型异步队列的生产者-消费者模式](#使用泛型异步队列的生产者-消费者模式)
    - [使用泛型实现异步迭代器适配器](#使用泛型实现异步迭代器适配器)
  - [总结](#总结)

## 同步模式下的生成器实现

首先需要添加依赖：

```toml:Cargo.toml
[dependencies]
genawaiter = "0.99"
```

### 斐波那契数列生成器

```rust
use genawaiter::{sync::gen, yield_};

// 同步斐波那契数列生成器
fn fibonacci(limit: usize) -> impl Iterator<Item = u64> {
    gen!({
        let mut a = 0;
        let mut b = 1;
        
        for _ in 0..limit {
            yield_!(a);
            let next = a + b;
            a = b;
            b = next;
        }
    })
    .into_iter()
}

fn main() {
    // 使用生成器
    println!("斐波那契数列:");
    for num in fibonacci(10) {
        println!("{}", num);
    }
}
```

### 使用泛型容器的素数筛选

```rust
use genawaiter::{sync::gen, yield_};
use std::collections::HashSet;

// 使用泛型容器的素数生成器
fn primes<T>(limit: usize) -> impl Iterator<Item = usize>
where
    T: FromIterator<usize> + Extend<usize> + IntoIterator<Item = usize>,
{
    gen!({
        if limit >= 2 {
            yield_!(2);
        }
        
        let mut sieve: T = (2..=2).collect();
        
        for n in 3..=limit {
            if n % 2 == 0 {
                continue;
            }
            
            let is_prime = !sieve.into_iter().any(|p| n % p == 0);
            
            if is_prime {
                sieve = sieve.into_iter().collect::<T>();
                sieve.extend(std::iter::once(n));
                yield_!(n);
            }
        }
    })
    .into_iter()
}

fn main() {
    // 使用HashSet作为容器
    println!("素数列表 (使用HashSet):");
    for prime in primes::<HashSet<usize>>(50) {
        print!("{} ", prime);
    }
    println!();
    
    // 使用Vec作为容器
    println!("素数列表 (使用Vec):");
    for prime in primes::<Vec<usize>>(50) {
        print!("{} ", prime);
    }
    println!();
}
```

## 异步模式下的生成器实现

### 异步斐波那契数列生成器

```rust
use genawaiter::{rc::gen, yield_};
use futures::StreamExt;

// 异步斐波那契数列生成器
async fn async_fibonacci(limit: usize) {
    let stream = gen!({
        let mut a = 0;
        let mut b = 1;
        
        for _ in 0..limit {
            yield_!(a);
            let next = a + b;
            a = b;
            b = next;
        }
    });
    
    // 使用异步流处理
    let mut stream = Box::pin(stream);
    while let Some(num) = stream.next().await {
        println!("异步斐波那契: {}", num);
        // 这里可以添加异步操作，如延迟
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    }
}

// 需要在异步运行时中执行
#[tokio::main]
async fn main() {
    async_fibonacci(10).await;
}
```

### 使用泛型异步队列的生产者-消费者模式

```rust
use std::collections::VecDeque;
use std::sync::Arc;
use tokio::sync::Mutex;

// 泛型异步队列
struct AsyncQueue<T> {
    data: Arc<Mutex<VecDeque<T>>>,
}

impl<T: Clone> AsyncQueue<T> {
    fn new() -> Self {
        AsyncQueue {
            data: Arc::new(Mutex::new(VecDeque::new())),
        }
    }
    
    async fn enqueue(&self, item: T) {
        let mut queue = self.data.lock().await;
        queue.push_back(item);
    }
    
    async fn dequeue(&self) -> Option<T> {
        let mut queue = self.data.lock().await;
        queue.pop_front()
    }
    
    async fn is_empty(&self) -> bool {
        let queue = self.data.lock().await;
        queue.is_empty()
    }
}

// 生产者函数
async fn producer<T: Clone + From<u32>>(queue: Arc<AsyncQueue<T>>, count: u32) {
    for i in 0..count {
        let item = T::from(i);
        queue.enqueue(item).await;
        println!("生产: {}", i);
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    }
}

// 消费者函数
async fn consumer<T: Clone + std::fmt::Display>(queue: Arc<AsyncQueue<T>>) {
    loop {
        if let Some(item) = queue.dequeue().await {
            println!("消费: {}", item);
        } else if queue.is_empty().await {
            tokio::time::sleep(tokio::time::Duration::from_millis(500)).await;
            if queue.is_empty().await {
                break;
            }
        }
        tokio::time::sleep(tokio::time::Duration::from_millis(200)).await;
    }
}

#[tokio::main]
async fn main() {
    // 创建一个i32类型的队列
    let queue: Arc<AsyncQueue<i32>> = Arc::new(AsyncQueue::new());
    
    // 启动生产者和消费者任务
    let producer_task = tokio::spawn(producer(Arc::clone(&queue), 10));
    let consumer_task = tokio::spawn(consumer(Arc::clone(&queue)));
    
    // 等待任务完成
    let _ = tokio::join!(producer_task, consumer_task);
}
```

### 使用泛型实现异步迭代器适配器

```rust
use std::marker::PhantomData;
use futures::{Stream, StreamExt};
use std::pin::Pin;
use std::task::{Context, Poll};
use futures::stream::BoxStream;

// 泛型异步映射适配器
struct AsyncMap<S, F, T, U> {
    stream: S,
    f: F,
    _phantom: PhantomData<(T, U)>,
}

impl<S, F, T, U> AsyncMap<S, F, T, U>
where
    S: Stream<Item = T> + Unpin,
    F: FnMut(T) -> U + Unpin,
{
    fn new(stream: S, f: F) -> Self {
        AsyncMap {
            stream,
            f,
            _phantom: PhantomData,
        }
    }
}

impl<S, F, T, U> Stream for AsyncMap<S, F, T, U>
where
    S: Stream<Item = T> + Unpin,
    F: FnMut(T) -> U + Unpin,
{
    type Item = U;

    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        match Pin::new(&mut self.stream).poll_next(cx) {
            Poll::Ready(Some(item)) => {
                let mapped = (self.f)(item);
                Poll::Ready(Some(mapped))
            }
            Poll::Ready(None) => Poll::Ready(None),
            Poll::Pending => Poll::Pending,
        }
    }
}

// 扩展Stream特征
trait AsyncStreamExt: Stream {
    fn async_map<F, U>(self, f: F) -> AsyncMap<Self, F, Self::Item, U>
    where
        Self: Sized + Unpin,
        F: FnMut(Self::Item) -> U + Unpin,
    {
        AsyncMap::new(self, f)
    }
}

// 为所有Stream实现扩展特征
impl<T: Stream> AsyncStreamExt for T {}

// 创建一个简单的异步数字流
fn number_stream(limit: u32) -> BoxStream<'static, u32> {
    let stream = futures::stream::iter((0..limit).collect::<Vec<_>>());
    Box::pin(stream)
}

#[tokio::main]
async fn main() {
    // 使用我们的异步映射适配器
    let mut stream = number_stream(10)
        .async_map(|x| x * x)
        .async_map(|x| format!("平方值: {}", x));
    
    while let Some(item) = stream.next().await {
        println!("{}", item);
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    }
}
```

## 总结

以上示例展示了如何在Rust中：

1. 使用`genawaiter`库模拟生成器和`yield`功能
2. 在同步和异步模式下实现基本算法
3. 使用泛型容器来增强代码的灵活性和复用性
4. 实现自定义的异步流处理工具

这些模式可以应用于各种场景，如数据处理、流式计算、异步任务调度等。虽然Rust没有内置的生成器语法，但通过这些技术可以实现类似的功能。

注意：要运行异步示例，需要添加`tokio`和`futures`依赖：

```toml
[dependencies]
genawaiter = "0.99"
tokio = { version = "1", features = ["full"] }
futures = "0.3"
```
