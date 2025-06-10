# 使用 Rust 2024 版本中的 `gen` 与 Tokio 结合使用

下面详细介绍 Rust 2024 版本中 `gen` 与 Tokio 的结合使用方法。
我们将通过多个场景和示例来展示其功能和用法。

## 目录

- [使用 Rust 2024 版本中的 `gen` 与 Tokio 结合使用](#使用-rust-2024-版本中的-gen-与-tokio-结合使用)
  - [目录](#目录)
  - [1. 基础配置](#1-基础配置)
  - [2. 基本的 Generator 实现](#2-基本的-generator-实现)
  - [3. 结合 Tokio 的异步 Generator](#3-结合-tokio-的异步-generator)
  - [4. 异步流生成器](#4-异步流生成器)
  - [5. 带状态的异步生成器](#5-带状态的异步生成器)
  - [6. 错误处理与生成器](#6-错误处理与生成器)
  - [7. 并发生成器](#7-并发生成器)
  - [8. 资源管理生成器](#8-资源管理生成器)
  - [9. 带超时的生成器](#9-带超时的生成器)
  - [10. 可取消的生成器](#10-可取消的生成器)
  - [11. 组合多个生成器](#11-组合多个生成器)

## 1. 基础配置

首先在 `Cargo.toml` 中添加必要的依赖：

```toml
[dependencies]
tokio = { version = "1.0", features = ["full"] }
futures = "0.3"
async-stream = "0.3"
pin-project = "1.0"
```

## 2. 基本的 Generator 实现

```rust
#![feature(gen_blocks)]

use std::ops::{Generator, GeneratorState};
use std::pin::Pin;

fn main() {
    let mut gen = || {
        yield 1;
        yield 2;
        yield 3;
        "done"
    };

    loop {
        match Pin::new(&mut gen).resume(()) {
            GeneratorState::Yielded(value) => println!("Yielded: {}", value),
            GeneratorState::Complete(value) => {
                println!("Completed: {}", value);
                break;
            }
        }
    }
}
```

## 3. 结合 Tokio 的异步 Generator

```rust
use tokio::time::{sleep, Duration};
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

struct AsyncGenerator<G> {
    gen: G,
}

impl<G> AsyncGenerator<G>
where
    G: Generator<Yield = ()>,
{
    fn new(gen: G) -> Self {
        Self { gen }
    }
}

impl<G> Future for AsyncGenerator<G>
where
    G: Generator<Yield = ()> + Unpin,
{
    type Output = G::Return;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        match Pin::new(&mut self.gen).resume(()) {
            GeneratorState::Yielded(()) => Poll::Pending,
            GeneratorState::Complete(value) => Poll::Ready(value),
        }
    }
}

#[tokio::main]
async fn main() {
    let gen = AsyncGenerator::new(|| {
        yield ();
        sleep(Duration::from_secs(1)).await;
        yield ();
        "done"
    });

    let result = gen.await;
    println!("Result: {}", result);
}
```

## 4. 异步流生成器

```rust
use async_stream::stream;
use futures::Stream;
use std::pin::Pin;
use tokio::time::{sleep, Duration};

fn generate_numbers() -> impl Stream<Item = i32> {
    stream! {
        for i in 0..5 {
            sleep(Duration::from_millis(100)).await;
            yield i;
        }
    }
}

#[tokio::main]
async fn main() {
    let mut numbers = Box::pin(generate_numbers());
    while let Some(number) = numbers.next().await {
        println!("Generated: {}", number);
    }
}
```

## 5. 带状态的异步生成器

```rust
struct StateGenerator {
    state: i32,
}

impl StateGenerator {
    fn new() -> Self {
        Self { state: 0 }
    }

    fn generate(&mut self) -> impl Stream<Item = i32> + '_ {
        stream! {
            while self.state < 5 {
                yield self.state;
                self.state += 1;
                sleep(Duration::from_millis(100)).await;
            }
        }
    }
}

#[tokio::main]
async fn main() {
    let mut gen = StateGenerator::new();
    let mut stream = Box::pin(gen.generate());
    
    while let Some(value) = stream.next().await {
        println!("State: {}", value);
    }
}
```

## 6. 错误处理与生成器

```rust
use std::error::Error;

type Result<T> = std::result::Result<T, Box<dyn Error>>;

fn generate_with_error() -> impl Stream<Item = Result<i32>> {
    stream! {
        for i in 0..5 {
            if i == 3 {
                yield Err("Error at 3".into());
            } else {
                yield Ok(i);
            }
            sleep(Duration::from_millis(100)).await;
        }
    }
}

#[tokio::main]
async fn main() {
    let mut stream = Box::pin(generate_with_error());
    
    while let Some(result) = stream.next().await {
        match result {
            Ok(value) => println!("Value: {}", value),
            Err(e) => println!("Error: {}", e),
        }
    }
}
```

## 7. 并发生成器

```rust
use tokio::sync::mpsc;
use futures::StreamExt;

async fn concurrent_generator() {
    let (tx, mut rx) = mpsc::channel(10);
    
    // 生成器任务
    let generator = tokio::spawn(async move {
        let stream = stream! {
            for i in 0..5 {
                sleep(Duration::from_millis(100)).await;
                yield i;
            }
        };
        
        let mut stream = Box::pin(stream);
        while let Some(value) = stream.next().await {
            tx.send(value).await.unwrap();
        }
    });
    
    // 消费者任务
    while let Some(value) = rx.recv().await {
        println!("Received: {}", value);
    }
    
    generator.await.unwrap();
}

#[tokio::main]
async fn main() {
    concurrent_generator().await;
}
```

## 8. 资源管理生成器

```rust
struct Resource {
    id: i32,
}

impl Resource {
    async fn new(id: i32) -> Self {
        sleep(Duration::from_millis(100)).await;
        Self { id }
    }
    
    async fn cleanup(&self) {
        sleep(Duration::from_millis(100)).await;
        println!("Cleaning up resource {}", self.id);
    }
}

fn resource_generator() -> impl Stream<Item = Resource> {
    stream! {
        for i in 0..3 {
            let resource = Resource::new(i).await;
            yield resource;
        }
    }
}

#[tokio::main]
async fn main() {
    let mut resources = Box::pin(resource_generator());
    
    while let Some(resource) = resources.next().await {
        println!("Using resource {}", resource.id);
        resource.cleanup().await;
    }
}
```

## 9. 带超时的生成器

```rust
use tokio::time::timeout;

async fn generator_with_timeout() {
    let stream = stream! {
        for i in 0..5 {
            sleep(Duration::from_secs(1)).await;
            yield i;
        }
    };
    
    let mut stream = Box::pin(stream);
    while let Some(value) = stream.next().await {
        match timeout(Duration::from_millis(500), async move { value }).await {
            Ok(v) => println!("Value: {}", v),
            Err(_) => println!("Timeout"),
        }
    }
}

#[tokio::main]
async fn main() {
    generator_with_timeout().await;
}
```

## 10. 可取消的生成器

```rust
use tokio::select;
use tokio::sync::oneshot;

async fn cancellable_generator() {
    let (tx, rx) = oneshot::channel();
    
    let generator = tokio::spawn(async move {
        let stream = stream! {
            for i in 0..10 {
                sleep(Duration::from_millis(100)).await;
                yield i;
            }
        };
        
        let mut stream = Box::pin(stream);
        while let Some(value) = stream.next().await {
            println!("Generated: {}", value);
        }
    });
    
    // 3秒后取消生成器
    sleep(Duration::from_secs(3)).await;
    tx.send(()).unwrap();
    
    generator.await.unwrap();
}

#[tokio::main]
async fn main() {
    cancellable_generator().await;
}
```

## 11. 组合多个生成器

```rust
use futures::stream::select;

fn combined_generators() -> impl Stream<Item = i32> {
    let gen1 = stream! {
        for i in 0..3 {
            sleep(Duration::from_millis(100)).await;
            yield i;
        }
    };
    
    let gen2 = stream! {
        for i in 3..6 {
            sleep(Duration::from_millis(150)).await;
            yield i;
        }
    };
    
    select(gen1, gen2)
}

#[tokio::main]
async fn main() {
    let mut combined = Box::pin(combined_generators());
    while let Some(value) = combined.next().await {
        println!("Combined value: {}", value);
    }
}
```

这些示例展示了如何在 Rust 2024 版本中使用 `gen` 与 Tokio 结合，实现各种异步生成器模式。主要特点包括：

1. 基本的生成器语法
2. 异步生成器实现
3. 流式处理
4. 状态管理
5. 错误处理
6. 并发控制
7. 资源管理
8. 超时处理
9. 可取消操作
10. 生成器组合

通过这些模式，您可以构建复杂的异步数据流处理系统。记住要使用 nightly 版本的 Rust，因为 `gen` 特性目前还是不稳定的。
