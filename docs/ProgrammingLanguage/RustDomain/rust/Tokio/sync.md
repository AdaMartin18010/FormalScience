# rust Tokio 同步机制

以下是关于 Tokio 同步机制 的详细介绍，包括定义、概念、示例代码以及思维导图。内容以 Markdown 格式输出。
Tokio 同步机制
Tokio 提供了多种同步机制，用于在异步任务之间进行同步和通信。
这些机制包括互斥锁（Mutex）、信号量（Semaphore）、屏障（Barrier）、通道（Channel）、通知（Notify）等。

## 目录

- [rust Tokio 同步机制](#rust-tokio-同步机制)
  - [目录](#目录)
  - [1. 互斥锁（Mutex）](#1-互斥锁mutex)
  - [2. 信号量（Semaphore）](#2-信号量semaphore)
  - [3. 屏障（Barrier）](#3-屏障barrier)
  - [4. 通道（Channel）](#4-通道channel)
  - [5. 通知（Notify）](#5-通知notify)

## 1. 互斥锁（Mutex）

互斥锁用于保护共享资源，确保同一时间只有一个任务可以访问该资源。
概念
    互斥锁：允许多个任务竞争访问一个共享资源，但同一时间只有一个任务可以持有锁。
    异步安全：Tokio 的 Mutex 是异步安全的，适用于异步任务。
示例代码

```rust
use tokio::sync::Mutex;
use std::sync::Arc;

#[tokio::main]
async fn main() {
    let mutex = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let mutex = Arc::clone(&mutex);
        let handle = tokio::spawn(async move {
            let mut num = mutex.lock().await;
            *num += 1;
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.await.unwrap();
    }

    println!("Result: {}", *mutex.lock().await);
}
```

## 2. 信号量（Semaphore）

信号量用于限制同时访问某个资源的任务数量。
概念
    信号量：通过计数器控制同时访问资源的任务数量。
    许可（Permits）：任务需要获取许可后才能继续执行。
示例代码

```rust
    use tokio::sync::Semaphore;
    use std::sync::Arc;

    #[tokio::main]
    async fn main() {
        let semaphore = Arc::new(Semaphore::new(3)); // 最多允许3个任务同时运行
        let mut handles = vec![];

        for i in 0..10 {
            let semaphore = Arc::clone(&semaphore);
            let handle = tokio::spawn(async move {
                let permit = semaphore.acquire().await.unwrap();
                println!("Task {} started", i);
                tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
                println!("Task {} completed", i);
                drop(permit); // 释放许可
            });
            handles.push(handle);
        }

        for handle in handles {
            handle.await.unwrap();
        }
    }
```

## 3. 屏障（Barrier）

屏障用于等待多个任务到达某个点。
概念
    屏障：所有任务必须到达屏障后才能继续执行。
    同步点：用于任务同步，确保所有任务完成某个阶段后再继续。
示例代码

```rust
    use tokio::sync::Barrier;
    use std::sync::Arc;

    #[tokio::main]
    async fn main() {
        let barrier = Arc::new(Barrier::new(10));
        let mut handles = vec![];

        for _ in 0..10 {
            let barrier = Arc::clone(&barrier);
            let handle = tokio::spawn(async move {
                println!("Task before wait");
                barrier.wait().await;
                println!("Task after wait");
            });
            handles.push(handle);
        }

        for handle in handles {
            handle.await.unwrap();
        }
    }
```

## 4. 通道（Channel）

通道用于任务之间的消息传递。
概念
    MPSC：多生产者单消费者通道。
    Oneshot：单生产者单消费者通道，用于任务完成通知。
    Broadcast：多生产者多消费者通道，用于广播消息。
    Watch：单生产者多消费者通道，用于状态通知。
示例代码
MPSC 通道

```rust
    use tokio::sync::mpsc;

    #[tokio::main]
    async fn main() {
        let (tx, mut rx) = mpsc::channel(10);

        let tx1 = tx.clone();
        tokio::spawn(async move {
            tx1.send("Hello from task 1").await.unwrap();
        });

        let tx2 = tx.clone();
        tokio::spawn(async move {
            tx2.send("Hello from task 2").await.unwrap();
        });

        while let Some(msg) = rx.recv().await {
            println!("Received: {}", msg);
        }
    }
```

## 5. 通知（Notify）

通知用于任务间的通知机制。
概念
Notify：用于任务间的通知，不携带数据。
唤醒机制：通知等待的任务继续执行。
示例代码

```rust
    use tokio::sync::Notify;
    use std::sync::Arc;

    #[tokio::main]
    async fn main() {
        let notify = Arc::new(Notify::new());
        let notify_clone = Arc::clone(&notify);

        let handle = tokio::spawn(async move {
            notify_clone.notified().await;
            println!("Received notification");
        });

        notify.notify_one();
        handle.await.unwrap();
    }
```

思维导图

```Mermaid
Code经典手绘
graph TD
    A[Tokio 同步机制] --> B[Mutex]
    A --> C[Semaphore]
    A --> D[Barrier]
    A --> E[Channel]
    A --> F[Notify]

    B --> B1[互斥锁]
    B --> B2[保护共享资源]
    B --> B3[异步安全]

    C --> C1[信号量]
    C --> C2[限制任务数量]
    C --> C3[许可机制]

    D --> D1[屏障]
    D --> D2[任务同步]
    D --> D3[同步点]

    E --> E1[MPSC]
    E --> E2[Oneshot]
    E --> E3[Broadcast]
    E --> E4[Watch]
    E --> E5[消息传递]

    F --> F1[通知]
    F --> F2[任务间通知]
    F --> F3[唤醒机制]
```

Tokio 同步机制
Mutex
Semaphore
Barrier
Channel
Notify
互斥锁
保护共享资源
异步安全
信号量
限制任务数量
许可机制
屏障
任务同步
同步点
MPSC
Oneshot
Broadcast
Watch
消息传递
通知
任务间通知
唤醒机制
通过这些同步机制，Tokio 提供了强大的工具来管理异步任务之间的同步和通信。
开发者可以根据具体需求选择合适的同步机制，以实现高效的异步编程
