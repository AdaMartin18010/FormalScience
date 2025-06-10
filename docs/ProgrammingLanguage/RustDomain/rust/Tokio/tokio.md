# Rust异步编程与资源管理

在 Tokio 的异步编程中，资源管理是优化性能和确保高效运行的关键。
Tokio 提供了多种机制和策略来管理资源，以下是一些核心概念和实践方法：

## 目录

- [Rust异步编程与资源管理](#rust异步编程与资源管理)
  - [目录](#目录)
  - [1. 合理管理并发任务](#1-合理管理并发任务)
  - [2. 使用连接池](#2-使用连接池)
  - [3. 任务预算策略](#3-任务预算策略)
  - [4. 超时管理](#4-超时管理)
  - [5. 资源释放和取消操作](#5-资源释放和取消操作)
  - [6. 性能监控](#6-性能监控)
  - [7. 避免阻塞操作](#7-避免阻塞操作)
  - [8. 优雅关闭](#8-优雅关闭)
  - [9. 使用合适的同步机制](#9-使用合适的同步机制)
  - [1. 选择运行时模式](#1-选择运行时模式)
  - [2. 任务调度与并发](#2-任务调度与并发)
  - [3. 优化并发性能](#3-优化并发性能)
  - [4. 资源管理](#4-资源管理)
  - [2. 任务调度策略](#2-任务调度策略)
  - [3. 任务优先级](#3-任务优先级)
  - [4. 监控与调整](#4-监控与调整)
  - [5. 第三方调度器](#5-第三方调度器)
  - [3. 使用 tokio::sync::watch 通道](#3-使用-tokiosyncwatch-通道)
  - [4. 使用 tokio::sync::broadcast 通道](#4-使用-tokiosyncbroadcast-通道)
  - [5. 使用 tokio::sync::oneshot 通道](#5-使用-tokiosynconeshot-通道)
  - [1. 使用 JoinHandle 等待多个任务完成](#1-使用-joinhandle-等待多个任务完成)
  - [2. 使用 tokio::sync::Barrier](#2-使用-tokiosyncbarrier)
  - [1. 使用 tokio::sync::Notify](#1-使用-tokiosyncnotify)
  - [4. 使用 tokio::task::JoinSet](#4-使用-tokiotaskjoinset)
  - [1. 基本使用](#1-基本使用)
  - [2. 实现简单的通道](#2-实现简单的通道)
  - [3. 多生产者多消费者（MPMC）通道](#3-多生产者多消费者mpmc通道)
  - [4. 通知所有等待者](#4-通知所有等待者)

## 1. 合理管理并发任务

Tokio 的运行时支持多线程和单线程模式，可以根据应用需求选择合适的并发模型：
多线程运行时：通过 Builder::new_multi_thread() 创建，适合需要高并发处理的场景。
单线程运行时：通过 Builder::new_current_thread() 创建，适合简单的异步任务。

## 2. 使用连接池

连接池是管理资源的有效方式，可以限制同时打开的连接数量，减少内存和 CPU 的消耗。
例如，使用数据库连接池可以避免频繁创建和销毁连接。

## 3. 任务预算策略

Tokio 通过任务预算策略（budget）来避免任务饥饿和资源过度占用。
每个任务在运行时都有一个预算限制（例如 128 次操作），当预算耗尽时，任务会自动让出执行权，调度器切换到其他任务。

## 4. 超时管理

Tokio 提供了超时管理机制，通过 tokio::time::timeout() 函数可以为异步任务设置超时时间。
这有助于避免任务长时间占用资源。

## 5. 资源释放和取消操作

在使用完资源后，应确保正确地取消或回收资源，避免内存泄漏。
例如，使用 Future 时，可以通过 drop() 显式释放资源。

## 6. 性能监控

Tokio 提供了性能监控工具，如 tokio::time::Instant，用于测量代码执行时间，从而找出性能瓶颈。

## 7. 避免阻塞操作

在 Tokio 中，应尽量避免阻塞操作，因为这会阻止事件循环调度其他任务。
如果必须进行阻塞操作，可以使用 tokio::task::spawn_blocking() 将其移到独立线程中。

## 8. 优雅关闭

在程序结束时，Tokio 提供了优雅关闭的机制，可以通过信号处理（如 tokio::signal::ctrl_c()）来安全地关闭运行时。

## 9. 使用合适的同步机制

Tokio 提供了多种同步机制，如互斥锁（Mutex）、信号量（Semaphore）等，用于同步多个任务之间的操作。

总结
Tokio 的资源管理策略包括合理配置并发模型、使用连接池、任务预算策略、超时管理、资源释放、性能监控、避免阻塞操作以及优雅关闭等。
通过这些机制，开发者可以更好地控制资源的使用，提高应用的性能和稳定性。

在 Tokio 中，设置并发模型主要涉及选择合适的运行时配置以及合理安排任务的调度方式。
Tokio 提供了多种运行时配置选项，可以根据应用需求选择单线程或多线程模式，并通过任务调度器管理并发任务。
以下是具体的设置方法和示例：

## 1. 选择运行时模式

Tokio 提供了两种主要的运行时模式：
单线程模式：所有任务都在同一个线程中执行，适合轻量级任务。
多线程模式：任务在多个线程中并发执行，适合需要高并发处理的场景。
配置单线程运行时

```rust
use tokio::runtime::Builder;

fn main() {
    let rt = Builder::new_current_thread()
        .enable_all() // 启用所有特性（I/O、时间等）
        .build()
        .unwrap();

    rt.block_on(async {
        println!("Running in single-threaded runtime");
        tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
        println!("Task completed");
    });
}
```

配置多线程运行时

```rust
use tokio::runtime::Builder;

fn main() {
    let rt = Builder::new_multi_thread()
        .worker_threads(4) // 指定工作线程数
        .enable_all() // 启用所有特性
        .build()
        .unwrap();

        rt.block_on(async {
        println!("Running in multi-threaded runtime");
        tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
        println!("Task completed");
        });
}
```

## 2. 任务调度与并发

 Tokio 使用 M:N 模型，其中 M 表示轻量级任务的数量，N 表示操作系统线程的数量。默认情况下，Tokio 会根据 CPU 核心数配置线程池大小，但也可以手动调整。
 动态任务调度通过 tokio::spawn 启动异步任务，并使用 join 等待任务完成。

 ```rust
 #[tokio::main]
 async fn main() {
     let task1 = tokio::spawn(async {
         tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
         println!("Task 1 completed");
     });

     let task2 = tokio::spawn(async {
         tokio::time::sleep(tokio::time::Duration::from_secs(2)).await;
         println!("Task 2 completed");
     });

     let _ = tokio::try_join!(task1, task2);
 }
 ```

## 3. 优化并发性能

 限制任务数量：通过 Semaphore 或其他同步机制限制同时运行的任务数量。
 合理配置线程池：根据应用需求调整线程池大小。
 避免阻塞操作：使用 tokio::task::spawn_blocking 处理阻塞任务。

## 4. 资源管理

 Tokio 的任务调度器会根据任务的 I/O 状态和 .await 点进行任务切换。
 合理使用 .await 可以避免任务饥饿，同时提高资源利用率。

总结
 通过选择合适的运行时模式（单线程或多线程）、合理配置任务调度以及优化资源管理，Tokio 可以高效地处理并发任务。
 开发者可以根据应用的实际需求调整运行时配置，以达到最佳性能。

在 Tokio 中优化任务调度是提高异步应用性能的关键。
以下是一些基于最新搜索结果的优化建议和实现方法：

1. 合理选择运行时模式

 Tokio 提供了单线程和多线程运行时，选择合适的模式对任务调度至关重要：
 单线程运行时：适用于轻量级任务，减少线程切换开销。
 多线程运行时：适合高并发场景，通过多个线程提高任务处理能力。

1. 任务偷取（Work Stealing）

 Tokio 的多线程运行时使用任务偷取机制来平衡任务负载：
 每个线程维护一个本地队列（local queue）和一个全局队列（global queue）。
 当本地队列为空时，线程会尝试从全局队列或其它线程的本地队列中“偷取”任务。
 Tokio 限制本地队列的大小（如 256 个任务），超出部分的任务会被移至全局队列。

1. LIFO 优化

 Tokio 使用 LIFO（后进先出）槽优化任务调度：
 当一个任务唤醒另一个任务时，被唤醒的任务会被优先放入 LIFO 槽。
 如果 LIFO 槽已被占用，旧任务会被移入本地队列，新任务放入 LIFO 槽。
 这种机制减少了任务切换的延迟，同时优化了 CPU 缓存的利用率。

1. 公平性保证

 Tokio 提供了公平性保证，确保任务不会被饿死：
 如果任务总数不超过某个上限（MAX_TASKS），且每个任务的调度时间不超过某个上限（MAX_SCHEDULE），则 Tokio 保证任务在一定时间内被调度。
 Tokio 会定期检查全局队列，避免任务在队列中等待过久。

1. 减少内存分配

 Tokio 的新调度器减少了任务的内存分配次数：
 旧版本中，每个任务需要两次内存分配，而新版本通过优化减少了分配次数。
 任务状态被划分为“热”数据（频繁访问）和“冷”数据（较少访问），以优化 CPU 缓存的使用。

1. 避免任务饥饿
 Tokio 提供了协作式调度机制，避免任务长时间占用调度器：
 如果任务长时间运行而不让出执行权，可能会饿死其他任务。
 使用 tokio::task::yield_now() 可以让任务主动让出执行权。

1. 优化消息传递
 Tokio 对消息传递模式进行了优化：
 当任务通过通道（channel）发送消息时，接收任务会被优先调度，减少消息传递的延迟。

1. 动态调整调度策略
 Tokio 允许动态调整调度策略：
 例如，可以通过 global_queue_interval 设置全局队列的检查间隔。
 可以通过 event_interval 设置事件检查的频率。

总结
优化 Tokio 的任务调度需要综合考虑运行时模式、任务偷取、LIFO 优化、公平性保证、内存分配、协作式调度和消息传递等多个方面。
通过合理配置这些机制，可以显著提升 Tokio 应用的性能和并发能力。

在 Tokio 中，调度器的动态调整主要通过配置运行时（Runtime）和任务调度策略来实现。
以下是基于最新搜索结果的动态调整方法和配置建议：

1. 运行时配置
 Tokio 提供了灵活的运行时配置选项，可以通过 tokio::runtime::Builder 来调整调度器的行为。
 示例：配置多线程运行时

 ```rust
 use tokio::runtime::Builder;

 fn main() {
     let rt = Builder::new_multi_thread()
         .worker_threads(4) // 设置工作线程数量
         .enable_all() // 启用所有特性（I/O、时间等）
         .build()
         .unwrap();

     rt.block_on(async {
         // 异步任务
         tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
         println!("Task completed");
     });
 }
 ```

 示例：配置单线程运行时

 ```rust
 use tokio::runtime::Builder;

 fn main() {
     let rt = Builder::new_current_thread()
         .enable_all()
         .build()
         .unwrap();

     rt.block_on(async {
         // 异步任务
         tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
         println!("Task completed");
     });
 }
 ```

## 2. 任务调度策略

 Tokio 的调度器使用任务偷取（Work Stealing）和 LIFO（后进先出）槽来优化任务调度。
 动态调整调度策略
 任务队列大小：可以通过环境变量 TOKIO_MAX_TASKS 和 TOKIO_MAX_SCHEDULE 来调整任务队列的大小和调度限制。
 全局队列检查间隔：通过 global_queue_interval 设置全局队列的检查间隔。
 事件检查频率：通过 event_interval 设置事件检查的频率。

## 3. 任务优先级

 虽然 Tokio 的默认调度器不支持任务优先级，但可以通过第三方库（如 tokio-task-scheduler）来实现。
 示例：使用 tokio-task-scheduler 设置任务优先级

 ```rust
 use tokio_task_scheduler::{Scheduler, TaskBuilder};
 use std::time::Duration;
 use tokio;

 #[tokio::main]
 async fn main() -> Result<(), Box<dyn std::error::Error>> {
     let scheduler = Scheduler::new();

     // 创建一个高优先级任务
     let high_priority_task = TaskBuilder::new("high_priority", || {
         println!("High priority task");
         Ok(())
     })
     .every_seconds(10)
     .with_priority(1) // 设置优先级
     .build();

     // 创建一个低优先级任务
     let low_priority_task = TaskBuilder::new("low_priority", || {
         println!("Low priority task");
         Ok(())
     })
     .every_seconds(20)
     .with_priority(2) // 设置优先级
     .build();

     scheduler.add_task(high_priority_task).await?;
     scheduler.add_task(low_priority_task).await?;

     scheduler.start().await?;

     tokio::time::sleep(Duration::from_secs(60)).await;

     scheduler.stop().await?;
     Ok(())
 }
 ```

## 4. 监控与调整

 Tokio 提供了监控工具（如 tokio::time::Instant）来测量任务的执行时间，从而动态调整调度策略。

## 5. 第三方调度器

 如果需要更复杂的调度功能（如定时任务、任务依赖等），可以使用第三方库（如 tokio-cron-scheduler）。
 示例：使用 tokio-cron-scheduler 添加定时任务

 ```rust
 use std::time::Duration;
 use tokio_cron_scheduler::{Job, JobScheduler, JobSchedulerError};

 #[tokio::main]
 async fn main() -> Result<(), JobSchedulerError> {
     let mut sched = JobScheduler::new().await?;

     // 添加每 10 秒运行一次的任务
     sched.add(
         Job::new("1/10 * * * * *", |_uuid, _l| {
             println!("I run every 10 seconds");
         })?
     ).await?;

     // 添加一次性任务
     sched.add(
         Job::new_one_shot(Duration::from_secs(18), |_uuid, _l| {
             println!("I only run once");
         })?
     ).await?;

     sched.start().await?;

     tokio::time::sleep(Duration::from_secs(100)).await;

     Ok(())
 }
 ```

总结
通过合理配置运行时模式、调整任务调度策略、使用任务优先级和第三方调度器，Tokio 的调度器可以动态调整以满足不同的性能需求。
开发者可以根据应用的实际场景选择合适的配置和工具，以优化任务调度的效率和性能。

在 Tokio 中，消息队列和消息通知是异步编程中的重要功能，可以通过多种方式实现。以下是基于最新搜索结果的实现方法和示例代码：

1. 使用 Tokio 的内置通道（Channel）

 Tokio 提供了多种内置通道（如 mpsc 和 broadcast），用于在异步任务之间传递消息。
 示例：使用 mpsc 通道

 ```rust复制
 use tokio::sync::mpsc;

 #[tokio::main]
 async fn main() {
     let (tx, mut rx) = mpsc::unbounded_channel();

     tokio::spawn(async move {
         tx.send("hello").await.unwrap();
     });

     let msg = rx.recv().await.unwrap();
     println!("{}", msg);
 }
 ```

 在这个示例中，mpsc::unbounded_channel 创建了一个无界通道，任务可以通过 tx.send 发送消息，而接收者可以通过 rx.recv 接收消息。

1. 使用有界通道（Bounded Channel）
 为了控制内存使用和实现背压，可以使用有界通道。
 示例：使用 async-channel 创建有界通道

 ```rust复制
 use async_channel::{bounded, Sender, Receiver};

 #[tokio::main]
 async fn main() {
     let (tx, rx) = bounded(10); // 创建容量为 10 的有界通道

     tokio::spawn(async move {
         tx.send("hello").await.unwrap();
     });

     let msg = rx.recv().await.unwrap();
     println!("{}", msg);
 }
 ```

 在这个示例中，bounded(10) 创建了一个容量为 10 的有界通道，当通道已满时，发送者会等待直到有空间。

## 3. 使用 tokio::sync::watch 通道

 watch 通道适用于一对多的通知场景，发送者可以通知所有接收者。
 示例：使用 watch 通道

 ```rust复制
 use tokio::sync::watch;

 #[tokio::main]
 async fn main() {
     let (tx, mut rx) = watch::channel("initial value");

     tokio::spawn(async move {
         // 等待通知
         while rx.changed().await.is_ok() {
             println!("Received: {}", *rx.borrow());
         }
     });

     // 发送通知
     tx.send("new value").unwrap();
 }
 ```

 在这个示例中，watch::channel 创建了一个通道，发送者可以通过 tx.send 更新值，所有接收者会收到通知。

## 4. 使用 tokio::sync::broadcast 通道

 broadcast 通道允许发送者向多个接收者广播消息。
 示例：使用 broadcast 通道

 ```rust复制
 use tokio::sync::broadcast;

 #[tokio::main]
 async fn main() {
     let (tx, mut rx) = broadcast::channel(16); // 创建容量为 16 的广播通道

     tokio::spawn(async move {
         while let Ok(msg) = rx.recv().await {
             println!("Received: {}", msg);
         }
     });

     // 发送消息
     tx.send("hello").unwrap();
 }
 ```

 在这个示例中，broadcast::channel(16) 创建了一个容量为 16 的广播通道，发送者可以通过 tx.send 发送消息，所有接收者会收到消息。

## 5. 使用 tokio::sync::oneshot 通道

 oneshot 通道用于发送单个消息，适用于任务完成通知。
 示例：使用 oneshot 通道

 ```rust复制
 use tokio::sync::oneshot;

 #[tokio::main]
 async fn main() {
     let (tx, rx) = oneshot::channel();

     tokio::spawn(async move {
         tx.send("task completed").unwrap();
     });

     let msg = rx.await.unwrap();
     println!("{}", msg);
 }
 ```

 在这个示例中，oneshot::channel 创建了一个单次通道，发送者可以通过 tx.send 发送消息，接收者可以通过 rx.await 接收消息。

总结
 Tokio 提供了多种通道类型，适用于不同的消息传递场景：
  mpsc：用于任务间的消息传递。
  async-channel：提供有界通道，支持背压控制。
  watch：适用于一对多的通知场景。
  broadcast：用于向多个接收者广播消息。
  oneshot：用于发送单个消息，适用于任务完成通知。
 通过合理选择通道类型，可以高效地实现异步消息队列和通知机制。

在 Tokio 中，虽然没有直接等价于 Go 的 sync.WaitGroup 的机制，但可以通过组合使用 JoinHandle 和 tokio::sync 提供的同步原语（如 Notify 或 Barrier）来实现类似的功能。
以下是实现类似 sync.WaitGroup 功能的几种方法：

## 1. 使用 JoinHandle 等待多个任务完成

 JoinHandle 是 Tokio 中用于等待任务完成的机制。通过收集所有任务的 JoinHandle，可以等待所有任务完成。
 示例代码：

 ```rust复制
 #[tokio::main]
 async fn main() {
     let mut handles = vec![];

     for i in 0..10 {
         let handle = tokio::spawn(async move {
             println!("Task {} started", i);
             tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
             println!("Task {} completed", i);
         });
         handles.push(handle);
     }

     // 等待所有任务完成
     for handle in handles {
         handle.await.unwrap();
     }

     println!("All tasks have completed");
 }
 ```

## 2. 使用 tokio::sync::Barrier

 Barrier 是一个同步原语，用于等待多个任务到达某个点。它可以用于模拟 sync.WaitGroup 的功能。
 示例代码：

 ```rust
 use tokio::sync::Barrier;

 #[tokio::main]
 async fn main() {
     let num_tasks = 10;
     let barrier = Arc::new(Barrier::new(num_tasks));

     for i in 0..num_tasks {
         let barrier = Arc::clone(&barrier);
         tokio::spawn(async move {
             println!("Task {} started", i);
             tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
             println!("Task {} reached the barrier", i);
             barrier.wait().await;
             println!("Task {} continued", i);
         });
     }

     println!("All tasks have reached the barrier");
 }
 ```

## 1. 使用 tokio::sync::Notify

 Notify 是一个用于任务间通知的同步原语。可以通过 Notify 来实现任务完成的通知机制。
 示例代码：

 ```rust
 use tokio::sync::Notify;
 use std::sync::Arc;

 #[tokio::main]
 async fn main() {
     let notify = Arc::new(Notify::new());
     let mut handles = vec![];

     for i in 0..10 {
         let notify = Arc::clone(&notify);
         let handle = tokio::spawn(async move {
             println!("Task {} started", i);
             tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
             println!("Task {} completed", i);
             notify.notify_one();
         });
         handles.push(handle);
     }

     // 等待所有任务完成
     for handle in handles {
         handle.await.unwrap();
     }

     println!("All tasks have completed");
 }
 ```

## 4. 使用 tokio::task::JoinSet

 JoinSet 是一个用于管理多个任务的集合。它可以用于等待所有任务完成。
 示例代码：

 ```rust
 use tokio::task::JoinSet;

 #[tokio::main]
 async fn main() {
     let mut join_set = JoinSet::new();

     for i in 0..10 {
         join_set.spawn(async move {
             println!("Task {} started", i);
             tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
             println!("Task {} completed", i);
         });
     }

     // 等待所有任务完成
     while let Some(result) = join_set.join_next().await {
         result.unwrap();
     }

     println!("All tasks have completed");
 }
 ```

总结
 虽然 Tokio 没有直接等价于 Go 的 sync.WaitGroup，但可以通过以下方式实现类似功能：
  使用 JoinHandle 等待多个任务完成。
  使用 tokio::sync::Barrier 等待多个任务到达某个点。
  使用 tokio::sync::Notify 实现任务完成的通知。
  使用 tokio::task::JoinSet 管理多个任务。
  这些工具和方法可以帮助你在 Tokio 中实现任务同步和等待机制。

在 Tokio 中，Notify 是一个用于任务间通知的同步原语，用于在异步任务之间传递信号。
它类似于 Go 的 sync.WaitGroup，但功能更灵活。以下是 Notify 的使用方法和示例：

## 1. 基本使用

 Notify 提供了一种机制，允许一个任务通知另一个任务执行某些操作。它本身不携带数据，而是用于信号传递。
 示例代码：

 ```rust
 use tokio::sync::Notify;
 use std::sync::Arc;

 #[tokio::main]
 async fn main() {
     let notify = Arc::new(Notify::new());
     let notify2 = notify.clone();

     let handle = tokio::spawn(async move {
         notify2.notified().await; // 等待通知
         println!("received notification");
     });

     println!("sending notification");
     notify.notify_one(); // 发送通知

     // 等待任务接收通知
     handle.await.unwrap();
 }
 ```

## 2. 实现简单的通道

 Notify 可以用于实现简单的消息通道，例如一个单生产者单消费者（SPSC）通道。
 示例代码：

 ```rust
 use tokio::sync::Notify;
 use std::collections::VecDeque;
 use std::sync::Mutex;

 struct Channel<T> {
     values: Mutex<VecDeque<T>>,
     notify: Notify,
 }

 impl<T> Channel<T> {
     pub fn new() -> Self {
         Self {
             values: Mutex::new(VecDeque::new()),
             notify: Notify::new(),
         }
     }

     pub fn send(&self, value: T) {
         self.values.lock().unwrap().push_back(value);
         self.notify.notify_one(); // 通知消费者
     }

     pub async fn recv(&self) -> T {
         loop {
             if let Some(value) = self.values.lock().unwrap().pop_front() {
                 return value;
             }
             self.notify.notified().await; // 等待通知
         }
     }
 }

 #[tokio::main]
 async fn main() {
     let channel = Arc::new(Channel::new());
     let channel_clone = channel.clone();

     let sender = tokio::spawn(async move {
         channel_clone.send("Hello, world!");
     });

     let receiver = tokio::spawn(async move {
         let msg = channel.recv().await;
         println!("Received: {}", msg);
     });

     sender.await.unwrap();
     receiver.await.unwrap();
 }
 ```

## 3. 多生产者多消费者（MPMC）通道

 Notify 也可以用于实现多生产者多消费者（MPMC）通道。
 示例代码：

 ```rust
 use tokio::sync::Notify;
 use std::collections::VecDeque;
 use std::sync::Mutex;

 struct Channel<T> {
     messages: Mutex<VecDeque<T>>,
     notify_on_sent: Notify,
 }

 impl<T> Channel<T> {
     pub fn new() -> Self {
         Self {
             messages: Mutex::new(VecDeque::new()),
             notify_on_sent: Notify::new(),
         }
     }

     pub fn send(&self, msg: T) {
         let mut locked_queue = self.messages.lock().unwrap();
         locked_queue.push_back(msg);
         drop(locked_queue);

         self.notify_on_sent.notify_one(); // 通知消费者
     }

     pub fn try_recv(&self) -> Option<T> {
         let mut locked_queue = self.messages.lock().unwrap();
         locked_queue.pop_front()
     }

     pub async fn recv(&self) -> T {
         let future = self.notify_on_sent.notified();
         tokio::pin!(future);

         loop {
             future.as_mut().enable(); // 确保不会丢失唤醒

             if let Some(msg) = self.try_recv() {
                 return msg;
             }

             future.as_mut().await; // 等待通知

             // 重置未来，以防另一个 `try_recv` 在我们之前获取了消息
             future.set(self.notify_on_sent.notified());
         }
     }
 }

 #[tokio::main]
 async fn main() {
     let channel = Arc::new(Channel::new());
     let channel_clone = channel.clone();

     let sender = tokio::spawn(async move {
         channel_clone.send("Hello, world!");
     });

     let receiver = tokio::spawn(async move {
         let msg = channel.recv().await;
         println!("Received: {}", msg);
     });

     sender.await.unwrap();
     receiver.await.unwrap();
 }
 ```

## 4. 通知所有等待者

 Notify 提供了 notify_waiters() 方法，可以通知所有等待的任务。
 示例代码：

 ```rust
 use tokio::sync::Notify;
 use std::sync::Arc;

 #[tokio::main]
 async fn main() {
     let notify = Arc::new(Notify::new());
     let notify2 = notify.clone();

     let notified1 = notify.notified();
     let notified2 = notify.notified();

     let handle = tokio::spawn(async move {
         println!("sending notifications");
         notify2.notify_waiters(); // 通知所有等待者
     });

     notified1.await;
     notified2.await;
     println!("received notifications");
 }
 ```

总结
 Notify 是一个强大的同步原语，适用于任务间的通知机制。它支持以下功能：
 单任务通知：通过 notify_one() 唤醒一个等待任务。
 多任务通知：通过 notify_waiters() 唤醒所有等待任务。
 实现通道：可以用于实现简单的消息队列，支持单生产者单消费者（SPSC）或多生产者多消费者（MPMC）模式。
 通过合理使用 Notify，可以实现高效的异步任务同步和通信。
