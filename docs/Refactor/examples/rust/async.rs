/// # 异步编程示例
/// 
/// 本文件展示 Rust 异步编程的核心概念：
/// - Future 和 async/await
/// - 执行器（Executor）
/// - 并发组合
/// - 流（Streams）
/// - 超时和取消
/// 
/// 对应理论：计算理论、并发模型

use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
use std::time::{Duration, Instant};

// ============================================================
// 第一部分：Future 基础
// ============================================================

/// 自定义 Future：计时器
struct Delay {
    when: Instant,
}

impl Future for Delay {
    type Output = &'static str;
    
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        if Instant::now() >= self.when {
            println!("Hello world!");
            Poll::Ready("done")
        } else {
            // 安排在未来某个时间唤醒
            cx.waker().wake_by_ref();
            Poll::Pending
        }
    }
}

/// 使用自定义 Future
async fn delay_demo() {
    println!("=== 自定义 Future ===");
    
    let when = Instant::now() + Duration::from_millis(10);
    let delay = Delay { when };
    
    let out = delay.await;
    println!("Result: {}", out);
    
    println!();
}

// ============================================================
// 第二部分：async/await 基础
// ============================================================

/// 基本的异步函数
async fn hello_world() -> String {
    "Hello, world!".to_string()
}

/// 异步函数组合
async fn say_hello() {
    println!("Hello!");
}

async fn say_world() {
    println!("World!");
}

async fn async_composition() {
    println!("=== async/await 基础 ===");
    
    // 顺序执行
    say_hello().await;
    say_world().await;
    
    let result = hello_world().await;
    println!("Result: {}", result);
    
    println!();
}

// ============================================================
// 第三部分：并发执行
// ============================================================

use futures::future::{join, join_all, select, Either};
use futures::stream::{self, StreamExt};

/// 模拟异步操作
async fn fetch_data(id: u32) -> String {
    tokio::time::sleep(Duration::from_millis(10)).await;
    format!("Data {}", id)
}

/// 使用 join 并发执行
async fn concurrent_with_join() {
    println!("=== 使用 join 并发 ===");
    
    let f1 = fetch_data(1);
    let f2 = fetch_data(2);
    let f3 = fetch_data(3);
    
    let (r1, r2, r3) = join!(f1, f2, f3);
    
    println!("Results: {}, {}, {}", r1, r2, r3);
    println!();
}

/// 使用 join_all 处理动态数量的 Future
async fn concurrent_with_join_all() {
    println!("=== 使用 join_all ===");
    
    let futures = (0..5).map(|i| fetch_data(i));
    let results = join_all(futures).await;
    
    for (i, result) in results.iter().enumerate() {
        println!("Result {}: {}", i, result);
    }
    
    println!();
}

/// 使用 select 等待多个 Future（返回最先完成的）
async fn race_demo() {
    println!("=== 使用 select 竞争 ===");
    
    async fn slow() -> &'static str {
        tokio::time::sleep(Duration::from_millis(20)).await;
        "slow"
    }
    
    async fn fast() -> &'static str {
        tokio::time::sleep(Duration::from_millis(5)).await;
        "fast"
    }
    
    let result = match select(Box::pin(slow()), Box::pin(fast())).await {
        Either::Left((result, _)) => result,
        Either::Right((result, _)) => result,
    };
    
    println!("Winner: {}", result);
    println!();
}

// ============================================================
// 第四部分：流（Streams）
// ============================================================

/// 使用流处理异步序列
async fn stream_demo() {
    println!("=== Stream 处理 ===");
    
    // 创建一个数字流
    let mut stream = stream::iter(vec![1, 2, 3, 4, 5]);
    
    // 使用 while let 消费流
    while let Some(num) = stream.next().await {
        println!("Received: {}", num);
    }
    
    println!();
}

/// 流的转换操作
async fn stream_transform() {
    println!("=== Stream 转换 ===");
    
    let stream = stream::iter(vec![1, 2, 3, 4, 5])
        .map(|x| x * 2)  // 每个元素乘以 2
        .filter(|x| *x > 4);  // 过滤大于 4 的元素
    
    stream.for_each(|x| async move {
        println!("Transformed: {}", x);
    }).await;
    
    println!();
}

/// 从异步操作创建流
async fn async_stream() {
    println!("=== 异步 Stream ===");
    
    use futures::stream::Stream;
    use std::pin::Pin;
    
    // 创建一个生成定时事件的流
    async fn ticker(interval_ms: u64, count: usize) -> impl Stream<Item = usize> {
        stream::unfold(0, move |state| async move {
            if state < count {
                tokio::time::sleep(Duration::from_millis(interval_ms)).await;
                Some((state, state + 1))
            } else {
                None
            }
        })
    }
    
    let mut stream = ticker(5, 3);
    while let Some(tick) = stream.next().await {
        println!("Tick: {}", tick);
    }
    
    println!();
}

// ============================================================
// 第五部分：超时和取消
// ============================================================

use tokio::time::timeout;

/// 超时处理
async fn timeout_demo() {
    println!("=== 超时处理 ===");
    
    let slow_operation = async {
        tokio::time::sleep(Duration::from_millis(100)).await;
        "completed"
    };
    
    match timeout(Duration::from_millis(50), slow_operation).await {
        Ok(result) => println!("Operation succeeded: {}", result),
        Err(_) => println!("Operation timed out!"),
    }
    
    println!();
}

/// 取消安全
async fn cancel_safe_demo() {
    println!("=== 取消安全 ===");
    
    use tokio::select;
    
    let operation = async {
        println!("Starting long operation...");
        tokio::time::sleep(Duration::from_millis(100)).await;
        println!("Long operation completed");
        "result"
    };
    
    let timeout = tokio::time::sleep(Duration::from_millis(10));
    
    tokio::pin!(operation);
    
    select! {
        _ = timeout => {
            println!("Cancelled!");
        }
        _ = &mut operation => {
            println!("Completed!");
        }
    }
    
    println!();
}

// ============================================================
// 第六部分：通道和消息传递
// ============================================================

use tokio::sync::mpsc;

/// 使用通道进行异步通信
async fn channel_demo() {
    println!("=== 异步通道 ===");
    
    let (tx, mut rx) = mpsc::channel(100);
    
    // 发送任务
    let sender = tokio::spawn(async move {
        for i in 0..5 {
            tx.send(i).await.unwrap();
            println!("Sent: {}", i);
        }
    });
    
    // 接收任务
    let receiver = tokio::spawn(async move {
        while let Some(val) = rx.recv().await {
            println!("Received: {}", val);
        }
    });
    
    let _ = tokio::join!(sender, receiver);
    
    println!();
}

/// 多生产者单消费者
async fn mpsc_demo() {
    println!("=== 多生产者单消费者 ===");
    
    let (tx, mut rx) = mpsc::channel(100);
    
    let tx2 = tx.clone();
    
    let producer1 = tokio::spawn(async move {
        for i in 0..3 {
            tx.send(format!("Producer 1: {}", i)).await.unwrap();
        }
    });
    
    let producer2 = tokio::spawn(async move {
        for i in 0..3 {
            tx2.send(format!("Producer 2: {}", i)).await.unwrap();
        }
    });
    
    let consumer = tokio::spawn(async move {
        while let Some(msg) = rx.recv().await {
            println!("Received: {}", msg);
        }
    });
    
    let _ = tokio::join!(producer1, producer2, consumer);
    
    println!();
}

// ============================================================
// 第七部分：共享状态
// ============================================================

use tokio::sync::{Mutex, RwLock};
use std::sync::Arc;

/// 使用 Mutex 保护共享状态
async fn shared_state_demo() {
    println!("=== 共享状态 ===");
    
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];
    
    for i in 0..5 {
        let counter = Arc::clone(&counter);
        let handle = tokio::spawn(async move {
            let mut num = counter.lock().await;
            *num += 1;
            println!("Task {} incremented counter to {}", i, *num);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.await.unwrap();
    }
    
    println!("Final counter: {}", *counter.lock().await);
    println!();
}

/// 使用 RwLock 进行读写分离
async fn rwlock_demo() {
    println!("=== RwLock ===");
    
    let data = Arc::new(RwLock::new(vec![1, 2, 3]));
    
    // 多个读者
    let reader1 = {
        let data = Arc::clone(&data);
        tokio::spawn(async move {
            let read = data.read().await;
            println!("Reader 1 sees: {:?}", *read);
        })
    };
    
    let reader2 = {
        let data = Arc::clone(&data);
        tokio::spawn(async move {
            let read = data.read().await;
            println!("Reader 2 sees: {:?}", *read);
        })
    };
    
    // 一个写者
    let writer = {
        let data = Arc::clone(&data);
        tokio::spawn(async move {
            let mut write = data.write().await;
            write.push(4);
            println!("Writer added 4");
        })
    };
    
    let _ = tokio::join!(reader1, reader2, writer);
    
    println!("Final data: {:?}", *data.read().await);
    println!();
}

// ============================================================
// 主函数
// ============================================================

#[tokio::main]
async fn main() {
    println!("╔══════════════════════════════════════════════════════════╗");
    println!("║          Rust 异步编程示例                                ║");
    println!("╚══════════════════════════════════════════════════════════╝\n");
    
    delay_demo().await;
    async_composition().await;
    concurrent_with_join().await;
    concurrent_with_join_all().await;
    race_demo().await;
    stream_demo().await;
    stream_transform().await;
    async_stream().await;
    timeout_demo().await;
    cancel_safe_demo().await;
    channel_demo().await;
    mpsc_demo().await;
    shared_state_demo().await;
    rwlock_demo().await;
    
    println!("╔══════════════════════════════════════════════════════════╗");
    println!("║          所有示例运行完成！                               ║");
    println!("╚══════════════════════════════════════════════════════════╝");
}

/*
输出说明：

运行要求：
```bash
cargo add tokio --features full
cargo add futures
```

编译和运行（使用 Cargo）：
```bash
cargo run --bin async
```

或者手动：
```bash
rustc --edition 2021 async.rs --extern tokio=... --extern futures=... -o async
./async
```

预期输出：
```
╔══════════════════════════════════════════════════════════╗
║          Rust 异步编程示例                                ║
╚══════════════════════════════════════════════════════════╝

=== 自定义 Future ===
Hello world!
Result: done

=== async/await 基础 ===
Hello!
World!
Result: Hello, world!

=== 使用 join 并发 ===
Results: Data 1, Data 2, Data 3

=== 使用 join_all ===
Result 0: Data 0
...

=== 使用 select 竞争 ===
Winner: fast

=== Stream 处理 ===
Received: 1
...

=== 超时处理 ===
Operation timed out!

=== 取消安全 ===
Starting long operation...
Cancelled!

=== 异步通道 ===
...

╔══════════════════════════════════════════════════════════╗
║          所有示例运行完成！                               ║
╚══════════════════════════════════════════════════════════╝
```

理论对应：
- Future ↔ 延续（Continuation）
- async/await ↔ 状态机变换
- Stream ↔ 共归纳类型（Coinductive Types）
- 通道 ↔ CSP（Communicating Sequential Processes）
*/
