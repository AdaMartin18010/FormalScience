/// Tokio 使用示例
/// 
/// 演示 Tokio 异步运行时的主要功能和最佳实践

use std::io;
use std::time::{Duration, Instant};

// ============== 基本异步函数 ==============

/// 模拟异步IO操作
async fn fetch_data(id: u32) -> Result<String, String> {
    println!("开始获取数据 {}...", id);
    
    // 模拟网络延迟
    tokio::time::sleep(Duration::from_millis(100)).await;
    
    if id % 5 == 0 {
        Err(format!("数据 {} 获取失败", id))
    } else {
        Ok(format!("数据 {} 的内容", id))
    }
}

/// 并发获取多个数据
async fn fetch_concurrent() -> Vec<Result<String, String>> {
    let handles: Vec<_> = (1..=5)
        .map(|i| tokio::spawn(fetch_data(i)))
        .collect();
    
    let mut results = Vec::new();
    for handle in handles {
        results.push(handle.await.unwrap());
    }
    
    results
}

/// 使用 join! 并发执行
async fn use_join() {
    println!("\n=== 使用 join! ===");
    
    let f1 = fetch_data(1);
    let f2 = fetch_data(2);
    let f3 = fetch_data(3);
    
    let start = Instant::now();
    let (r1, r2, r3) = tokio::join!(f1, f2, f3);
    
    println!("并发完成，耗时 {:?}", start.elapsed());
    println!("结果: {:?}, {:?}, {:?}", r1, r2, r3);
}

/// 使用 select! 选择最快完成的
async fn use_select() {
    println!("\n=== 使用 select! ===");
    
    let f1 = tokio::time::sleep(Duration::from_millis(100));
    let f2 = tokio::time::sleep(Duration::from_millis(50));
    let f3 = tokio::time::sleep(Duration::from_millis(150));
    
    tokio::select! {
        _ = f1 => println!("任务 1 (100ms) 最先完成"),
        _ = f2 => println!("任务 2 (50ms) 最先完成"),
        _ = f3 => println!("任务 3 (150ms) 最先完成"),
    }
}

/// 使用 timeout
async fn use_timeout() {
    println!("\n=== 使用 timeout ===");
    
    let result = tokio::time::timeout(
        Duration::from_millis(50),
        fetch_data(1)
    ).await;
    
    match result {
        Ok(Ok(data)) => println!("成功获取: {}", data),
        Ok(Err(e)) => println!("获取失败: {}", e),
        Err(_) => println!("超时!"),
    }
}

// ============== 通道使用 ==============

/// 多生产者单消费者 (MPSC)
async fn demo_mpsc() {
    println!("\n=== MPSC 通道 ===");
    
    let (tx, mut rx) = tokio::sync::mpsc::channel(100);
    
    // 生产者任务
    let producer = async move {
        for i in 0..5 {
            if tx.send(i).await.is_err() {
                break;
            }
            println!("发送: {}", i);
        }
    };
    
    // 消费者任务
    let consumer = async move {
        while let Some(val) = rx.recv().await {
            println!("接收: {}", val);
        }
    };
    
    tokio::join!(producer, consumer);
}

/// 广播通道
async fn demo_broadcast() {
    println!("\n=== 广播通道 ===");
    
    let (tx, mut rx1) = tokio::sync::broadcast::channel(16);
    let mut rx2 = tx.subscribe();
    let mut rx3 = tx.subscribe();
    
    // 发送任务
    let sender = async move {
        for i in 0..3 {
            tx.send(format!("消息 {}", i)).unwrap();
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    };
    
    // 接收任务
    let recv1 = async move {
        while let Ok(msg) = rx1.recv().await {
            println!("接收者 1: {}", msg);
        }
    };
    
    let recv2 = async move {
        while let Ok(msg) = rx2.recv().await {
            println!("接收者 2: {}", msg);
            if msg == "消息 1" {
                break; // 接收者 2 提前退出
            }
        }
    };
    
    let recv3 = async move {
        while let Ok(msg) = rx3.recv().await {
            println!("接收者 3: {}", msg);
        }
    };
    
    tokio::join!(sender, recv1, recv2, recv3);
}

/// 一次性通道 (oneshot)
async fn demo_oneshot() {
    println!("\n=== Oneshot 通道 ===");
    
    let (tx, rx) = tokio::sync::oneshot::channel();
    
    let producer = async move {
        tokio::time::sleep(Duration::from_millis(100)).await;
        tx.send("完成结果").unwrap();
    };
    
    let consumer = async move {
        match rx.await {
            Ok(result) => println!("收到结果: {}", result),
            Err(_) => println!("发送者已关闭"),
        }
    };
    
    tokio::join!(producer, consumer);
}

// ============== 同步原语 ==============

/// 互斥锁 (Mutex)
async fn demo_mutex() {
    println!("\n=== Tokio Mutex ===");
    
    let data = std::sync::Arc::new(tokio::sync::Mutex::new(0));
    let mut handles = vec![];
    
    for i in 0..5 {
        let data = data.clone();
        handles.push(tokio::spawn(async move {
            let mut guard = data.lock().await;
            *guard += 1;
            println!("任务 {} 增加计数到 {}", i, *guard);
        }));
    }
    
    for handle in handles {
        handle.await.unwrap();
    }
    
    println!("最终值: {}", *data.lock().await);
}

/// 读写锁 (RwLock)
async fn demo_rwlock() {
    println!("\n=== Tokio RwLock ===");
    
    let data = std::sync::Arc::new(tokio::sync::RwLock::new(String::from("Hello")));
    
    // 多个读者
    let mut read_handles = vec![];
    for i in 0..3 {
        let data = data.clone();
        read_handles.push(tokio::spawn(async move {
            let guard = data.read().await;
            println!("读者 {} 读取: {}", i, *guard);
        }));
    }
    
    for handle in read_handles {
        handle.await.unwrap();
    }
    
    // 一个写者
    let mut guard = data.write().await;
    guard.push_str(" World!");
    println!("写者写入: {}", *guard);
}

/// 信号量 (Semaphore)
async fn demo_semaphore() {
    println!("\n=== Tokio Semaphore ===");
    
    // 限制并发数为 2
    let semaphore = std::sync::Arc::new(tokio::sync::Semaphore::new(2));
    let mut handles = vec![];
    
    for i in 0..5 {
        let permit = semaphore.clone().acquire_owned().await.unwrap();
        handles.push(tokio::spawn(async move {
            println!("任务 {} 获取许可，开始执行", i);
            tokio::time::sleep(Duration::from_millis(100)).await;
            println!("任务 {} 完成", i);
            drop(permit); // 释放许可
        }));
    }
    
    for handle in handles {
        handle.await.unwrap();
    }
}

// ============== 文件IO ==============

/// 异步文件操作
async fn demo_file_io() -> io::Result<()> {
    println!("\n=== 异步文件 IO ===");
    
    use tokio::fs::File;
    use tokio::io::{AsyncReadExt, AsyncWriteExt};
    
    // 写入文件
    let mut file = File::create("test_async.txt").await?;
    file.write_all(b"Hello from Tokio!").await?;
    file.flush().await?;
    drop(file);
    
    println!("文件写入完成");
    
    // 读取文件
    let mut file = File::open("test_async.txt").await?;
    let mut contents = String::new();
    file.read_to_string(&mut contents).await?;
    
    println!("文件内容: {}", contents);
    
    // 清理
    tokio::fs::remove_file("test_async.txt").await?;
    println!("临时文件已删除");
    
    Ok(())
}

// ============== 网络编程 ==============

/// TCP 客户端示例（简化版）
async fn demo_tcp() {
    println!("\n=== TCP 网络编程 ===");
    
    use tokio::io::{AsyncReadExt, AsyncWriteExt};
    use tokio::net::TcpListener;
    
    // 启动服务器
    let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
    let addr = listener.local_addr().unwrap();
    println!("服务器监听: {}", addr);
    
    let server = tokio::spawn(async move {
        let (mut socket, _) = listener.accept().await.unwrap();
        
        let mut buf = [0u8; 1024];
        let n = socket.read(&mut buf).await.unwrap();
        let received = String::from_utf8_lossy(&buf[..n]);
        println!("服务器收到: {}", received);
        
        socket.write_all(b"Received your message").await.unwrap();
    });
    
    // 客户端
    let client = tokio::spawn(async move {
        let mut stream = tokio::net::TcpStream::connect(addr).await.unwrap();
        
        stream.write_all(b"Hello Server!").await.unwrap();
        
        let mut buf = [0u8; 1024];
        let n = stream.read(&mut buf).await.unwrap();
        let response = String::from_utf8_lossy(&buf[..n]);
        println!("客户端收到: {}", response);
    });
    
    tokio::join!(server, client);
}

// ============== 任务管理 ==============

/// 任务取消
async fn demo_task_cancellation() {
    println!("\n=== 任务取消 ===");
    
    use tokio::sync::mpsc;
    use tokio::task::JoinHandle;
    
    let (tx, mut rx) = mpsc::channel(1);
    
    let task: JoinHandle<()> = tokio::spawn(async move {
        let mut interval = tokio::time::interval(Duration::from_millis(100));
        
        loop {
            tokio::select! {
                _ = interval.tick() => {
                    println!("任务运行中...");
                }
                _ = rx.recv() => {
                    println!("收到取消信号，任务退出");
                    break;
                }
            }
        }
    });
    
    // 让任务运行一段时间
    tokio::time::sleep(Duration::from_millis(350)).await;
    
    // 发送取消信号
    tx.send(()).await.unwrap();
    
    // 等待任务完成
    let _ = task.await;
}

/// 任务组管理
async fn demo_task_group() {
    println!("\n=== 任务组管理 ===");
    
    use tokio::task::JoinSet;
    
    let mut set = JoinSet::new();
    
    for i in 0..5 {
        set.spawn(async move {
            tokio::time::sleep(Duration::from_millis((5 - i) * 50)).await;
            println!("任务 {} 完成", i);
            i * 10
        });
    }
    
    while let Some(result) = set.join_next().await {
        match result {
            Ok(value) => println!("任务返回值: {}", value),
            Err(e) => println!("任务 panic: {:?}", e),
        }
    }
    
    println!("所有任务完成");
}

// ============== 流 (Stream) ==============

/// 使用 Stream
async fn demo_stream() {
    println!("\n=== Stream 处理 ===");
    
    use tokio_stream::StreamExt;
    use std::pin::pin;
    
    // 创建流并固定
    let stream = tokio_stream::iter(1..=5)
        .then(|i| async move {
            tokio::time::sleep(Duration::from_millis(50)).await;
            i * i
        });
    let mut stream = pin!(stream);
    
    // 消费流
    while let Some(value) = stream.next().await {
        println!("流元素: {}", value);
    }
}

// ============== 运行时配置 ==============

/// 多线程运行时
fn demo_multi_thread_runtime() {
    println!("\n=== 多线程运行时 ===");
    
    let rt = tokio::runtime::Runtime::new().unwrap();
    
    rt.block_on(async {
        let handles: Vec<_> = (0..10)
            .map(|i| {
                tokio::spawn(async move {
                    println!("任务 {} 在线程 {:?} 上运行", 
                             i, std::thread::current().id());
                })
            })
            .collect();
        
        for handle in handles {
            handle.await.unwrap();
        }
    });
}

/// 当前线程运行时
fn demo_current_thread_runtime() {
    println!("\n=== 当前线程运行时 ===");
    
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap();
    
    rt.block_on(async {
        println!("所有任务都在当前线程执行");
        
        for i in 0..3 {
            tokio::spawn(async move {
                println!("任务 {} 执行", i);
            }).await.unwrap();
        }
    });
}

// ============== 主函数 ==============

#[tokio::main]
async fn main() {
    println!("=== Tokio 异步运行时示例 ===");
    
    // 基本并发
    use_join().await;
    use_select().await;
    use_timeout().await;
    
    // 通道
    demo_mpsc().await;
    demo_broadcast().await;
    demo_oneshot().await;
    
    // 同步原语
    demo_mutex().await;
    demo_rwlock().await;
    demo_semaphore().await;
    
    // IO
    if let Err(e) = demo_file_io().await {
        eprintln!("文件IO错误: {}", e);
    }
    demo_tcp().await;
    
    // 任务管理
    demo_task_cancellation().await;
    demo_task_group().await;
    
    // 流
    demo_stream().await;
    
    // 运行时演示（需要单独的运行时）
    // demo_multi_thread_runtime();
    // demo_current_thread_runtime();
    
    println!("\n=== 示例完成 ===");
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_fetch_data() {
        let result = fetch_data(1).await;
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "数据 1 的内容");
        
        let result = fetch_data(5).await;
        assert!(result.is_err());
    }
    
    #[tokio::test]
    async fn test_mpsc() {
        let (tx, mut rx) = tokio::sync::mpsc::channel(10);
        
        tx.send(42).await.unwrap();
        assert_eq!(rx.recv().await, Some(42));
    }
    
    #[tokio::test]
    async fn test_mutex() {
        let mutex = tokio::sync::Mutex::new(0);
        
        {
            let mut guard = mutex.lock().await;
            *guard = 42;
        }
        
        assert_eq!(*mutex.lock().await, 42);
    }
    
    #[tokio::test]
    async fn test_timeout() {
        let result = tokio::time::timeout(
            Duration::from_millis(10),
            tokio::time::sleep(Duration::from_millis(100))
        ).await;
        
        assert!(result.is_err());
    }
}
