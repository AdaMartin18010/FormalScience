/// # 并发模式示例
/// 
/// 本文件展示 Rust 中的并发编程模式：
/// - 线程和线程安全
/// - 同步原语
/// - 无锁数据结构
/// - Actor 模式
/// - 工作窃取
/// 
/// 对应理论：进程演算、并发理论、内存模型

use std::sync::{mpsc, Arc, Mutex, RwLock, Barrier};
use std::thread;
use std::time::Duration;
use std::sync::atomic::{AtomicUsize, Ordering};

// ============================================================
// 第一部分：基础线程
// ============================================================

/// 创建线程和 join
fn basic_threads() {
    println!("=== 基础线程 ===");
    
    let handle = thread::spawn(|| {
        for i in 1..=3 {
            println!("Spawned thread: {}", i);
            thread::sleep(Duration::from_millis(1));
        }
    });
    
    for i in 1..=3 {
        println!("Main thread: {}", i);
        thread::sleep(Duration::from_millis(1));
    }
    
    // 等待子线程完成
    handle.join().unwrap();
    
    println!();
}

/// 使用 move 闭包传递数据
fn move_closure() {
    println!("=== Move 闭包 ===");
    
    let v = vec![1, 2, 3];
    
    let handle = thread::spawn(move || {
        println!("Vector from thread: {:?}", v);
    });
    
    handle.join().unwrap();
    // println!("{:?}", v);  // 错误！v 已经被移动到线程中
    
    println!();
}

// ============================================================
// 第二部分：消息传递
// ============================================================

/// 使用 mpsc 通道
fn channel_demo() {
    println!("=== 消息通道 ===");
    
    let (tx, rx) = mpsc::channel();
    
    thread::spawn(move || {
        let val = String::from("hi");
        tx.send(val).unwrap();
        // println!("val is {}", val);  // 错误！val 已经被发送
    });
    
    let received = rx.recv().unwrap();
    println!("Got: {}", received);
    
    println!();
}

/// 发送多个值
fn multi_value_channel() {
    println!("=== 多值通道 ===");
    
    let (tx, rx) = mpsc::channel();
    
    thread::spawn(move || {
        let vals = vec![
            String::from("hi"),
            String::from("from"),
            String::from("the"),
            String::from("thread"),
        ];
        
        for val in vals {
            tx.send(val).unwrap();
            thread::sleep(Duration::from_millis(100));
        }
    });
    
    for received in rx {
        println!("Got: {}", received);
    }
    
    println!();
}

/// 多生产者
fn multi_producer() {
    println!("=== 多生产者 ===");
    
    let (tx, rx) = mpsc::channel();
    
    let tx1 = tx.clone();
    thread::spawn(move || {
        let vals = vec!["1: hi", "1: from", "1: thread"];
        for val in vals {
            tx1.send(val).unwrap();
            thread::sleep(Duration::from_millis(50));
        }
    });
    
    thread::spawn(move || {
        let vals = vec!["2: more", "2: messages", "2: here"];
        for val in vals {
            tx.send(val).unwrap();
            thread::sleep(Duration::from_millis(50));
        }
    });
    
    for received in rx {
        println!("Got: {}", received);
    }
    
    println!();
}

// ============================================================
// 第三部分：共享状态
// ============================================================

/// 使用 Mutex
fn mutex_demo() {
    println!("=== Mutex ===");
    
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];
    
    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            let mut num = counter.lock().unwrap();
            *num += 1;
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("Result: {}", *counter.lock().unwrap());
    println!();
}

/// 使用 RwLock
fn rwlock_demo() {
    println!("=== RwLock ===");
    
    let data = Arc::new(RwLock::new(vec![1, 2, 3]));
    
    // 多个读者
    let mut readers = vec![];
    for i in 0..3 {
        let data = Arc::clone(&data);
        readers.push(thread::spawn(move || {
            let read = data.read().unwrap();
            println!("Reader {}: {:?}", i, *read);
        }));
    }
    
    for reader in readers {
        reader.join().unwrap();
    }
    
    // 一个写者
    let data_clone = Arc::clone(&data);
    let writer = thread::spawn(move || {
        let mut write = data_clone.write().unwrap();
        write.push(4);
        println!("Writer: added 4");
    });
    
    writer.join().unwrap();
    
    println!("Final: {:?}", *data.read().unwrap());
    println!();
}

// ============================================================
// 第四部分：原子操作
// ============================================================

/// 使用原子变量
fn atomic_demo() {
    println!("=== 原子操作 ===");
    
    let counter = Arc::new(AtomicUsize::new(0));
    let mut handles = vec![];
    
    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        handles.push(thread::spawn(move || {
            counter.fetch_add(1, Ordering::Relaxed);
        }));
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("Result: {}", counter.load(Ordering::Relaxed));
    println!();
}

/// 原子内存顺序
fn memory_ordering() {
    println!("=== 内存顺序 ===");
    
    // Relaxed: 最弱约束，只保证原子性
    let x = AtomicUsize::new(0);
    x.store(1, Ordering::Relaxed);
    let _val = x.load(Ordering::Relaxed);
    
    // Acquire/Release: 用于同步
    let y = AtomicUsize::new(0);
    y.store(1, Ordering::Release);
    let _val = y.load(Ordering::Acquire);
    
    // SeqCst: 最强约束，全局顺序
    let z = AtomicUsize::new(0);
    z.store(1, Ordering::SeqCst);
    let _val = z.load(Ordering::SeqCst);
    
    println!("Memory ordering demonstration complete");
    println!();
}

// ============================================================
// 第五部分：同步原语
// ============================================================

/// 使用 Barrier
fn barrier_demo() {
    println!("=== Barrier ===");
    
    let barrier = Arc::new(Barrier::new(3));
    let mut handles = vec![];
    
    for i in 0..3 {
        let barrier = Arc::clone(&barrier);
        handles.push(thread::spawn(move || {
            println!("Thread {} before barrier", i);
            thread::sleep(Duration::from_millis(100 * i as u64));
            barrier.wait();
            println!("Thread {} after barrier", i);
        }));
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!();
}

/// 使用 Condvar
fn condvar_demo() {
    println!("=== Condition Variable ===");
    
    use std::sync::Condvar;
    
    let pair = Arc::new((Mutex::new(false), Condvar::new()));
    let pair2 = Arc::clone(&pair);
    
    thread::spawn(move || {
        let (lock, cvar) = &*pair2;
        let mut started = lock.lock().unwrap();
        *started = true;
        println!("Worker: signaling...");
        cvar.notify_one();
    });
    
    let (lock, cvar) = &*pair;
    let mut started = lock.lock().unwrap();
    while !*started {
        println!("Main: waiting...");
        started = cvar.wait(started).unwrap();
    }
    println!("Main: started!");
    
    println!();
}

// ============================================================
// 第六部分：线程池
// ============================================================

use std::sync::mpsc::{Receiver, Sender};

/// 简单的线程池实现
type Job = Box<dyn FnOnce() + Send + 'static>;

struct ThreadPool {
    workers: Vec<Worker>,
    sender: Option<Sender<Job>>,
}

impl ThreadPool {
    fn new(size: usize) -> ThreadPool {
        let (sender, receiver) = mpsc::channel();
        let receiver = Arc::new(Mutex::new(receiver));
        
        let mut workers = Vec::with_capacity(size);
        for id in 0..size {
            workers.push(Worker::new(id, Arc::clone(&receiver)));
        }
        
        ThreadPool {
            workers,
            sender: Some(sender),
        }
    }
    
    fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        let job = Box::new(f);
        self.sender.as_ref().unwrap().send(job).unwrap();
    }
}

impl Drop for ThreadPool {
    fn drop(&mut self) {
        drop(self.sender.take());
        
        for worker in &mut self.workers {
            println!("Shutting down worker {}", worker.id);
            
            if let Some(thread) = worker.thread.take() {
                thread.join().unwrap();
            }
        }
    }
}

struct Worker {
    id: usize,
    thread: Option<thread::JoinHandle<()>>,
}

impl Worker {
    fn new(id: usize, receiver: Arc<Mutex<Receiver<Job>>>) -> Worker {
        let thread = thread::spawn(move || loop {
            let message = receiver.lock().unwrap().recv();
            
            match message {
                Ok(job) => {
                    println!("Worker {} got a job; executing.", id);
                    job();
                }
                Err(_) => {
                    println!("Worker {} shutting down.", id);
                    break;
                }
            }
        });
        
        Worker {
            id,
            thread: Some(thread),
        }
    }
}

fn threadpool_demo() {
    println!("=== 线程池 ===");
    
    let pool = ThreadPool::new(4);
    
    for i in 0..8 {
        pool.execute(move || {
            println!("Job {} started", i);
            thread::sleep(Duration::from_millis(50));
            println!("Job {} completed", i);
        });
    }
    
    thread::sleep(Duration::from_millis(500));
    
    println!("Thread pool demo complete");
    println!();
}

// ============================================================
// 第七部分：Actor 模式
// ============================================================

/// 简单的 Actor 实现
trait Actor {
    type Message;
    fn handle(&mut self, msg: Self::Message);
}

/// 计数器 Actor
struct CounterActor {
    count: i32,
}

#[derive(Debug)]
enum CounterMessage {
    Increment,
    Decrement,
    Get,
}

impl Actor for CounterActor {
    type Message = CounterMessage;
    
    fn handle(&mut self, msg: Self::Message) {
        match msg {
            CounterMessage::Increment => {
                self.count += 1;
                println!("Counter incremented to {}", self.count);
            }
            CounterMessage::Decrement => {
                self.count -= 1;
                println!("Counter decremented to {}", self.count);
            }
            CounterMessage::Get => {
                println!("Current count: {}", self.count);
            }
        }
    }
}

fn actor_demo() {
    println!("=== Actor 模式 ===");
    
    let (tx, rx) = mpsc::channel::<CounterMessage>();
    
    thread::spawn(move || {
        let mut actor = CounterActor { count: 0 };
        while let Ok(msg) = rx.recv() {
            actor.handle(msg);
        }
    });
    
    tx.send(CounterMessage::Increment).unwrap();
    tx.send(CounterMessage::Increment).unwrap();
    tx.send(CounterMessage::Get).unwrap();
    tx.send(CounterMessage::Decrement).unwrap();
    tx.send(CounterMessage::Get).unwrap();
    
    thread::sleep(Duration::from_millis(100));
    
    println!();
}

// ============================================================
// 第八部分：无锁数据结构
// ============================================================

/// 使用 crossbeam 的无锁数据结构（概念演示）
fn lock_free_concept() {
    println!("=== 无锁数据结构概念 ===");
    
    // 无锁队列的基本思想
    // 实际实现需要使用 atomic 指针操作
    println!("Lock-free data structures use atomic operations:");
    println!("- Compare-and-swap (CAS)");
    println!("- Load-link/store-conditional (LL/SC)");
    println!("- Memory ordering constraints");
    
    // 简单的无锁计数器演示
    let counter = Arc::new(AtomicUsize::new(0));
    let mut handles = vec![];
    
    for _ in 0..100 {
        let counter = Arc::clone(&counter);
        handles.push(thread::spawn(move || {
            // 使用 CAS 循环实现无锁递增
            loop {
                let current = counter.load(Ordering::Relaxed);
                let new = current + 1;
                match counter.compare_exchange(
                    current,
                    new,
                    Ordering::SeqCst,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => break,
                    Err(_) => continue,  // 重试
                }
            }
        }));
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("Lock-free counter result: {}", counter.load(Ordering::Relaxed));
    println!();
}

// ============================================================
// 主函数
// ============================================================

fn main() {
    println!("╔══════════════════════════════════════════════════════════╗");
    println!("║          Rust 并发模式示例                                ║");
    println!("╚══════════════════════════════════════════════════════════╝\n");
    
    basic_threads();
    move_closure();
    channel_demo();
    multi_value_channel();
    multi_producer();
    mutex_demo();
    rwlock_demo();
    atomic_demo();
    memory_ordering();
    barrier_demo();
    condvar_demo();
    threadpool_demo();
    actor_demo();
    lock_free_concept();
    
    println!("╔══════════════════════════════════════════════════════════╗");
    println!("║          所有示例运行完成！                               ║");
    println!("╚══════════════════════════════════════════════════════════╝");
}

/*
输出说明：

编译和运行：
```bash
rustc --edition 2021 concurrent_patterns.rs -o concurrent_patterns
./concurrent_patterns
```

预期输出：
```
╔══════════════════════════════════════════════════════════╗
║          Rust 并发模式示例                                ║
╚══════════════════════════════════════════════════════════╝

=== 基础线程 ===
Main thread: 1
Spawned thread: 1
...

=== 消息通道 ===
Got: hi

=== 多值通道 ===
Got: hi
Got: from
Got: the
Got: thread

=== 多生产者 ===
...

=== Mutex ===
Result: 10

=== RwLock ===
...

=== 原子操作 ===
Result: 10

=== 内存顺序 ===
Memory ordering demonstration complete

=== Barrier ===
...

=== Condition Variable ===
...

=== 线程池 ===
...

=== Actor 模式 ===
Counter incremented to 1
...

=== 无锁数据结构概念 ===
Lock-free counter result: 100

╔══════════════════════════════════════════════════════════╗
║          所有示例运行完成！                               ║
╚══════════════════════════════════════════════════════════╝
```

理论对应：
- 消息传递 ↔ CSP（Communicating Sequential Processes）
- Mutex/RwLock ↔ 互斥和读写锁理论
- 原子操作 ↔ 顺序一致性模型
- Actor ↔ Actor Model
- 无锁结构 ↔ 非阻塞同步理论
*/
