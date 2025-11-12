# Rust 2024 并发、并行与分布式设计模式实现指南

## 📋 目录

- [1 一、Rust 2024 并发设计模式](#1-一rust-2024-并发设计模式)
  - [1.1 互斥锁模式Mutex Pattern](#11-互斥锁模式mutex-pattern)
  - [1.2 读写锁模式Read-Write Lock Pattern](#12-读写锁模式read-write-lock-pattern)
  - [1.3 通道模式Channel Pattern](#13-通道模式channel-pattern)
  - [1.4 Actor 模式Actor Pattern](#14-actor-模式actor-pattern)
  - [1.5 异步任务模式Async Task Pattern](#15-异步任务模式async-task-pattern)
- [2 二、Rust 2024 并行设计模式](#2-二rust-2024-并行设计模式)
  - [2.1 分而治之模式Divide and Conquer Pattern](#21-分而治之模式divide-and-conquer-pattern)
  - [2.2 映射归约模式Map-Reduce Pattern](#22-映射归约模式map-reduce-pattern)
  - [2.3 工作窃取模式Work Stealing Pattern](#23-工作窃取模式work-stealing-pattern)
  - [2.4 数据并行模式Data Parallelism Pattern](#24-数据并行模式data-parallelism-pattern)
  - [2.5 管道并行模式Pipeline Parallelism Pattern](#25-管道并行模式pipeline-parallelism-pattern)
- [3 三、Rust 2024 分布式设计模式](#3-三rust-2024-分布式设计模式)
  - [3.1 主从模式Master-Worker Pattern](#31-主从模式master-worker-pattern)
  - [3.2 发布-订阅模式Publish-Subscribe Pattern](#32-发布-订阅模式publish-subscribe-pattern)
  - [3.3 远程过程调用模式RPC Pattern](#33-远程过程调用模式rpc-pattern)
  - [3.4 分布式锁模式Distributed Lock Pattern](#34-分布式锁模式distributed-lock-pattern)
  - [3.5 一致性哈希模式Consistent Hashing Pattern](#35-一致性哈希模式consistent-hashing-pattern)
- [4 四、Rust 2024 表达能力分析](#4-四rust-2024-表达能力分析)
  - [4.1 Rust 并发模式的表达能力](#41-rust-并发模式的表达能力)
  - [4.2 Rust 并行模式的表达能力](#42-rust-并行模式的表达能力)
  - [4.3 Rust 分布式模式的表达能力](#43-rust-分布式模式的表达能力)
- [5 五、Rust 2024 设计模式实现对比分析](#5-五rust-2024-设计模式实现对比分析)
  - [5.1 并发模式实现对比](#51-并发模式实现对比)
    - [1.1.1 互斥锁模式对比](#111-互斥锁模式对比)
    - [1.1.2 通道模式对比](#112-通道模式对比)
  - [5.2 并行模式实现对比](#52-并行模式实现对比)
    - [2.2.1 数据并行对比](#221-数据并行对比)
    - [2.2.2 分而治之模式对比](#222-分而治之模式对比)
  - [5.3 分布式模式实现对比](#53-分布式模式实现对比)
    - [3.3.1 RPC 模式对比](#331-rpc-模式对比)
- [6 六、结论与最佳实践](#6-六结论与最佳实践)
  - [6.1 Rust 2024 并发、并行和分布式设计模式的选择指南](#61-rust-2024-并发并行和分布式设计模式的选择指南)
    - [1.1.1 并发模式选择](#111-并发模式选择)
    - [1.1.2 并行模式选择](#112-并行模式选择)
    - [1.1.3 分布式模式选择](#113-分布式模式选择)
  - [6.2 Rust 2024 设计模式实现的最佳实践](#62-rust-2024-设计模式实现的最佳实践)
  - [6.3 并发编程最佳实践](#63-并发编程最佳实践)
  - [6.4 并行编程最佳实践](#64-并行编程最佳实践)
  - [6.5 分布式编程最佳实践](#65-分布式编程最佳实践)
  - [6.6 总结](#66-总结)

---

## 1 一、Rust 2024 并发设计模式

### 1.1 互斥锁模式Mutex Pattern

```rust
// 互斥锁模式 - 保护共享资源
use std::sync::{Arc, Mutex};
use std::thread;

// 共享状态
struct SharedState {
    counter: u64,
    message: String,
}

// 线程安全的包装器
struct ThreadSafeCounter {
    state: Arc<Mutex<SharedState>>,
}

impl ThreadSafeCounter {
    fn new(initial: u64, message: impl Into<String>) -> Self {
        ThreadSafeCounter {
            state: Arc::new(Mutex::new(SharedState {
                counter: initial,
                message: message.into(),
            })),
        }
    }
    
    fn increment(&self) -> u64 {
        let mut state = self.state.lock().unwrap();
        state.counter += 1;
        state.counter
    }
    
    fn update_message(&self, new_message: impl Into<String>) {
        let mut state = self.state.lock().unwrap();
        state.message = new_message.into();
    }
    
    fn get_state(&self) -> (u64, String) {
        let state = self.state.lock().unwrap();
        (state.counter, state.message.clone())
    }
}

// 使用示例
fn mutex_pattern_example() {
    let counter = ThreadSafeCounter::new(0, "初始消息");
    let counter_clone = counter.clone();
    
    // 创建线程修改共享状态
    let handle = thread::spawn(move || {
        for _ in 0..5 {
            let value = counter_clone.increment();
            println!("线程: 计数器值 = {}", value);
            thread::sleep(std::time::Duration::from_millis(10));
        }
        counter_clone.update_message("线程更新的消息");
    });
    
    // 主线程也修改共享状态
    for _ in 0..3 {
        let value = counter.increment();
        println!("主线程: 计数器值 = {}", value);
        thread::sleep(std::time::Duration::from_millis(15));
    }
    
    // 等待线程完成
    handle.join().unwrap();
    
    // 获取最终状态
    let (final_count, final_message) = counter.get_state();
    println!("最终状态: 计数 = {}, 消息 = '{}'", final_count, final_message);
}

impl Clone for ThreadSafeCounter {
    fn clone(&self) -> Self {
        ThreadSafeCounter {
            state: Arc::clone(&self.state),
        }
    }
}
```

### 1.2 读写锁模式Read-Write Lock Pattern

```rust
// 读写锁模式 - 允许多读单写访问
use std::sync::{Arc, RwLock};
use std::thread;

// 共享资源
struct Database {
    data: Vec<String>,
    access_count: usize,
}

// 线程安全的数据库访问
struct ThreadSafeDatabase {
    db: Arc<RwLock<Database>>,
}

impl ThreadSafeDatabase {
    fn new() -> Self {
        ThreadSafeDatabase {
            db: Arc::new(RwLock::new(Database {
                data: Vec::new(),
                access_count: 0,
            })),
        }
    }
    
    // 写操作 - 需要独占锁
    fn insert(&self, item: impl Into<String>) -> Result<(), String> {
        match self.db.write() {
            Ok(mut db) => {
                db.data.push(item.into());
                db.access_count += 1;
                Ok(())
            }
            Err(_) => Err("获取写锁失败".to_string()),
        }
    }
    
    // 读操作 - 可以并发读取
    fn get_all(&self) -> Result<Vec<String>, String> {
        match self.db.read() {
            Ok(db) => {
                // 模拟读取延迟
                thread::sleep(std::time::Duration::from_millis(50));
                let result = db.data.clone();
                Ok(result)
            }
            Err(_) => Err("获取读锁失败".to_string()),
        }
    }
    
    // 读操作 - 获取访问计数
    fn get_access_count(&self) -> Result<usize, String> {
        match self.db.read() {
            Ok(db) => Ok(db.access_count),
            Err(_) => Err("获取读锁失败".to_string()),
        }
    }
}

impl Clone for ThreadSafeDatabase {
    fn clone(&self) -> Self {
        ThreadSafeDatabase {
            db: Arc::clone(&self.db),
        }
    }
}

// 使用示例
fn rwlock_pattern_example() {
    let database = ThreadSafeDatabase::new();
    
    // 预填充数据
    for i in 0..5 {
        database.insert(format!("项目 {}", i)).unwrap();
    }
    
    // 创建多个读取线程
    let mut read_handles = vec![];
    for i in 0..3 {
        let db_clone = database.clone();
        let handle = thread::spawn(move || {
            println!("读取线程 {} 开始", i);
            match db_clone.get_all() {
                Ok(data) => println!("读取线程 {}: 读取了 {} 项", i, data.len()),
                Err(e) => println!("读取线程 {} 错误: {}", i, e),
            }
        });
        read_handles.push(handle);
    }
    
    // 创建写入线程
    let db_clone = database.clone();
    let write_handle = thread::spawn(move || {
        for i in 5..10 {
            println!("写入线程: 插入项目 {}", i);
            match db_clone.insert(format!("项目 {}", i)) {
                Ok(_) => println!("写入线程: 插入项目 {} 成功", i),
                Err(e) => println!("写入线程: 插入失败 {}", e),
            }
            thread::sleep(std::time::Duration::from_millis(20));
        }
    });
    
    // 等待所有线程完成
    for handle in read_handles {
        handle.join().unwrap();
    }
    write_handle.join().unwrap();
    
    // 检查最终状态
    println!("数据库访问计数: {}", database.get_access_count().unwrap());
    println!("最终数据项数: {}", database.get_all().unwrap().len());
}
```

### 1.3 通道模式Channel Pattern

```rust
// 通道模式 - 线程间消息传递
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

// 工作请求
enum WorkRequest {
    Task(String),
    Terminate,
}

// 工作结果
struct WorkResult {
    task_id: String,
    result: String,
}

// 工作者
struct Worker {
    receiver: mpsc::Receiver<WorkRequest>,
    result_sender: mpsc::Sender<WorkResult>,
}

impl Worker {
    fn new(
        receiver: mpsc::Receiver<WorkRequest>,
        result_sender: mpsc::Sender<WorkResult>,
    ) -> Self {
        Worker {
            receiver,
            result_sender,
        }
    }
    
    fn run(&self) {
        println!("工作者: 开始运行");
        
        loop {
            match self.receiver.recv() {
                Ok(WorkRequest::Task(task_id)) => {
                    println!("工作者: 处理任务 '{}'", task_id);
                    
                    // 模拟工作
                    thread::sleep(Duration::from_millis(100));
                    
                    // 发送结果
                    let result = WorkResult {
                        task_id: task_id.clone(),
                        result: format!("任务 '{}' 的结果", task_id),
                    };
                    
                    match self.result_sender.send(result) {
                        Ok(_) => println!("工作者: 已发送任务 '{}' 的结果", task_id),
                        Err(_) => println!("工作者: 无法发送结果，接收者可能已关闭"),
                    }
                }
                Ok(WorkRequest::Terminate) => {
                    println!("工作者: 收到终止信号");
                    break;
                }
                Err(_) => {
                    println!("工作者: 通道已关闭");
                    break;
                }
            }
        }
        
        println!("工作者: 停止运行");
    }
}

// 任务分发器
struct Dispatcher {
    task_sender: mpsc::Sender<WorkRequest>,
    result_receiver: mpsc::Receiver<WorkResult>,
}

impl Dispatcher {
    fn new() -> (Self, Worker) {
        let (task_sender, task_receiver) = mpsc::channel();
        let (result_sender, result_receiver) = mpsc::channel();
        
        let worker = Worker::new(task_receiver, result_sender);
        
        (
            Dispatcher {
                task_sender,
                result_receiver,
            },
            worker,
        )
    }
    
    fn dispatch_task(&self, task_id: impl Into<String>) -> Result<(), String> {
        let task = WorkRequest::Task(task_id.into());
        self.task_sender.send(task).map_err(|_| "发送任务失败".to_string())
    }
    
    fn terminate_worker(&self) -> Result<(), String> {
        self.task_sender
            .send(WorkRequest::Terminate)
            .map_err(|_| "发送终止信号失败".to_string())
    }
    
    fn collect_results(&self) -> Vec<WorkResult> {
        let mut results = Vec::new();
        
        while let Ok(result) = self.result_receiver.try_recv() {
            results.push(result);
        }
        
        results
    }
}

// 使用示例
fn channel_pattern_example() {
    // 创建分发器和工作者
    let (dispatcher, worker) = Dispatcher::new();
    
    // 在单独的线程中运行工作者
    let worker_thread = thread::spawn(move || {
        worker.run();
    });
    
    // 分发任务
    for i in 1..=5 {
        let task_id = format!("任务{}", i);
        match dispatcher.dispatch_task(&task_id) {
            Ok(_) => println!("主线程: 分发了 {}", task_id),
            Err(e) => println!("主线程: 分发失败 {}", e),
        }
        
        // 给工作者一些处理时间
        thread::sleep(Duration::from_millis(50));
        
        // 收集并处理结果
        let results = dispatcher.collect_results();
        for result in results {
            println!("主线程: 收到结果 - {} -> {}", result.task_id, result.result);
        }
    }
    
    // 等待所有任务完成
    thread::sleep(Duration::from_millis(200));
    
    // 收集最终结果
    let final_results = dispatcher.collect_results();
    println!("最终收到 {} 个结果", final_results.len());
    
    // 终止工作者
    dispatcher.terminate_worker().unwrap();
    
    // 等待工作者线程结束
    worker_thread.join().unwrap();
}
```

### 1.4 Actor 模式Actor Pattern

```rust
// Actor 模式 - 基于消息的并发
use std::collections::HashMap;
use std::sync::mpsc::{channel, Receiver, Sender};
use std::thread;

// Actor 消息
enum Message {
    Get { key: String, respond_to: Sender<Option<String>> },
    Set { key: String, value: String },
    Delete { key: String },
    Shutdown,
}

// 键值存储 Actor
struct KeyValueActor {
    receiver: Receiver<Message>,
    store: HashMap<String, String>,
}

impl KeyValueActor {
    fn new(receiver: Receiver<Message>) -> Self {
        KeyValueActor {
            receiver,
            store: HashMap::new(),
        }
    }
    
    fn run(&mut self) {
        println!("KV Actor: 开始运行");
        
        loop {
            match self.receiver.recv() {
                Ok(Message::Get { key, respond_to }) => {
                    println!("KV Actor: 获取键 '{}'", key);
                    let value = self.store.get(&key).cloned();
                    let _ = respond_to.send(value);
                }
                Ok(Message::Set { key, value }) => {
                    println!("KV Actor: 设置 '{}' = '{}'", key, value);
                    self.store.insert(key, value);
                }
                Ok(Message::Delete { key }) => {
                    println!("KV Actor: 删除键 '{}'", key);
                    self.store.remove(&key);
                }
                Ok(Message::Shutdown) => {
                    println!("KV Actor: 收到关闭信号");
                    break;
                }
                Err(_) => {
                    println!("KV Actor: 通道已关闭");
                    break;
                }
            }
        }
        
        println!("KV Actor: 停止运行");
    }
}

// Actor 引用 - 客户端用来与 Actor 交互
struct KeyValueActorRef {
    sender: Sender<Message>,
}

impl KeyValueActorRef {
    fn new(sender: Sender<Message>) -> Self {
        KeyValueActorRef { sender }
    }
    
    fn get(&self, key: impl Into<String>) -> Option<String> {
        let (respond_to_sender, respond_to_receiver) = channel();
        let key = key.into();
        
        self.sender
            .send(Message::Get {
                key,
                respond_to: respond_to_sender,
            })
            .expect("Actor 已停止");
        
        respond_to_receiver.recv().expect("Actor 响应失败")
    }
    
    fn set(&self, key: impl Into<String>, value: impl Into<String>) {
        self.sender
            .send(Message::Set {
                key: key.into(),
                value: value.into(),
            })
            .expect("Actor 已停止");
    }
    
    fn delete(&self, key: impl Into<String>) {
        self.sender
            .send(Message::Delete { key: key.into() })
            .expect("Actor 已停止");
    }
    
    fn shutdown(self) {
        let _ = self.sender.send(Message::Shutdown);
    }
}

impl Clone for KeyValueActorRef {
    fn clone(&self) -> Self {
        KeyValueActorRef {
            sender: self.sender.clone(),
        }
    }
}

// 创建 Actor 系统
fn spawn_kv_actor() -> (KeyValueActorRef, thread::JoinHandle<()>) {
    let (sender, receiver) = channel();
    let actor_ref = KeyValueActorRef::new(sender);
    
    let handle = thread::spawn(move || {
        let mut actor = KeyValueActor::new(receiver);
        actor.run();
    });
    
    (actor_ref, handle)
}

// 使用示例
fn actor_pattern_example() {
    // 创建 Actor
    let (actor_ref, actor_handle) = spawn_kv_actor();
    
    // 使用 Actor
    actor_ref.set("hello", "world");
    actor_ref.set("foo", "bar");
    
    // 获取值
    match actor_ref.get("hello") {
        Some(value) => println!("获取 'hello' = '{}'", value),
        None => println!("'hello' 不存在"),
    }
    
    // 删除键
    actor_ref.delete("foo");
    
    // 验证删除
    match actor_ref.get("foo") {
        Some(value) => println!("获取 'foo' = '{}'", value),
        None => println!("'foo' 不存在"),
    }
    
    // 创建 Actor 的克隆引用
    let actor_ref_clone = actor_ref.clone();
    
    // 在另一个线程中使用 Actor
    let client_handle = thread::spawn(move || {
        actor_ref_clone.set("thread", "value from thread");
        println!("线程: 设置了 'thread' 键");
        
        match actor_ref_clone.get("hello") {
            Some(value) => println!("线程: 获取 'hello' = '{}'", value),
            None => println!("线程: 'hello' 不存在"),
        }
    });
    
    // 等待客户端线程完成
    client_handle.join().unwrap();
    
    // 验证线程设置的值
    match actor_ref.get("thread") {
        Some(value) => println!("获取 'thread' = '{}'", value),
        None => println!("'thread' 不存在"),
    }
    
    // 关闭 Actor
    actor_ref.shutdown();
    
    // 等待 Actor 线程结束
    actor_handle.join().unwrap();
}
```

### 1.5 异步任务模式Async Task Pattern

```rust
// 异步任务模式 - 使用 async/await
use futures::future::join_all;
use std::time::Duration;
use tokio::time::sleep;

// 异步任务
async fn async_task(id: u32, duration_ms: u64) -> Result<String, String> {
    println!("任务 {} 开始", id);
    
    // 模拟异步工作
    sleep(Duration::from_millis(duration_ms)).await;
    
    // 模拟可能的失败
    if id % 5 == 0 {
        println!("任务 {} 失败", id);
        return Err(format!("任务 {} 失败", id));
    }
    
    println!("任务 {} 完成", id);
    Ok(format!("任务 {} 的结果", id))
}

// 任务执行器
struct AsyncTaskExecutor;

impl AsyncTaskExecutor {
    // 执行单个任务
    async fn execute_task(id: u32, duration_ms: u64) -> Result<String, String> {
        async_task(id, duration_ms).await
    }
    
    // 并发执行多个任务
    async fn execute_many(count: u32) -> Vec<Result<String, String>> {
        let mut futures = Vec::new();
        
        for i in 1..=count {
            // 随机持续时间，模拟不同的工作负载
            let duration = 100 + (i * 50) % 400;
            futures.push(Self::execute_task(i, duration as u64));
        }
        
        join_all(futures).await
    }
    
    // 执行任务并处理结果
    async fn execute_and_process(count: u32) -> (Vec<String>, Vec<String>) {
        let results = Self::execute_many(count).await;
        
        let mut successes = Vec::new();
        let mut failures = Vec::new();
        
        for result in results {
            match result {
                Ok(success) => successes.push(success),
                Err(error) => failures.push(error),
            }
        }
        
        (successes, failures)
    }
}

// 使用示例
#[tokio::main]
async fn async_task_pattern_example() {
    println!("开始异步任务示例");
    
    // 执行单个任务
    match AsyncTaskExecutor::execute_task(1, 200).await {
        Ok(result) => println!("单个任务结果: {}", result),
        Err(e) => println!("单个任务错误: {}", e),
    }
    
    // 执行多个任务并处理结果
    let (successes, failures) = AsyncTaskExecutor::execute_and_process(10).await;
    
    println!("成功完成的任务: {}", successes.len());
    for success in &successes {
        println!("  - {}", success);
    }
    
    println!("失败的任务: {}", failures.len());
    for failure in &failures {
        println!("  - {}", failure);
    }
    
    println!("异步任务示例完成");
}
```

## 2 二、Rust 2024 并行设计模式

### 2.1 分而治之模式Divide and Conquer Pattern

```rust
// 分而治之模式 - 递归分解问题
use rayon::prelude::*;
use std::time::Instant;

// 串行归并排序
fn merge_sort_serial<T: Ord + Copy>(slice: &mut [T]) {
    if slice.len() <= 1 {
        return;
    }
    
    let mid = slice.len() / 2;
    let (left, right) = slice.split_at_mut(mid);
    
    merge_sort_serial(left);
    merge_sort_serial(right);
    
    // 合并已排序的子数组
    let mut temp = Vec::with_capacity(slice.len());
    let mut left_idx = 0;
    let mut right_idx = 0;
    
    while left_idx < left.len() && right_idx < right.len() {
        if left[left_idx] <= right[right_idx] {
            temp.push(left[left_idx]);
            left_idx += 1;
        } else {
            temp.push(right[right_idx]);
            right_idx += 1;
        }
    }
    
    // 添加剩余元素
    temp.extend_from_slice(&left[left_idx..]);
    temp.extend_from_slice(&right[right_idx..]);
    
    // 复制回原数组
    slice.copy_from_slice(&temp);
}

// 并行归并排序
fn merge_sort_parallel<T: Ord + Copy + Send>(slice: &mut [T]) {
    if slice.len() <= 1024 {  // 小问题使用串行算法
        merge_sort_serial(slice);
        return;
    }
    
    let mid = slice.len() / 2;
    let (left, right) = slice.split_at_mut(mid);
    
    // 并行递归
    rayon::join(
        || merge_sort_parallel(left),
        || merge_sort_parallel(right)
    );
    
    // 合并已排序的子数组
    let mut temp = Vec::with_capacity(slice.len());
    let mut left_idx = 0;
    let mut right_idx = 0;
    
    while left_idx < left.len() && right_idx < right.len() {
        if left[left_idx] <= right[right_idx] {
            temp.push(left[left_idx]);
            left_idx += 1;
        } else {
            temp.push(right[right_idx]);
            right_idx += 1;
        }
    }
    
    // 添加剩余元素
    temp.extend_from_slice(&left[left_idx..]);
    temp.extend_from_slice(&right[right_idx..]);
    
    // 复制回原数组
    slice.copy_from_slice(&temp);
}

// 使用示例
fn divide_and_conquer_example() {
    // 创建大型测试数组
    let size = 1_000_000;
    let mut data_serial = Vec::with_capacity(size);
    let mut data_parallel = Vec::with_capacity(size);
    
    // 填充随机数据
    use rand::Rng;
    let mut rng = rand::thread_rng();
    
    for _ in 0..size {
        let value = rng.gen::<u32>();
        data_serial.push(value);
        data_parallel.push(value);
    }
    
    // 测量串行排序时间
    let start = Instant::now();
    merge_sort_serial(&mut data_serial);
    let serial_duration = start.elapsed();
    println!("串行排序耗时: {:?}", serial_duration);
    
    // 测量并行排序时间
    let start = Instant::now();
    merge_sort_parallel(&mut data_parallel);
    let parallel_duration = start.elapsed();
    println!("并行排序耗时: {:?}", parallel_duration);
    
    // 验证结果
    assert_eq!(data_serial, data_parallel);
    
    // 计算加速比
    let speedup = serial_duration.as_secs_f64() / parallel_duration.as_secs_f64();
    println!("加速比: {:.2}x", speedup);
}
```

### 2.2 映射归约模式Map-Reduce Pattern

```rust
// 映射归约模式 - 并行数据处理
use rayon::prelude::*;
use std::collections::HashMap;
use std::hash::Hash;
use std::time::Instant;

// 映射函数 - 将输入转换为键值对
fn map_function(text: &str) -> Vec<(String, u64)> {
    text.split_whitespace()
        .map(|word| {
            let word = word.to_lowercase()
                .chars()
                .filter(|c| c.is_alphabetic())
                .collect::<String>();
            (word, 1)
        })
        .filter(|(word, _)| !word.is_empty())
        .collect()
}

// 归约函数 - 合并相同键的值
fn reduce_function<K: Eq + Hash + Clone>(pairs: Vec<(K, u64)>) -> HashMap<K, u64> {
    let mut counts = HashMap::new();
    
    for (key, value) in pairs {
        *counts.entry(key).or_insert(0) += value;
    }
    
    counts
}

// 串行映射归约
fn map_reduce_serial(texts: &[&str]) -> HashMap<String, u64> {
    // 映射阶段
    let mapped: Vec<(String, u64)> = texts
        .iter()
        .flat_map(|&text| map_function(text))
        .collect();
    
    // 归约阶段
    reduce_function(mapped)
}

// 并行映射归约
fn map_reduce_parallel(texts: &[&str]) -> HashMap<String, u64> {
    // 并行映射阶段
    let mapped: Vec<(String, u64)> = texts
        .par_iter()
        .flat_map(|&text| map_function(text))
        .collect();
    
    // 并行归约阶段 - 使用分组策略
    let reduced: HashMap<String, u64> = mapped
        .par_iter()
        .fold(
            || HashMap::new(),
            |mut acc, (key, value)| {
                *acc.entry(key.clone()).or_insert(0) += value;
                acc
            },
        )
        .reduce(
            || HashMap::new(),
            |mut acc1, acc2| {
                for (key, value) in acc2 {
                    *acc1.entry(key).or_insert(0) += value;
                }
                acc1
            },
        );
    
    reduced
}

// 使用示例
fn map_reduce_example() {
    // 准备测试数据
    let texts = [
        "Rust is a systems programming language that runs blazingly fast, prevents segfaults, and guarantees thread safety.",
        "Rust is designed to be memory safe without using garbage collection.",
        "Rust is syntactically similar to C++, but provides better memory safety while maintaining high performance.",
        "Rust has been voted the most loved programming language in the Stack Overflow Developer Survey every year since 2016.",
        "Rust's ownership system guarantees memory safety and thread safety at compile time.",
        "Rust allows for zero-cost abstractions, meaning that abstractions cost nothing at runtime.",
        "Rust is used by companies like Mozilla, Dropbox, and Microsoft for performance-critical components.",
        "Rust's package manager, Cargo, makes adding dependencies straightforward and consistent.",
        "Rust has a growing ecosystem of libraries, called crates, available through crates.io.",
        "Rust combines low-level control with high-level ergonomics.",
    ];
    
    // 重复文本以创建更大的数据集
    let mut large_texts = Vec::new();
    for _ in 0..100 {
        large_texts.extend_from_slice(&texts);
    }
    let large_texts: Vec<&str> = large_texts.iter().map(|&s| s).collect();
    
    // 测量串行处理时间
    let start = Instant::now();
    let serial_result = map_reduce_serial(&large_texts);
    let serial_duration = start.elapsed();
    println!("串行映射归约耗时: {:?}", serial_duration);
    println!("串行结果中的单词数: {}", serial_result.len());
    
    // 测量并行处理时间
    let start = Instant::now();
    let parallel_result = map_reduce_parallel(&large_texts);
    let parallel_duration = start.elapsed();
    println!("并行映射归约耗时: {:?}", parallel_duration);
    println!("并行结果中的单词数: {}", parallel_result.len());
    
    // 验证结果
    assert_eq!(serial_result.len(), parallel_result.len());
    for (word, count) in &serial_result {
        assert_eq!(parallel_result.get(word), Some(count));
    }
    
    // 计算加速比
    let speedup = serial_duration.as_secs_f64() / parallel_duration.as_secs_f64();
    println!("加速比: {:.2}x", speedup);
    
    // 打印一些结果
    println!("\n常见单词统计:");
    let mut word_counts: Vec<(&String, &u64)> = parallel_result.iter().collect();
    word_counts.sort_by(|a, b| b.1.cmp(a.1));
    
    for (word, count) in word_counts.iter().take(10) {
        println!("{}: {}", word, count);
    }
}
```

### 2.3 工作窃取模式Work Stealing Pattern

```rust
// 工作窃取模式 - 动态负载均衡
use crossbeam::deque::{Injector, Stealer, Worker};
use crossbeam::utils::CachePadded;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

// 任务定义
struct Task {
    id: usize,
    work_amount: usize, // 模拟工作量
}

impl Task {
    fn new(id: usize, work_amount: usize) -> Self {
        Task { id, work_amount }
    }
    
    fn execute(&self) -> usize {
        println!("执行任务 {}, 工作量: {}", self.id, self.work_amount);
        
        // 模拟计算工作
        let mut result = 0;
        for i in 0..self.work_amount {
            result = result.wrapping_add(i);
            // 引入一些延迟以模拟真实工作
            if i % 10000 == 0 {
                thread::yield_now();
            }
        }
        
        println!("完成任务 {}", self.id);
        result
    }
}

// 工作窃取调度器
struct WorkStealingScheduler {
    global_queue: Injector<Task>,
    workers: Vec<Worker<Task>>,
    stealers: Vec<Stealer<Task>>,
    completed_tasks: Arc<AtomicUsize>,
    results: Arc<Mutex<Vec<usize>>>,
}

impl WorkStealingScheduler {
    fn new(num_workers: usize) -> Self {
        let global_queue = Injector::new();
        let mut workers = Vec::with_capacity(num_workers);
        let mut stealers = Vec::with_capacity(num_workers);
        
        // 为每个工作线程创建一个本地队列
        for _ in 0..num_workers {
            let worker = Worker::new_lifo();
            stealers.push(worker.stealer());
            workers.push(worker);
        }
        
        WorkStealingScheduler {
            global_queue,
            workers,
            stealers,
            completed_tasks: Arc::new(AtomicUsize::new(0)),
            results: Arc::new(Mutex::new(Vec::new())),
        }
    }
    
    // 提交任务到全局队列
    fn submit(&self, task: Task) {
        self.global_queue.push(task);
    }
    
    // 启动工作线程
    fn start(&self, total_tasks: usize) -> Vec<thread::JoinHandle<()>> {
        let mut handles = Vec::new();
        
        for (worker_id, worker) in self.workers.iter().enumerate() {
            let worker = worker.clone();
            let stealers = self.stealers.clone();
            let global = self.global_queue.stealer();
            let completed = Arc::clone(&self.completed_tasks);
            let results = Arc::clone(&self.results);
            
            let handle = thread::spawn(move || {
                println!("工作线程 {} 启动", worker_id);
                
                loop {
                    // 首先尝试从本地队列获取任务
                    let task = worker.pop().or_else(|| {
                        // 然后尝试从全局队列窃取
                        global.steal().success().or_else(|| {
                            // 最后尝试从其他工作线程窃取
                            stealers
                                .iter()
                                .filter(|s| !std::ptr::eq(*s, &stealers[worker_id]))
                                .map(|s| s.steal())
                                .find_map(|s| s.success())
                        })
                    });
                    
                    match task {
                        Some(task) => {
                            // 执行任务并存储结果
                            let result = task.execute();
                            results.lock().unwrap().push(result);
                            
                            // 更新完成的任务计数
                            let prev_completed = completed.fetch_add(1, Ordering::SeqCst);
                            if prev_completed + 1 >= total_tasks {
                                break;
                            }
                        }
                        None => {
                            // 没有任务可执行，检查是否所有任务都已完成
                            if completed.load(Ordering::SeqCst) >= total_tasks {
                                break;
                            }
                            
                            // 短暂休眠以避免忙等待
                            thread::sleep(Duration::from_millis(1));
                        }
                    }
                }
                
                println!("工作线程 {} 完成", worker_id);
            });
            
            handles.push(handle);
        }
        
        handles
    }
    
    // 获取结果
    fn get_results(&self) -> Vec<usize> {
        self.results.lock().unwrap().clone()
    }
}

// 使用示例
fn work_stealing_example() {
    // 创建调度器
    let num_workers = num_cpus::get();
    println!("创建 {} 个工作线程", num_workers);
    let scheduler = WorkStealingScheduler::new(num_workers);
    
    // 创建不平衡的工作负载
    let num_tasks = 20;
    println!("创建 {} 个任务", num_tasks);
    
    for i in 0..num_tasks {
        // 创建工作量不均匀的任务
        let work_amount = if i % 5 == 0 {
            10_000_000 // 大任务
        } else {
            1_000_000 // 小任务
        };
        
        scheduler.submit(Task::new(i, work_amount));
    }
    
    // 启动工作线程
    let start = Instant::now();
    let handles = scheduler.start(num_tasks);
    
    // 等待所有工作线程完成
    for handle in handles {
        handle.join().unwrap();
    }
    
    let duration = start.elapsed();
    println!("所有任务完成，耗时: {:?}", duration);
    
    // 获取结果
    let results = scheduler.get_results();
    println!("完成的任务数: {}", results.len());
    
    // 计算结果总和以验证正确性
    let sum: usize = results.iter().sum();
    println!("结果总和: {}", sum);
}
```

### 2.4 数据并行模式Data Parallelism Pattern

```rust
// 数据并行模式 - 同时处理数据的不同部分
use rayon::prelude::*;
use std::time::Instant;

// 图像处理模拟
struct Image {
    width: usize,
    height: usize,
    pixels: Vec<u8>,
}

impl Image {
    fn new(width: usize, height: usize) -> Self {
        // 创建模拟图像数据
        let pixels = vec![0; width * height * 3]; // RGB格式
        Image {
            width,
            height,
            pixels,
        }
    }
    
    // 生成测试图像
    fn generate_test_pattern(&mut self) {
        for y in 0..self.height {
            for x in 0..self.width {
                let index = (y * self.width + x) * 3;
                
                // 创建一个简单的渐变图案
                self.pixels[index] = ((x as f32 / self.width as f32) * 255.0) as u8;     // R
                self.pixels[index + 1] = ((y as f32 / self.height as f32) * 255.0) as u8; // G
                self.pixels[index + 2] = 128; // B
            }
        }
    }
    
    // 串行模糊滤镜
    fn apply_blur_filter_serial(&self) -> Image {
        let mut result = Image::new(self.width, self.height);
        let kernel_size = 5;
        let kernel_half = kernel_size / 2;
        
        for y in 0..self.height {
            for x in 0..self.width {
                let mut r_sum = 0;
                let mut g_sum = 0;
                let mut b_sum = 0;
                let mut count = 0;
                
                // 应用卷积核
                for ky in 0..kernel_size {
                    for kx in 0..kernel_size {
                        let px = x as isize + (kx as isize - kernel_half as isize);
                        let py = y as isize + (ky as isize - kernel_half as isize);
                        
                        if px >= 0 && px < self.width as isize && py >= 0 && py < self.height as isize {
                            let index = (py as usize * self.width + px as usize) * 3;
                            r_sum += self.pixels[index] as u32;
                            g_sum += self.pixels[index + 1] as u32;
                            b_sum += self.pixels[index + 2] as u32;
                            count += 1;
                        }
                    }
                }
                
                // 计算平均值
                let out_index = (y * self.width + x) * 3;
                result.pixels[out_index] = (r_sum / count) as u8;
                result.pixels[out_index + 1] = (g_sum / count) as u8;
                result.pixels[out_index + 2] = (b_sum / count) as u8;
            }
        }
        
        result
    }
    
    // 并行模糊滤镜
    fn apply_blur_filter_parallel(&self) -> Image {
        let mut result = Image::new(self.width, self.height);
        let kernel_size = 5;
        let kernel_half = kernel_size / 2;
        
        // 并行处理每一行
        result.pixels
            .par_chunks_mut(self.width * 3)
            .enumerate()
            .for_each(|(y, row)| {
                for x in 0..self.width {
                    let mut r_sum = 0;
                    let mut g_sum = 0;
                    let mut b_sum = 0;
                    let mut count = 0;
                    
                    // 应用卷积核
                    for ky in 0..kernel_size {
                        for kx in 0..kernel_size {
                            let px = x as isize + (kx as isize - kernel_half as isize);
                            let py = y as isize + (ky as isize - kernel_half as isize);
                            
                            if px >= 0 && px < self.width as isize && py >= 0 && py < self.height as isize {
                                let index = (py as usize * self.width + px as usize) * 3;
                                r_sum += self.pixels[index] as u32;
                                g_sum += self.pixels[index + 1] as u32;
                                b_sum += self.pixels[index + 2] as u32;
                                count += 1;
                            }
                        }
                    }
                    
                    // 计算平均值
                    let out_index = x * 3;
                    row[out_index] = (r_sum / count) as u8;
                    row[out_index + 1] = (g_sum / count) as u8;
                    row[out_index + 2] = (b_sum / count) as u8;
                }
            });
        
        result
    }
    
    // 计算两个图像的差异以验证结果
    fn calculate_difference(&self, other: &Image) -> f64 {
        if self.width != other.width || self.height != other.height {
            return f64::MAX;
        }
        
        let mut total_diff = 0.0;
        
        for i in 0..self.pixels.len() {
            let diff = (self.pixels[i] as i32 - other.pixels[i] as i32).abs() as f64;
            total_diff += diff;
        }
        
        total_diff / (self.width * self.height * 3) as f64
    }
}

// 使用示例
fn data_parallelism_example() {
    // 创建大型测试图像
    let width = 2048;
    let height = 2048;
    println!("创建 {}x{} 测试图像", width, height);
    
    let mut image = Image::new(width, height);
    image.generate_test_pattern();
    
    // 应用串行滤镜
    println!("应用串行模糊滤镜...");
    let start = Instant::now();
    let blurred_serial = image.apply_blur_filter_serial();
    let serial_duration = start.elapsed();
    println!("串行处理耗时: {:?}", serial_duration);
    
    // 应用并行滤镜
    println!("应用并行模糊滤镜...");
    let start = Instant::now();
    let blurred_parallel = image.apply_blur_filter_parallel();
    let parallel_duration = start.elapsed();
    println!("并行处理耗时: {:?}", parallel_duration);
    
    // 验证结果
    let diff = blurred_serial.calculate_difference(&blurred_parallel);
    println!("结果差异 (平均每像素): {:.6}", diff);
    
    // 计算加速比
    let speedup = serial_duration.as_secs_f64() / parallel_duration.as_secs_f64();
    println!("加速比: {:.2}x", speedup);
}
```

### 2.5 管道并行模式Pipeline Parallelism Pattern

```rust
// 管道并行模式 - 流水线处理
use crossbeam::channel::{bounded, unbounded};
use std::thread;
use std::time::{Duration, Instant};

// 数据项定义
struct DataItem {
    id: usize,
    value: String,
    // 可以包含更多字段
}

// 管道阶段特征
trait PipelineStage<I, O> {
    fn process(&self, input: I) -> O;
    fn name(&self) -> &str;
}

// 第一阶段：数据生成
struct DataGenerator {
    count: usize,
}

impl DataGenerator {
    fn new(count: usize) -> Self {
        DataGenerator { count }
    }
    
    fn generate(&self) -> Vec<usize> {
        (0..self.count).collect()
    }
}

// 第二阶段：数据转换
struct DataTransformer;

impl PipelineStage<usize, DataItem> for DataTransformer {
    fn process(&self, input: usize) -> DataItem {
        // 模拟处理时间
        thread::sleep(Duration::from_millis(5));
        
        DataItem {
            id: input,
            value: format!("Item-{}", input),
        }
    }
    
    fn name(&self) -> &str {
        "转换器"
    }
}

// 第三阶段：数据验证
struct DataValidator;

impl PipelineStage<DataItem, Result<DataItem, String>> for DataValidator {
    fn process(&self, input: DataItem) -> Result<DataItem, String> {
        // 模拟处理时间
        thread::sleep(Duration::from_millis(3));
        
        // 模拟验证逻辑
        if input.id % 10 == 0 {
            Err(format!("验证失败: {}", input.id))
        } else {
            Ok(input)
        }
    }
    
    fn name(&self) -> &str {
        "验证器"
    }
}

// 第四阶段：数据处理
struct DataProcessor;

impl PipelineStage<Result<DataItem, String>, Option<String>> for DataProcessor {
    fn process(&self, input: Result<DataItem, String>) -> Option<String> {
        // 模拟处理时间
        thread::sleep(Duration::from_millis(8));
        
        match input {
            Ok(item) => {
                // 处理有效数据
                Some(format!("处理成功: {} - {}", item.id, item.value))
            }
            Err(error) => {
                // 记录错误
                println!("错误: {}", error);
                None
            }
        }
    }
    
    fn name(&self) -> &str {
        "处理器"
    }
}

// 串行管道
fn run_pipeline_serial(count: usize) -> Vec<Option<String>> {
    let generator = DataGenerator::new(count);
    let transformer = DataTransformer;
    let validator = DataValidator;
    let processor = DataProcessor;
    
    let mut results = Vec::new();
    
    // 串行执行所有阶段
    for id in generator.generate() {
        let item = transformer.process(id);
        let validated = validator.process(item);
        let result = processor.process(validated);
        results.push(result);
    }
    
    results
}

// 并行管道
fn run_pipeline_parallel(count: usize, buffer_size: usize) -> Vec<Option<String>> {
    let generator = DataGenerator::new(count);
    let transformer = DataTransformer;
    let validator = DataValidator;
    let processor = DataProcessor;
    
    // 创建有界通道连接各阶段
    let (tx1, rx1) = bounded(buffer_size);  // 生成器 -> 转换器
    let (tx2, rx2) = bounded(buffer_size);  // 转换器 -> 验证器
    let (tx3, rx3) = bounded(buffer_size);  // 验证器 -> 处理器
    let (tx_result, rx_result) = unbounded(); // 处理器 -> 结果收集
    
    // 阶段1：生成数据
    let generator_handle = thread::spawn(move || {
        println!("生成器: 开始");
        for id in generator.generate() {
            if tx1.send(id).is_err() {
                break;
            }
        }
        println!("生成器: 完成");
    });
    
    // 阶段2：转换数据
    let transformer_handle = thread::spawn(move || {
        println!("{}: 开始", transformer.name());
        while let Ok(id) = rx1.recv() {
            let item = transformer.process(id);
            if tx2.send(item).is_err() {
                break;
            }
        }
        println!("{}: 完成", transformer.name());
    });
    
    // 阶段3：验证数据
    let validator_handle = thread::spawn(move || {
        println!("{}: 开始", validator.name());
        while let Ok(item) = rx2.recv() {
            let validated = validator.process(item);
            if tx3.send(validated).is_err() {
                break;
            }
        }
        println!("{}: 完成", validator.name());
    });
    
    // 阶段4：处理数据
    let processor_handle = thread::spawn(move || {
        println!("{}: 开始", processor.name());
        while let Ok(validated) = rx3.recv() {
            let result = processor.process(validated);
            if tx_result.send(result).is_err() {
                break;
            }
        }
        println!("{}: 完成", processor.name());
    });
    
    // 收集结果
    let collector_handle = thread::spawn(move || {
        let mut results = Vec::with_capacity(count);
        
        for _ in 0..count {
            match rx_result.recv() {
                Ok(result) => results.push(result),
                Err(_) => break,
            }
        }
        
        results
    });
    
    // 等待所有线程完成
    generator_handle.join().unwrap();
    transformer_handle.join().unwrap();
    validator_handle.join().unwrap();
    processor_handle.join().unwrap();
    
    // 获取结果
    collector_handle.join().unwrap()
}

// 使用示例
fn pipeline_parallelism_example() {
    let item_count = 100;
    println!("处理 {} 个数据项", item_count);
    
    // 运行串行管道
    println!("\n运行串行管道...");
    let start = Instant::now();
    let serial_results = run_pipeline_serial(item_count);
    let serial_duration = start.elapsed();
    println!("串行管道耗时: {:?}", serial_duration);
    println!("串行管道成功处理: {}", serial_results.iter().filter(|r| r.is_some()).count());
    
    // 运行并行管道
    println!("\n运行并行管道...");
    let start = Instant::now();
    let parallel_results = run_pipeline_parallel(item_count, 10);
    let parallel_duration = start.elapsed();
    println!("并行管道耗时: {:?}", parallel_duration);
    println!("并行管道成功处理: {}", parallel_results.iter().filter(|r| r.is_some()).count());
    
    // 验证结果数量
    assert_eq!(serial_results.len(), parallel_results.len());
    
    // 计算加速比
    let speedup = serial_duration.as_secs_f64() / parallel_duration.as_secs_f64();
    println!("加速比: {:.2}x", speedup);
    
    // 理论最大加速比
    let theoretical_max = 4.0; // 4个阶段
    println!("理论最大加速比: {:.2}x", theoretical_max);
    println!("效率: {:.2}%", (speedup / theoretical_max) * 100.0);
}
```

## 3 三、Rust 2024 分布式设计模式

### 3.1 主从模式Master-Worker Pattern

```rust
// 主从模式 - 中央协调器分发任务
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

// 任务定义
#[derive(Clone, Debug, Serialize, Deserialize)]
struct Task {
    id: usize,
    data: Vec<u32>,
}

// 结果定义
#[derive(Clone, Debug, Serialize, Deserialize)]
struct TaskResult {
    task_id: usize,
    result: u64,
    worker_id: usize,
}

// 工作者状态
#[derive(Clone, Copy, Debug, PartialEq)]
enum WorkerStatus {
    Idle,
    Busy,
    Failed,
}

// 工作者信息
struct WorkerInfo {
    id: usize,
    status: WorkerStatus,
    tasks_completed: usize,
}

// 主节点
struct Master {
    workers: Arc<Mutex<HashMap<usize, WorkerInfo>>>,
    pending_tasks: Arc<Mutex<Vec<Task>>>,
    in_progress_tasks: Arc<Mutex<HashMap<usize, Task>>>,
    completed_results: Arc<Mutex<Vec<TaskResult>>>,
    next_worker_id: Arc<Mutex<usize>>,
}

impl Master {
    fn new() -> Self {
        Master {
            workers: Arc::new(Mutex::new(HashMap::new())),
            pending_tasks: Arc::new(Mutex::new(Vec::new())),
            in_progress_tasks: Arc::new(Mutex::new(HashMap::new())),
            completed_results: Arc::new(Mutex::new(Vec::new())),
            next_worker_id: Arc::new(Mutex::new(0)),
        }
    }
    
    // 添加任务
    fn add_task(&self, task: Task) {
        println!("主节点: 添加任务 {}", task.id);
        self.pending_tasks.lock().unwrap().push(task);
    }
    
    // 注册新工作者
    fn register_worker(&self) -> usize {
        let mut next_id = self.next_worker_id.lock().unwrap();
        let worker_id = *next_id;
        *next_id += 1;
        
        let mut workers = self.workers.lock().unwrap();
        workers.insert(
            worker_id,
            WorkerInfo {
                id: worker_id,
                status: WorkerStatus::Idle,
                tasks_completed: 0,
            },
        );
        
        println!("主节点: 注册工作者 {}", worker_id);
        worker_id
    }
    
    // 获取任务
    fn get_task(&self, worker_id: usize) -> Option<Task> {
        // 更新工作者状态
        let mut workers = self.workers.lock().unwrap();
        if let Some(worker) = workers.get_mut(&worker_id) {
            if worker.status == WorkerStatus::Failed {
                return None;
            }
            worker.status = WorkerStatus::Busy;
        } else {
            return None;
        }
        
        // 获取待处理任务
        let mut pending = self.pending_tasks.lock().unwrap();
        if pending.is_empty() {
            // 没有待处理任务，将工作者设为空闲
            if let Some(worker) = workers.get_mut(&worker_id) {
                worker.status = WorkerStatus::Idle;
            }
            return None;
        }
        
        let task = pending.remove(0);
        println!("主节点: 分配任务 {} 给工作者 {}", task.id, worker_id);
        
        // 将任务标记为进行中
        let mut in_progress = self.in_progress_tasks.lock().unwrap();
        in_progress.insert(task.id, task.clone());
        
        Some(task)
    }
    
    // 提交结果
    fn submit_result(&self, result: TaskResult) {
        println!(
            "主节点: 接收到任务 {} 的结果，来自工作者 {}",
            result.task_id, result.worker_id
        );
        
        // 更新工作者状态
        let mut workers = self.workers.lock().unwrap();
        if let Some(worker) = workers.get_mut(&result.worker_id) {
            worker.status = WorkerStatus::Idle;
            worker.tasks_completed += 1;
        }
        
        // 从进行中任务列表中移除
        let mut in_progress = self.in_progress_tasks.lock().unwrap();
        in_progress.remove(&result.task_id);
        
        // 添加到完成结果
        self.completed_results.lock().unwrap().push(result);
    }
    
    // 标记工作者失败
    fn mark_worker_failed(&self, worker_id: usize) {
        println!("主节点: 标记工作者 {} 为失败", worker_id);
        
        let mut workers = self.workers.lock().unwrap();
        if let Some(worker) = workers.get_mut(&worker_id) {
            worker.status = WorkerStatus::Failed;
        }
        
        // 重新分配该工作者正在处理的任务
        let mut in_progress = self.in_progress_tasks.lock().unwrap();
        let mut pending = self.pending_tasks.lock().unwrap();
        
        // 找出该工作者正在处理的任务
        let worker_tasks: Vec<Task> = in_progress
            .iter()
            .filter_map(|(_, task)| {
                // 这里我们没有任务-工作者映射，所以简化处理
                // 在实际系统中，应该维护任务-工作者映射
                Some(task.clone())
            })
            .collect();
        
        // 将这些任务重新添加到待处理队列
        for task in worker_tasks {
            println!("主节点: 重新分配任务 {}", task.id);
            pending.push(task.clone());
            in_progress.remove(&task.id);
        }
    }
    
    // 获取所有结果
    fn get_results(&self) -> Vec<TaskResult> {
        self.completed_results.lock().unwrap().clone()
    }
    
    // 获取工作者统计信息
    fn get_worker_stats(&self) -> HashMap<usize, (WorkerStatus, usize)> {
        let workers = self.workers.lock().unwrap();
        workers
            .iter()
            .map(|(&id, info)| (id, (info.status, info.tasks_completed)))
            .collect()
    }
    
    // 检查是否所有任务都已完成
    fn all_tasks_completed(&self) -> bool {
        let pending = self.pending_tasks.lock().unwrap();
        let in_progress = self.in_progress_tasks.lock().unwrap();
        
        pending.is_empty() && in_progress.is_empty()
    }
}

// 工作者节点
struct Worker {
    id: usize,
    master: Arc<Master>,
}

impl Worker {
    fn new(id: usize, master: Arc<Master>) -> Self {
        Worker { id, master }
    }
    
    // 工作循环
    fn run(&self) {
        println!("工作者 {}: 开始运行", self.id);
        
        loop {
            // 获取任务
            match self.master.get_task(self.id) {
                Some(task) => {
                    println!("工作者 {}: 处理任务 {}", self.id, task.id);
                    
                    // 模拟处理
                    thread::sleep(Duration::from_millis(50 + (task.id % 5) * 20));
                    
                    // 计算结果
                    let result: u64 = task.data.iter().map(|&x| x as u64).sum();
                    
                    // 模拟随机失败
                    if task.id % 17 == 0 && self.id % 3 == 0 {
                        println!("工作者 {}: 处理任务 {} 时失败", self.id, task.id);
                        continue;
                    }
                    
                    // 提交结果
                    let task_result = TaskResult {
                        task_id: task.id,
                        result,
                        worker_id: self.id,
                    };
                    
                    self.master.submit_result(task_result);
                }
                None => {
                    // 没有任务，休眠一段时间
                    thread::sleep(Duration::from_millis(10));
                    
                    // 检查是否所有任务都已完成
                    if self.master.all_tasks_completed() {
                        break;
                    }
                }
            }
        }
        
        println!("工作者 {}: 完成运行", self.id);
    }
}

// 使用示例
fn master_worker_example() {
    // 创建主节点
    let master = Arc::new(Master::new());
    
    // 创建任务
    let task_count = 50;
    for i in 0..task_count {
        // 创建随机数据
        let data: Vec<u32> = (0..100).map(|x| x + i as u32).collect();
        
        let task = Task {
            id: i,
            data,
        };
        
        master.add_task(task);
    }
    
    // 创建工作者
    let worker_count = 5;
    let mut worker_handles = Vec::new();
    
    for _ in 0..worker_count {
        let worker_id = master.register_worker();
        let worker = Worker::new(worker_id, Arc::clone(&master));
        
        let handle = thread::spawn(move || {
            worker.run();
        });
        
        worker_handles.push(handle);
    }
    
    // 等待所有工作者完成
    for handle in worker_handles {
        handle.join().unwrap();
    }
    
    // 获取结果
    let results = master.get_results();
    println!("完成的任务数: {}/{}", results.len(), task_count);
    
    // 获取工作者统计信息
    let worker_stats = master.get_worker_stats();
    println!("\n工作者统计:");
    for (id, (status, completed)) in worker_stats {
        println!(
            "工作者 {}: 状态 = {:?}, 完成任务数 = {}",
            id, status, completed
        );
    }
}
```

### 3.2 发布-订阅模式Publish-Subscribe Pattern

```rust
// 发布-订阅模式 - 消息传递系统
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

// 消息定义
#[derive(Clone, Debug)]
struct Message {
    topic: String,
    id: usize,
    content: String,
    timestamp: Instant,
}

impl Message {
    fn new(topic: impl Into<String>, id: usize, content: impl Into<String>) -> Self {
        Message {
            topic: topic.into(),
            id,
            content: content.into(),
            timestamp: Instant::now(),
        }
    }
}

// 订阅者特征
trait Subscriber: Send + Sync {
    fn id(&self) -> usize;
    fn receive(&self, message: Message);
}

// 具体订阅者
struct ConcreteSubscriber {
    id: usize,
    name: String,
    received_messages: Arc<Mutex<Vec<Message>>>,
}

impl ConcreteSubscriber {
    fn new(id: usize, name: impl Into<String>) -> Self {
        ConcreteSubscriber {
            id,
            name: name.into(),
            received_messages: Arc::new(Mutex::new(Vec::new())),
        }
    }
    
    fn get_received_messages(&self) -> Vec<Message> {
        self.received_messages.lock().unwrap().clone()
    }
}

impl Subscriber for ConcreteSubscriber {
    fn id(&self) -> usize {
        self.id
    }
    
    fn receive(&self, message: Message) {
        println!(
            "订阅者 {} ({}): 收到消息 {} 从主题 '{}'",
            self.id, self.name, message.id, message.topic
        );
        
        self.received_messages.lock().unwrap().push(message);
    }
}

// 消息代理
struct MessageBroker {
    topics: Arc<Mutex<HashMap<String, HashSet<usize>>>>,
    subscribers: Arc<Mutex<HashMap<usize, Arc<dyn Subscriber>>>>,
    message_queue: Arc<Mutex<Vec<Message>>>,
}

impl MessageBroker {
    fn new() -> Self {
        MessageBroker {
            topics: Arc::new(Mutex::new(HashMap::new())),
            subscribers: Arc::new(Mutex::new(HashMap::new())),
            message_queue: Arc::new(Mutex::new(Vec::new())),
        }
    }
    
    // 注册订阅者
    fn register_subscriber(&self, subscriber: Arc<dyn Subscriber>) {
        let id = subscriber.id();
        println!("代理: 注册订阅者 {}", id);
        
        let mut subscribers = self.subscribers.lock().unwrap();
        subscribers.insert(id, subscriber);
    }
    
    // 订阅主题
    fn subscribe(&self, subscriber_id: usize, topic: impl Into<String>) -> Result<(), String> {
        let topic = topic.into();
        println!("代理: 订阅者 {} 订阅主题 '{}'", subscriber_id, topic);
        
        // 检查订阅者是否存在
        let subscribers = self.subscribers.lock().unwrap();
        if !subscribers.contains_key(&subscriber_id) {
            return Err(format!("订阅者 {} 不存在", subscriber_id));
        }
        
        // 添加到主题订阅列表
        let mut topics = self.topics.lock().unwrap();
        topics
            .entry(topic)
            .or_insert_with(HashSet::new)
            .insert(subscriber_id);
        
        Ok(())
    }
    
    // 取消订阅
    fn unsubscribe(&self, subscriber_id: usize, topic: impl Into<String>) -> Result<(), String> {
        let topic = topic.into();
        println!("代理: 订阅者 {} 取消订阅主题 '{}'", subscriber_id, topic);
        
        let mut topics = self.topics.lock().unwrap();
        if let Some(subscribers) = topics.get_mut(&topic) {
            subscribers.remove(&subscriber_id);
            
            // 如果主题没有订阅者，可以选择删除主题
            if subscribers.is_empty() {
                topics.remove(&topic);
            }
            
            Ok(())
        } else {
            Err(format!("主题 '{}' 不存在", topic))
        }
    }
    
    // 发布消息
    fn publish(&self, message: Message) {
        println!(
            "代理: 发布消息 {} 到主题 '{}'",
            message.id, message.topic
        );
        
        // 将消息添加到队列
        self.message_queue.lock().unwrap().push(message);
    }
    
    // 分发消息
    fn dispatch_messages(&self) -> usize {
        // 获取并清空消息队列
        let messages = {
            let mut queue = self.message_queue.lock().unwrap();
            std::mem::take(&mut *queue)
        };
        
        if messages.is_empty() {
            return 0;
        }
        
        let mut dispatch_count = 0;
        
        // 获取主题和订阅者映射
        let topics = self.topics.lock().unwrap();
        let subscribers = self.subscribers.lock().unwrap();
        
        // 分发每条消息
        for message in messages {
            if let Some(topic_subscribers) = topics.get(&message.topic) {
                for &subscriber_id in topic_subscribers {
                    if let Some(subscriber) = subscribers.get(&subscriber_id) {
                        subscriber.receive(message.clone());
                        dispatch_count += 1;
                    }
                }
            }
        }
        
        dispatch_count
    }
    
    // 启动分发线程
    fn start_dispatcher(&self, interval_ms: u64) -> thread::JoinHandle<()> {
        let broker = Arc::new(self.clone());
        
        thread::spawn(move || {
            println!("分发线程: 开始运行");
            
            loop {
                // 分发消息
                let count = broker.dispatch_messages();
                if count > 0 {
                    println!("分发线程: 分发了 {} 条消息", count);
                }
                
                // 休眠一段时间
                thread::sleep(Duration::from_millis(interval_ms));
            }
        })
    }
}

impl Clone for MessageBroker {
    fn clone(&self) -> Self {
        MessageBroker {
            topics: Arc::clone(&self.topics),
            subscribers: Arc::clone(&self.subscribers),
            message_queue: Arc::clone(&self.message_queue),
        }
    }
}

// 使用示例
fn publish_subscribe_example() {
    // 创建消息代理
    let broker = MessageBroker::new();
    
    // 创建订阅者
    let subscriber1 = Arc::new(ConcreteSubscriber::new(1, "用户1"));
    let subscriber2 = Arc::new(ConcreteSubscriber::new(2, "用户2"));
    let subscriber3 = Arc::new(ConcreteSubscriber::new(3, "用户3"));
    
    // 注册订阅者
    broker.register_subscriber(subscriber1.clone() as Arc<dyn Subscriber>);
    broker.register_subscriber(subscriber2.clone() as Arc<dyn Subscriber>);
    broker.register_subscriber(subscriber3.clone() as Arc<dyn Subscriber>);
    
    // 订阅主题
    broker.subscribe(1, "新闻").unwrap();
    broker.subscribe(1, "体育").unwrap();
    broker.subscribe(2, "新闻").unwrap();
    broker.subscribe(2, "科技").unwrap();
    broker.subscribe(3, "体育").unwrap();
    broker.subscribe(3, "科技").unwrap();
    
    // 启动分发线程
    let _dispatcher = broker.start_dispatcher(100);
    
    // 发布消息
    broker.publish(Message::new("新闻", 1, "今日头条新闻"));
    broker.publish(Message::new("体育", 2, "体育赛事更新"));
    broker.publish(Message::new("科技", 3, "最新科技动态"));
    
    // 等待消息分发
    thread::sleep(Duration::from_millis(200));
    
    // 取消订阅
    broker.unsubscribe(1, "新闻").unwrap();
    
    // 再次发布消息
    broker.publish(Message::new("新闻", 4, "下午新闻更新"));
    broker.publish(Message::new("体育", 5, "赛事结果公布"));
    
    // 等待消息分发
    thread::sleep(Duration::from_millis(200));
    
    // 检查接收到的消息
    println!("\n订阅者接收到的消息:");
    println!("订阅者1: {} 条消息", subscriber1.get_received_messages().len());
    println!("订阅者2: {} 条消息", subscriber2.get_received_messages().len());
    println!("订阅者3: {} 条消息", subscriber3.get_received_messages().len());
    
    // 详细输出每个订阅者接收到的消息
    for (i, subscriber) in [&subscriber1, &subscriber2, &subscriber3].iter().enumerate() {
        println!("\n订阅者{}接收到的消息:", i + 1);
        for msg in subscriber.get_received_messages() {
            println!(
                "  主题: {}, ID: {}, 内容: {}",
                msg.topic, msg.id, msg.content
            );
        }
    }
}
```

### 3.3 远程过程调用模式RPC Pattern

```rust
// 远程过程调用模式 - 模拟RPC系统
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

// RPC请求
#[derive(Clone, Debug, Serialize, Deserialize)]
struct RpcRequest {
    id: usize,
    method: String,
    params: Vec<String>,
}

// RPC响应
#[derive(Clone, Debug, Serialize, Deserialize)]
struct RpcResponse {
    id: usize,
    result: Result<String, String>,
}

// RPC服务器
struct RpcServer {
    handlers: HashMap<String, Box<dyn Fn(Vec<String>) -> Result<String, String> + Send + Sync>>,
}

impl RpcServer {
    fn new() -> Self {
        RpcServer {
            handlers: HashMap::new(),
        }
    }
    
    // 注册处理函数
    fn register<F>(&mut self, method: impl Into<String>, handler: F)
    where
        F: Fn(Vec<String>) -> Result<String, String> + Send + Sync + 'static,
    {
        let method = method.into();
        println!("RPC服务器: 注册方法 '{}'", method);
        self.handlers.insert(method, Box::new(handler));
    }
    
    // 处理请求
    fn handle_request(&self, request: RpcRequest) -> RpcResponse {
        println!(
            "RPC服务器: 处理请求 {} 方法 '{}'",
            request.id, request.method
        );
        
        let result = match self.handlers.get(&request.method) {
            Some(handler) => {
                // 模拟处理延迟
                thread::sleep(Duration::from_millis(50));
                handler(request.params.clone())
            }
            None => Err(format!("未知方法: {}", request.method)),
        };
        
        RpcResponse {
            id: request.id,
            result,
        }
    }
}

// RPC客户端
struct RpcClient {
    server: Arc<RpcServer>,
    next_id: Mutex<usize>,
}

impl RpcClient {
    fn new(server: Arc<RpcServer>) -> Self {
        RpcClient {
            server,
            next_id: Mutex::new(0),
        }
    }
    
    // 发送RPC请求
    fn call(&self, method: impl Into<String>, params: Vec<String>) -> Result<String, String> {
        let method = method.into();
        
        // 生成请求ID
        let id = {
            let mut next_id = self.next_id.lock().unwrap();
            let id = *next_id;
            *next_id += 1;
            id
        };
        
        println!("RPC客户端: 调用方法 '{}' (ID: {})", method, id);
        
        // 创建请求
        let request = RpcRequest {
            id,
            method,
            params,
        };
        
        // 发送请求并等待响应
        let response = self.server.handle_request(request);
        
        // 处理响应
        response.result
    }
    
    // 异步调用
    fn call_async(
        &self,
        method: impl Into<String> + Send + 'static,
        params: Vec<String>,
    ) -> thread::JoinHandle<Result<String, String>> {
        let server = Arc::clone(&self.server);
        let method = method.into();
        
        // 生成请求ID
        let id = {
            let mut next_id = self.next_id.lock().unwrap();
            let id = *next_id;
            *next_id += 1;
            id
        };
        
        println!("RPC客户端: 异步调用方法 '{}' (ID: {})", method, id);
        
        thread::spawn(move || {
            // 创建请求
            let request = RpcRequest {
                id,
                method,
                params,
            };
            
            // 发送请求并等待响应
            let response = server.handle_request(request);
            
            // 处理响应
            response.result
        })
    }
}

// 使用示例
fn rpc_pattern_example() {
    // 创建RPC服务器
    let mut server = RpcServer::new();
    
    // 注册处理函数
    server.register("add", |params| {
        if params.len() != 2 {
            return Err("add方法需要两个参数".to_string());
        }
        
        let a = params[0].parse::<i32>().map_err(|e| e.to_string())?;
        let b = params[1].parse::<i32>().map_err(|e| e.to_string())?;
        
        Ok((a + b).to_string())
    });
    
    server.register("echo", |params| {
        if params.is_empty() {
            return Err("echo方法需要至少一个参数".to_string());
        }
        
        Ok(params.join(" "))
    });
    
    server.register("uppercase", |params| {
        if params.is_empty() {
            return Err("uppercase方法需要至少一个参数".to_string());
        }
        
        Ok(params.join(" ").to_uppercase())
    });
    
    // 创建RPC客户端
    let server_arc = Arc::new(server);
    let client = RpcClient::new(Arc::clone(&server_arc));
    
    // 同步调用
    match client.call("add", vec!["5".to_string(), "3".to_string()]) {
        Ok(result) => println!("同步调用 add 结果: {}", result),
        Err(e) => println!("同步调用 add 错误: {}", e),
    }
    
    match client.call("echo", vec!["Hello".to_string(), "World".to_string()]) {
        Ok(result) => println!("同步调用 echo 结果: {}", result),
        Err(e) => println!("同步调用 echo 错误: {}", e),
    }
    
    // 错误调用
    match client.call("unknown", vec!["test".to_string()]) {
        Ok(result) => println!("同步调用 unknown 结果: {}", result),
        Err(e) => println!("同步调用 unknown 错误: {}", e),
    }
    
    // 异步调用
    let handles = vec![
        client.call_async("add", vec!["10".to_string(), "20".to_string()]),
        client.call_async("uppercase", vec!["hello".to_string(), "rust".to_string()]),
        client.call_async("echo", vec!["async".to_string(), "call".to_string()]),
    ];
    
    // 等待所有异步调用完成
    for (i, handle) in handles.into_iter().enumerate() {
        match handle.join().unwrap() {
            Ok(result) => println!("异步调用 {} 结果: {}", i, result),
            Err(e) => println!("异步调用 {} 错误: {}", i, e),
        }
    }
}
```

### 3.4 分布式锁模式Distributed Lock Pattern

```rust
// 分布式锁模式 - 模拟分布式锁
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

// 锁管理器
struct LockManager {
    locks: Mutex<HashMap<String, LockInfo>>,
}

// 锁信息
struct LockInfo {
    owner: String,
    acquired_at: Instant,
    ttl: Duration,
}

// 锁结果
enum LockResult {
    Acquired,
    AlreadyLocked(String),
}

// 解锁结果
enum UnlockResult {
    Released,
    NotOwner,
    NotLocked,
}

impl LockManager {
    fn new() -> Self {
        LockManager {
            locks: Mutex::new(HashMap::new()),
        }
    }
    
    // 尝试获取锁
    fn try_lock(
        &self,
        resource: impl Into<String>,
        owner: impl Into<String>,
        ttl: Duration,
    ) -> LockResult {
        let resource = resource.into();
        let owner = owner.into();
        
        let mut locks = self.locks.lock().unwrap();
        
        // 检查资源是否已被锁定
        if let Some(lock_info) = locks.get(&resource) {
            // 检查锁是否过期
            if lock_info.acquired_at.elapsed() > lock_info.ttl {
                // 锁已过期，可以获取
                println!(
                    "锁管理器: 资源 '{}' 的锁已过期 (原所有者: {})",
                    resource, lock_info.owner
                );
            } else {
                // 锁仍然有效
                return LockResult::AlreadyLocked(lock_info.owner.clone());
            }
        }
        
        // 获取锁
        locks.insert(
            resource.clone(),
            LockInfo {
                owner: owner.clone(),
                acquired_at: Instant::now(),
                ttl,
            },
        );
        
        println!("锁管理器: 资源 '{}' 被 '{}' 锁定", resource, owner);
        LockResult::Acquired
    }
    
    // 解锁资源
    fn unlock(
        &self,
        resource: impl Into<String>,
        owner: impl Into<String>,
    ) -> UnlockResult {
        let resource = resource.into();
        let owner = owner.into();
        
        let mut locks = self.locks.lock().unwrap();
        
        // 检查资源是否已被锁定
        if let Some(lock_info) = locks.get(&resource) {
            // 检查是否是锁的所有者
            if lock_info.owner != owner {
                println!(
                    "锁管理器: 资源 '{}' 解锁失败，'{}' 不是所有者 (所有者是 '{}')",
                    resource, owner, lock_info.owner
                );
                return UnlockResult::NotOwner;
            }
            
            // 移除锁
            locks.remove(&resource);
            println!("锁管理器: 资源 '{}' 被 '{}' 解锁", resource, owner);
            UnlockResult::Released
        } else {
            println!("锁管理器: 资源 '{}' 未被锁定", resource);
            UnlockResult::NotLocked
        }
    }
    
    // 检查锁状态
    fn check_lock(&self, resource: impl Into<String>) -> Option<(String, Duration)> {
        let resource = resource.into();
        let locks = self.locks.lock().unwrap();
        
        locks.get(&resource).map(|lock_info| {
            let remaining = lock_info
                .ttl
                .checked_sub(lock_info.acquired_at.elapsed())
                .unwrap_or(Duration::from_secs(0));
            
            (lock_info.owner.clone(), remaining)
        })
    }
    
    // 清理过期的锁
    fn cleanup_expired_locks(&self) -> usize {
        let mut locks = self.locks.lock().unwrap();
        let before_count = locks.len();
        
        // 找出过期的锁
        let expired_resources: Vec<String> = locks
            .iter()
            .filter(|(_, lock_info)| lock_info.acquired_at.elapsed() > lock_info.ttl)
            .map(|(resource, _)| resource.clone())
            .collect();
        
        // 移除过期的锁
        for resource in &expired_resources {
            locks.remove(resource);
            println!("锁管理器: 清理过期的锁 '{}'", resource);
        }
        
        expired_resources.len()
    }
}

// 分布式锁客户端
struct DistributedLockClient {
    id: String,
    lock_manager: Arc<LockManager>,
}

impl DistributedLockClient {
    fn new(id: impl Into<String>, lock_manager: Arc<LockManager>) -> Self {
        DistributedLockClient {
            id: id.into(),
            lock_manager,
        }
    }
    
    // 尝试获取锁
    fn try_lock(&self, resource: impl Into<String>, ttl: Duration) -> bool {
        let resource = resource.into();
        
        match self.lock_manager.try_lock(&resource, &self.id, ttl) {
            LockResult::Acquired => {
                println!("客户端 {}: 获取资源 '{}' 的锁", self.id, resource);
                true
            }
            LockResult::AlreadyLocked(owner) => {
                println!(
                    "客户端 {}: 无法获取资源 '{}' 的锁 (已被 '{}' 锁定)",
                    self.id, resource, owner
                );
                false
            }
        }
    }
    
    // 解锁资源
    fn unlock(&self, resource: impl Into<String>) -> bool {
        let resource = resource.into();
        
        match self.lock_manager.unlock(&resource, &self.id) {
            UnlockResult::Released => {
                println!("客户端 {}: 释放资源 '{}' 的锁", self.id, resource);
                true
            }
            UnlockResult::NotOwner => {
                println!(
                    "客户端 {}: 无法释放资源 '{}' 的锁 (不是所有者)",
                    self.id, resource
                );
                false
            }
            UnlockResult::NotLocked => {
                println!("客户端 {}: 资源 '{}' 未被锁定", self.id, resource);
                false
            }
        }
    }
    
    // 带重试的锁获取
    fn lock_with_retry(
        &self,
        resource: impl Into<String> + Clone,
        ttl: Duration,
        max_retries: usize,
        retry_delay: Duration,
    ) -> bool {
        let resource = resource.into();
        
        for attempt in 0..=max_retries {
            if attempt > 0 {
                println!(
                    "客户端 {}: 重试获取资源 '{}' 的锁 (尝试 {}/{})",
                    self.id, resource, attempt, max_retries
                );
                thread::sleep(retry_delay);
            }
            
            if self.try_lock(&resource, ttl) {
                return true;
            }
        }
        
        println!(
            "客户端 {}: 在 {} 次尝试后无法获取资源 '{}' 的锁",
            self.id, max_retries, resource
        );
        false
    }
}

// 使用示例
fn distributed_lock_example() {
    // 创建锁管理器
    let lock_manager = Arc::new(LockManager::new());
    
    // 创建客户端
    let client1 = DistributedLockClient::new("Client1", Arc::clone(&lock_manager));
    let client2 = DistributedLockClient::new("Client2", Arc::clone(&lock_manager));
    let client3 = DistributedLockClient::new("Client3", Arc::clone(&lock_manager));
    
    // 资源名称
    let resource1 = "database";
    let resource2 = "file";
    
    // 客户端1获取锁
    if client1.try_lock(resource1, Duration::from_secs(5)) {
        println!("客户端1成功获取资源1的锁");
        
        // 客户端2尝试获取同一资源的锁（应该失败）
        if !client2.try_lock(resource1, Duration::from_secs(5)) {
            println!("客户端2无法获取资源1的锁（预期行为）");
        }
        
        // 客户端2获取不同资源的锁
        if client2.try_lock(resource2, Duration::from_secs(5)) {
            println!("客户端2成功获取资源2的锁");
            
            // 模拟工作
            thread::sleep(Duration::from_millis(100));
            
            // 客户端2释放锁
            client2.unlock(resource2);
        }
        
        // 模拟工作
        thread::sleep(Duration::from_millis(200));
        
        // 客户端1释放锁
        client1.unlock(resource1);
    }
    
    // 客户端3使用重试机制获取锁
    let client1_clone = client1.clone();
    let resource1_clone = resource1.to_string();
    
    // 在单独的线程中让客户端1获取锁，然后在短时间后释放
    thread::spawn(move || {
        if client1_clone.try_lock(&resource1_clone, Duration::from_secs(2)) {
            println!("客户端1在后台线程中获取了资源1的锁");
            
            // 持有锁一段时间
            thread::sleep(Duration::from_millis(500));
            
            // 释放锁
            client1_clone.unlock(&resource1_clone);
            println!("客户端1在后台线程中释放了资源1的锁");
        }
    });
    
    // 给客户端1一些时间来获取锁
    thread::sleep(Duration::from_millis(100));
    
    // 客户端3尝试使用重试机制获取锁
    if client3.lock_with_retry(
        resource1,
        Duration::from_secs(5),
        5,
        Duration::from_millis(200),
    ) {
        println!("客户端3最终获取了资源1的锁（通过重试）");
        
        // 模拟工作
        thread::sleep(Duration::from_millis(100));
        
        // 释放锁
        client3.unlock(resource1);
    }
    
    // 测试锁过期
    println!("\n测试锁过期:");
    if client1.try_lock(resource1, Duration::from_millis(200)) {
        println!("客户端1获取了资源1的短期锁（200毫秒）");
        
        // 等待锁过期
        thread::sleep(Duration::from_millis(300));
        
        // 客户端2应该能够获取锁，因为客户端1的锁已过期
        if client2.try_lock(resource1, Duration::from_secs(5)) {
            println!("客户端2在客户端1的锁过期后获取了资源1的锁");
            client2.unlock(resource1);
        }
    }
}
```

### 3.5 一致性哈希模式Consistent Hashing Pattern

```rust
// 一致性哈希模式 - 分布式缓存
use std::collections::{BTreeMap, HashMap};
use std::hash::{Hash, Hasher};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

// 哈希函数
fn hash<T: Hash>(t: &T) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    let mut s = DefaultHasher::new();
    t.hash(&mut s);
    s.finish()
}

// 一致性哈希环
struct ConsistentHash {
    ring: BTreeMap<u64, String>,
    virtual_nodes: usize,
}

impl ConsistentHash {
    fn new(virtual_nodes: usize) -> Self {
        ConsistentHash {
            ring: BTreeMap::new(),
            virtual_nodes,
        }
    }
    
    // 添加节点
    fn add_node(&mut self, node: impl Into<String>) {
        let node = node.into();
        
        for i in 0..self.virtual_nodes {
            let key = format!("{}:{}", node, i);
            let hash_value = hash(&key);
            self.ring.insert(hash_value, node.clone());
        }
        
        println!(
            "一致性哈希: 添加节点 '{}' (虚拟节点: {})",
            node, self.virtual_nodes
        );
    }
    
    // 移除节点
    fn remove_node(&mut self, node: impl AsRef<str>) {
        let node = node.as_ref();
        
        let keys_to_remove: Vec<u64> = self
            .ring
            .iter()
            .filter(|(_, v)| v == node)
            .map(|(k, _)| *k)
            .collect();
        
        for key in keys_to_remove {
            self.ring.remove(&key);
        }
        
        println!("一致性哈希: 移除节点 '{}'", node);
    }
    
    // 获取负责给定键的节点
    fn get_node(&self, key: impl Hash) -> Option<String> {
        if self.ring.is_empty() {
            return None;
        }
        
        let hash_value = hash(&key);
        
        // 找到第一个大于等于hash_value的节点
        match self.ring.range(hash_value..).next() {
            Some((_, node)) => Some(node.clone()),
            None => {
                // 如果没有找到，则使用环的第一个节点
                self.ring.values().next().cloned()
            }
        }
    }
    
    // 获取所有节点
    fn get_nodes(&self) -> Vec<String> {
        self.ring
            .values()
            .cloned()
            .collect::<std::collections::HashSet<_>>()
            .into_iter()
            .collect()
    }
}

// 分布式缓存
struct DistributedCache {
    consistent_hash: Mutex<ConsistentHash>,
    node_caches: Mutex<HashMap<String, HashMap<String, String>>>,
}

impl DistributedCache {
    fn new(virtual_nodes: usize) -> Self {
        DistributedCache {
            consistent_hash: Mutex::new(ConsistentHash::new(virtual_nodes)),
            node_caches: Mutex::new(HashMap::new()),
        }
    }
    
    // 添加节点
    fn add_node(&self, node: impl Into<String>) {
        let node = node.into();
        
        // 更新一致性哈希环
        self.consistent_hash.lock().unwrap().add_node(&node);
        
        // 为新节点创建缓存
        self.node_caches
            .lock()
            .unwrap()
            .entry(node)
            .or_insert_with(HashMap::new);
        
        // 重新分配键
        self.rebalance();
    }
    
    // 移除节点
    fn remove_node(&self, node: impl AsRef<str>) {
        let node = node.as_ref();
        
        // 更新一致性哈希环
        self.consistent_hash.lock().unwrap().remove_node(node);
        
        // 获取要移除的节点的缓存
        let keys_to_redistribute = {
            let mut node_caches = self.node_caches.lock().unwrap();
            if let Some(cache) = node_caches.remove(node) {
                cache.keys().cloned().collect::<Vec<_>>()
            } else {
                Vec::new()
            }
        };
        
        // 重新分配键
        for key in keys_to_redistribute {
            if let Some(value) = self.get(&key) {
                self.put(&key, &value);
            }
        }
    }
    
    // 重新平衡缓存
    fn rebalance(&self) {
        // 收集所有键值对
        let all_entries = {
            let node_caches = self.node_caches.lock().unwrap();
            let mut entries = Vec::new();
            
            for (_, cache) in node_caches.iter() {
                for (key, value) in cache.iter() {
                    entries.push((key.clone(), value.clone()));
                }
            }
            
            entries
        };
        
        // 清空所有缓存
        {
            let mut node_caches = self.node_caches.lock().unwrap();
            for (_, cache) in node_caches.iter_mut() {
                cache.clear();
            }
        }
        
        // 重新分配所有键值对
        for (key, value) in all_entries {
            self.put(&key, &value);
        }
        
        println!("分布式缓存: 完成重新平衡");
    }
    
    // 存储键值对
    fn put(&self, key: impl AsRef<str>, value: impl Into<String>) {
        let key = key.as_ref();
        let value = value.into();
        
        // 确定负责的节点
        if let Some(node) = self.consistent_hash.lock().unwrap().get_node(key) {
            // 存储在相应节点的缓存中
            let mut node_caches = self.node_caches.lock().unwrap();
            if let Some(cache) = node_caches.get_mut(&node) {
                cache.insert(key.to_string(), value.clone());
                println!(
                    "分布式缓存: 存储键 '{}' 到节点 '{}' (值: '{}')",
                    key, node, value
                );
            }
        }
    }
    
    // 获取键对应的值
    fn get(&self, key: impl AsRef<str>) -> Option<String> {
        let key = key.as_ref();
        
        // 确定负责的节点
        if let Some(node) = self.consistent_hash.lock().unwrap().get_node(key) {
            // 从相应节点的缓存中获取
            let node_caches = self.node_caches.lock().unwrap();
            if let Some(cache) = node_caches.get(&node) {
                let result = cache.get(key).cloned();
                println!(
                    "分布式缓存: 从节点 '{}' 获取键 '{}' (结果: {:?})",
                    node, key, result
                );
                return result;
            }
        }
        
        None
    }
    
    // 获取缓存统计信息
    fn get_stats(&self) -> HashMap<String, usize> {
        let node_caches = self.node_caches.lock().unwrap();
        node_caches
            .iter()
            .map(|(node, cache)| (node.clone(), cache.len()))
            .collect()
    }
}

// 使用示例
fn consistent_hashing_example() {
    // 创建分布式缓存
    let cache = Arc::new(DistributedCache::new(10));
    
    // 添加初始节点
    cache.add_node("node1");
    cache.add_node("node2");
    cache.add_node("node3");
    
    // 存储一些键值对
    let keys = vec![
        "user:1", "user:2", "user:3", "user:4", "user:5",
        "product:1", "product:2", "product:3",
        "order:1", "order:2",
    ];
    
    for key in &keys {
        cache.put(key, format!("value-for-{}", key));
    }
    
    // 显示初始分布
    println!("\n初始分布:");
    let stats = cache.get_stats();
    for (node, count) in &stats {
        println!("节点 {}: {} 个项目", node, count);
    }
    
    // 读取一些值
    for key in keys.iter().take(5) {
        if let Some(value) = cache.get(key) {
            println!("读取 {}: {}", key, value);
        }
    }
    
    // 添加新节点
    println!("\n添加新节点 'node4'");
    cache.add_node("node4");
    
    // 显示添加节点后的分布
    println!("\n添加节点后的分布:");
    let stats = cache.get_stats();
    for (node, count) in &stats {
        println!("节点 {}: {} 个项目", node, count);
    }
    
    // 移除一个节点
    println!("\n移除节点 'node2'");
    cache.remove_node("node2");
    
    // 显示移除节点后的分布
    println!("\n移除节点后的分布:");
    let stats = cache.get_stats();
    for (node, count) in &stats {
        println!("节点 {}: {} 个项目", node, count);
    }
    
    // 再次读取所有值，确保它们仍然可用
    println!("\n验证所有键仍然可用:");
    for key in &keys {
        if let Some(value) = cache.get(key) {
            println!("读取 {}: {}", key, value);
        } else {
            println!("键 {} 不可用", key);
        }
    }
    
    // 模拟节点故障和恢复
    println!("\n模拟节点 'node3' 故障和恢复");
    
    // 保存node3的数据
    let node3_data = {
        let node_caches = cache.node_caches.lock().unwrap();
        if let Some(cache) = node_caches.get("node3") {
            cache.clone()
        } else {
            HashMap::new()
        }
    };
    
    // 移除node3（模拟故障）
    cache.remove_node("node3");
    
    // 显示节点故障后的分布
    println!("\n节点故障后的分布:");
    let stats = cache.get_stats();
    for (node, count) in &stats {
        println!("节点 {}: {} 个项目", node, count);
    }
    
    // 恢复node3
    cache.add_node("node3");
    
    // 显示节点恢复后的分布
    println!("\n节点恢复后的分布:");
    let stats = cache.get_stats();
    for (node, count) in &stats {
        println!("节点 {}: {} 个项目", node, count);
    }
}
```

## 4 四、Rust 2024 表达能力分析

### 4.1 Rust 并发模式的表达能力

Rust 2024 在并发编程方面提供了强大而灵活的表达能力，主要体现在以下几个方面：

1. **所有权和借用系统**：Rust 的核心特性使并发安全成为可能
   - 编译时防止数据竞争
   - 无需垃圾回收即可安全管理内存
   - 通过类型系统强制执行线程安全约束

2. **丰富的并发原语**：
   - 标准库提供的 `Mutex`、`RwLock`、`Arc` 等
   - 通道（`mpsc`）用于线程间通信
   - `Atomic` 类型用于无锁并发

3. **异步编程支持**：
   - `async`/`await` 语法
   - `Future` 特征和执行器
   - 零成本抽象，编译为高效状态机

4. **第三方生态系统**：
   - Tokio、async-std 等异步运行时
   - Rayon 用于数据并行
   - Crossbeam 提供高级并发工具

```rust
// Rust 并发表达能力示例

// 1. 所有权系统保证线程安全
fn ownership_example() {
    let data = vec![1, 2, 3, 4, 5];
    
    // 将所有权移动到新线程
    let handle = thread::spawn(move || {
        // 在这里，data 被安全地移动到新线程
        println!("线程拥有数据: {:?}", data);
    });
    
    // 这里不能再访问 data，编译器会阻止
    // println!("主线程访问数据: {:?}", data); // 编译错误
    
    handle.join().unwrap();
}

// 2. 共享状态并发
fn shared_state_example() {
    // 使用 Arc 在线程间共享数据
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];
    
    for _ in 0..10 {
        let counter_clone = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            let mut num = counter_clone.lock().unwrap();
            *num += 1;
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("计数器结果: {}", *counter.lock().unwrap());
}

// 3. 消息传递并发
fn message_passing_example() {
    let (tx, rx) = mpsc::channel();
    
    thread::spawn(move || {
        for i in 1..5 {
            tx.send(i).unwrap();
            thread::sleep(Duration::from_millis(100));
        }
    });
    
    for received in rx {
        println!("收到: {}", received);
    }
}

// 4. 异步编程
async fn async_example() {
    let mut tasks = Vec::new();
    
    for i in 0..5 {
        tasks.push(async move {
            tokio::time::sleep(Duration::from_millis(100)).await;
            i
        });
    }
    
    let results = futures::future::join_all(tasks).await;
    println!("异步结果: {:?}", results);
}
```

### 4.2 Rust 并行模式的表达能力

Rust 2024 在并行编程方面的表达能力主要体现在：

1. **数据并行**：
   - Rayon 库提供简单的并行迭代器
   - 自动负载均衡
   - 工作窃取调度

2. **任务并行**：
   - 线程池和任务调度
   - 分而治之模式的自然表达
   - 并行管道处理

3. **SIMD 支持**：
   - 向量化操作
   - 编译器自动优化
   - 显式 SIMD 指令

4. **并行安全保证**：
   - 编译时检查并行安全性
   - 类型系统防止数据竞争
   - Send 和 Sync 特征

```rust
// Rust 并行表达能力示例

// 1. 数据并行 - 使用 Rayon
fn data_parallel_example() {
    use rayon::prelude::*;
    
    let data: Vec<i32> = (0..1000).collect();
    
    // 串行处理
    let sum_sequential: i32 = data.iter().map(|&x| x * x).sum();
    
    // 并行处理 - 只需将 iter() 改为 par_iter()
    let sum_parallel: i32 = data.par_iter().map(|&x| x * x).sum();
    
    assert_eq!(sum_sequential, sum_parallel);
    println!("并行计算结果正确: {}", sum_parallel);
}

// 2. 任务并行 - 分而治之
fn parallel_quicksort<T: Ord + Send>(slice: &mut [T]) {
    if slice.len() <= 1 {
        return;
    }
    
    let mid = partition(slice);
    let (left, right) = slice.split_at_mut(mid);
    
    // 并行处理两个子数组
    rayon::join(
        || parallel_quicksort(left),
        || parallel_quicksort(right),
    );
}

fn partition<T: Ord>(slice: &mut [T]) -> usize {
    let pivot = slice.len() - 1;
    let mut i = 0;
    
    for j in 0..pivot {
        if slice[j] <= slice[pivot] {
            slice.swap(i, j);
            i += 1;
        }
    }
    
    slice.swap(i, pivot);
    i
}

// 3. SIMD 支持
#[cfg(target_arch = "x86_64")]
fn simd_example() {
    use std::arch::x86_64::*;
    
    // 安全地使用 SIMD 指令
    unsafe {
        // 检查 CPU 是否支持 AVX2
        if is_x86_feature_detected!("avx2") {
            let a = _mm256_set1_epi32(10);
            let b = _mm256_set1_epi32(20);
            let result = _mm256_add_epi32(a, b);
            
            // 提取结果
            let mut output = [0i32; 8];
            _mm256_storeu_si256(output.as_mut_ptr() as *mut __m256i, result);
            
            println!("SIMD 结果: {:?}", output);
        } else {
            println!("CPU 不支持 AVX2");
        }
    }
}

// 4. 并行安全保证
struct ParallelSafeData {
    data: Vec<i32>,
}

// 实现 Send 和 Sync 特征，表明类型可以安全地在线程间传递和共享
unsafe impl Send for ParallelSafeData {}
unsafe impl Sync for ParallelSafeData {}

fn parallel_safety_example() {
    let data = Arc::new(ParallelSafeData { data: vec![1, 2, 3] });
    
    let data_clone = Arc::clone(&data);
    let handle = thread::spawn(move || {
        // 在另一个线程中安全地访问数据
        println!("线程访问数据: {:?}", data_clone.data);
    });
    
    // 在主线程中访问相同的数据
    println!("主线程访问数据: {:?}", data.data);
    
    handle.join().unwrap();
}
```

### 4.3 Rust 分布式模式的表达能力

Rust 2024 在分布式系统设计方面的表达能力：

1. **网络编程**：
   - 异步网络 I/O
   - 高性能 TCP/UDP 处理
   - HTTP 客户端和服务器

2. **序列化/反序列化**：
   - Serde 生态系统
   - 多种格式支持（JSON, CBOR, MessagePack 等）
   - 零拷贝反序列化

3. **分布式协议实现**：
   - 状态机建模
   - 错误处理和恢复
   - 超时和重试逻辑

4. **容错和弹性**：
   - 断路器模式
   - 重试和退避策略
   - 超时处理

```rust
// Rust 分布式表达能力示例

// 1. 网络编程 - 异步 TCP 服务器
async fn async_tcp_server_example() {
    use tokio::net::{TcpListener, TcpStream};
    use tokio::io::{AsyncReadExt, AsyncWriteExt};
    
    async fn handle_client(mut socket: TcpStream) {
        let mut buffer = [0; 1024];
        
        loop {
            match socket.read(&mut buffer).await {
                Ok(0) => break, // 连接关闭
                Ok(n) => {
                    // 回显接收到的数据
                    if socket.write_all(&buffer[0..n]).await.is_err() {
                        break;
                    }
                }
                Err(_) => break,
            }
        }
    }
    
    async fn run_server() {
        let listener = TcpListener::bind("127.0.0.1:8080").await.unwrap();
        println!("服务器监听在 127.0.0.1:8080");
        
        loop {
            match listener.accept().await {
                Ok((socket, addr)) => {
                    println!("新连接: {}", addr);
                    tokio::spawn(handle_client(socket));
                }
                Err(e) => {
                    println!("接受连接错误: {}", e);
                }
            }
        }
    }
    
    // 在实际应用中，你会调用 run_server().await
    println!("异步 TCP 服务器示例");
}

// 2. 序列化/反序列化
fn serialization_example() {
    use serde::{Serialize, Deserialize};
    
    #[derive(Serialize, Deserialize, Debug)]
    struct User {
        id: u64,
        name: String,
        email: Option<String>,
        roles: Vec<String>,
    }
    
    // 创建用户
    let user = User {
        id: 1,
        name: "Alice".to_string(),
        email: Some("alice@example.com".to_string()),
        roles: vec!["admin".to_string(), "user".to_string()],
    };
    
    // 序列化为 JSON
    let json = serde_json::to_string(&user).unwrap();
    println!("JSON: {}", json);
    
    // 反序列化
    let deserialized: User = serde_json::from_str(&json).unwrap();
    println!("反序列化: {:?}", deserialized);
    
    // 序列化为二进制格式 (CBOR)
    let cbor = serde_cbor::to_vec(&user).unwrap();
    println!("CBOR 大小: {} 字节", cbor.len());
    
    // 反序列化 CBOR
    let deserialized_cbor: User = serde_cbor::from_slice(&cbor).unwrap();
    println!("CBOR 反序列化: {:?}", deserialized_cbor);
}

// 3. 分布式协议 - Raft 共识算法状态机示例
enum RaftState {
    Follower,
    Candidate,
    Leader,
}

struct RaftNode {
    state: RaftState,
    current_term: u64,
    voted_for: Option<String>,
    log: Vec<LogEntry>,
    commit_index: usize,
    last_applied: usize,
    // 其他 Raft 状态...
}

struct LogEntry {
    term: u64,
    command: Vec<u8>,
}

impl RaftNode {
    fn new() -> Self {
        RaftNode {
            state: RaftState::Follower,
            current_term: 0,
            voted_for: None,
            log: Vec::new(),
            commit_index: 0,
            last_applied: 0,
        }
    }
    
    fn handle_append_entries(&mut self, term: u64, leader_id: &str, entries: Vec<LogEntry>) -> bool {
        // 简化的 AppendEntries RPC 处理
        if term < self.current_term {
            return false; // 拒绝来自过期任期的请求
        }
        
        if term > self.current_term {
            self.current_term = term;
            self.state = RaftState::Follower;
            self.voted_for = None;
        }
        
        // 处理日志条目...
        true
    }
    
    fn handle_request_vote(&mut self, term: u64, candidate_id: &str) -> bool {
        // 简化的 RequestVote RPC 处理
        if term < self.current_term {
            return false;
        }
        
        if term > self.current_term {
            self.current_term = term;
            self.state = RaftState::Follower;
            self.voted_for = None;
        }
        
        if self.voted_for.is_none() || self.voted_for.as_ref().unwrap() == candidate_id {
            self.voted_for = Some(candidate_id.to_string());
            return true;
        }
        
        false
    }
    
    // 其他 Raft 算法方法...
}

// 4. 容错和弹性 - 断路器模式
struct CircuitBreaker {
    failure_threshold: u32,
    reset_timeout: Duration,
    failure_count: u32,
    last_failure_time: Option<Instant>,
    state: CircuitState,
}

enum CircuitState {
    Closed,    // 正常运行
    Open,      // 断开状态，快速失败
    HalfOpen,  // 尝试恢复
}

impl CircuitBreaker {
    fn new(failure_threshold: u32, reset_timeout: Duration) -> Self {
        CircuitBreaker {
            failure_threshold,
            reset_timeout,
            failure_count: 0,
            last_failure_time: None,
            state: CircuitState::Closed,
        }
    }
    
    fn execute<F, T, E>(&mut self, operation: F) -> Result<T, E>
    where
        F: FnOnce() -> Result<T, E>,
    {
        match self.state {
            CircuitState::Open => {
                // 检查是否应该转换到半开状态
                if let Some(failure_time) = self.last_failure_time {
                    if failure_time.elapsed() >= self.reset_timeout {
                        println!("断路器: 从开路状态转换到半开状态");
                        self.state = CircuitState::HalfOpen;
                    } else {
                        return Err(operation().unwrap_err()); // 快速失败
                    }
                }
            }
            CircuitState::Closed | CircuitState::HalfOpen => {
                // 继续执行
            }
        }
        
        // 执行操作
        match operation() {
            Ok(result) => {
                // 成功，重置失败计数
                self.failure_count = 0;
                
                // 如果是半开状态，则转换回关闭状态
                if matches!(self.state, CircuitState::HalfOpen) {
                    println!("断路器: 从半开状态转换到关闭状态");
                    self.state = CircuitState::Closed;
                }
                
                Ok(result)
            }
            Err(error) => {
                // 失败，增加失败计数
                self.failure_count += 1;
                self.last_failure_time = Some(Instant::now());
                
                // 检查是否应该打开断路器
                if self.failure_count >= self.failure_threshold {
                    println!("断路器: 从{}状态转换到开路状态", 
                        match self.state {
                            CircuitState::Closed => "关闭",
                            CircuitState::HalfOpen => "半开",
                            CircuitState::Open => "开路",
                        }
                    );
                    self.state = CircuitState::Open;
                }
                
                Err(error)
            }
        }
    }
}

fn circuit_breaker_example() {
    let mut breaker = CircuitBreaker::new(3, Duration::from_secs(5));
    let mut fail_counter = 0;
    
    // 模拟一些操作
    for i in 0..10 {
        println!("尝试操作 {}", i);
        
        let result = breaker.execute(|| {
            // 模拟一些可能失败的操作
            if i < 5 && i % 2 == 0 {
                fail_counter += 1;
                println!("操作 {} 失败 (故意失败)", i);
                Err("操作失败")
            } else {
                println!("操作 {} 成功", i);
                Ok(format!("结果 {}", i))
            }
        });
        
        match result {
            Ok(value) => println!("获得结果: {}", value),
            Err(error) => println!("错误: {}", error),
        }
        
        // 添加一些延迟
        thread::sleep(Duration::from_millis(500));
    }
}
```

## 5 五、Rust 2024 设计模式实现对比分析

### 5.1 并发模式实现对比

Rust 提供了多种实现并发模式的方法，每种方法都有其优缺点：

#### 1.1.1 互斥锁模式对比

```rust
// 方法1: 使用标准库 Mutex
fn mutex_std_example() {
    use std::sync::{Arc, Mutex};
    
    let counter = Arc::new(Mutex::new(0));
    let counter_clone = Arc::clone(&counter);
    
    let handle = thread::spawn(move || {
        let mut num = counter_clone.lock().unwrap();
        *num += 1;
    });
    
    handle.join().unwrap();
    println!("计数: {}", *counter.lock().unwrap());
}

// 方法2: 使用 parking_lot Mutex (更高性能)
fn mutex_parking_lot_example() {
    use parking_lot::Mutex;
    use std::sync::Arc;
    
    let counter = Arc::new(Mutex::new(0));
    let counter_clone = Arc::clone(&counter);
    
    let handle = thread::spawn(move || {
        let mut num = counter_clone.lock();
        *num += 1;
    });
    
    handle.join().unwrap();
    println!("计数: {}", *counter.lock());
}

// 方法3: 使用原子类型 (无锁)
fn atomic_example() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;
    
    let counter = Arc::new(AtomicUsize::new(0));
    let counter_clone = Arc::clone(&counter);
    
    let handle = thread::spawn(move || {
        counter_clone.fetch_add(1, Ordering::SeqCst);
    });
    
    handle.join().unwrap();
    println!("计数: {}", counter.load(Ordering::SeqCst));
}

// 性能对比
fn mutex_performance_comparison() {
    use std::sync::{Arc, Mutex};
    use std::time::Instant;
    
    const ITERATIONS: usize = 1_000_000;
    const THREADS: usize = 4;
    
    // 标准库 Mutex
    {
        let counter = Arc::new(Mutex::new(0));
        let start = Instant::now();
        
        let mut handles = Vec::new();
        for _ in 0..THREADS {
            let counter = Arc::clone(&counter);
            let handle = thread::spawn(move || {
                for _ in 0..ITERATIONS / THREADS {
                    let mut num = counter.lock().unwrap();
                    *num += 1;
                }
            });
            handles.push(handle);
        }
        
        for handle in handles {
            handle.join().unwrap();
        }
        
        let duration = start.elapsed();
        println!("标准库 Mutex: {:?}, 结果: {}", duration, *counter.lock().unwrap());
    }
    
    // parking_lot Mutex
    {
        let counter = Arc::new(parking_lot::Mutex::new(0));
        let start = Instant::now();
        
        let mut handles = Vec::new();
        for _ in 0..THREADS {
            let counter = Arc::clone(&counter);
            let handle = thread::spawn(move || {
                for _ in 0..ITERATIONS / THREADS {
                    let mut num = counter.lock();
                    *num += 1;
                }
            });
            handles.push(handle);
        }
        
        for handle in handles {
            handle.join().unwrap();
        }
        
        let duration = start.elapsed();
        println!("parking_lot Mutex: {:?}, 结果: {}", duration, *counter.lock());
    }
    
    // 原子类型
    {
        let counter = Arc::new(AtomicUsize::new(0));
        let start = Instant::now();
        
        let mut handles = Vec::new();
        for _ in 0..THREADS {
            let counter = Arc::clone(&counter);
            let handle = thread::spawn(move || {
                for _ in 0..ITERATIONS / THREADS {
                    counter.fetch_add(1, Ordering::SeqCst);
                }
            });
            handles.push(handle);
        }
        
        for handle in handles {
            handle.join().unwrap();
        }
        
        let duration = start.elapsed();
        println!("原子类型: {:?}, 结果: {}", duration, counter.load(Ordering::SeqCst));
    }
}
```

#### 1.1.2 通道模式对比

```rust
// 方法1: 标准库 mpsc 通道
fn mpsc_channel_example() {
    use std::sync::mpsc;
    
    let (tx, rx) = mpsc::channel();
    
    thread::spawn(move || {
        for i in 0..5 {
            tx.send(i).unwrap();
            thread::sleep(Duration::from_millis(100));
        }
    });
    
    for received in rx {
        println!("收到: {}", received);
    }
}

// 方法2: crossbeam 通道 (支持多生产者多消费者)
fn crossbeam_channel_example() {
    use crossbeam::channel;
    
    let (tx, rx) = channel::unbounded();
    
    // 多个生产者
    for id in 0..3 {
        let tx = tx.clone();
        thread::spawn(move || {
            for i in 0..3 {
                tx.send(format!("生产者 {} - 消息 {}", id, i)).unwrap();
                thread::sleep(Duration::from_millis(100));
            }
        });
    }
    
    // 需要丢弃最后一个发送者
    drop(tx);
    
    // 多个消费者
    let rx1 = rx.clone();
    let rx2 = rx;
    
    let handle1 = thread::spawn(move || {
        for msg in rx1 {
            println!("消费者 1 收到: {}", msg);
        }
    });
    
    let handle2 = thread::spawn(move || {
        for msg in rx2 {
            println!("消费者 2 收到: {}", msg);
        }
    });
    
    handle1.join().unwrap();
    handle2.join().unwrap();
}

// 方法3: tokio 通道 (异步)
async fn tokio_channel_example() {
    use tokio::sync::mpsc;
    
    let (tx, mut rx) = mpsc::channel(10);
    
    tokio::spawn(async move {
        for i in 0..5 {
            tx.send(i).await.unwrap();
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    });
    
    while let Some(received) = rx.recv().await {
        println!("异步收到: {}", received);
    }
}

// 性能对比
fn channel_performance_comparison() {
    use std::sync::mpsc;
    use std::time::Instant;
    
    const MESSAGES: usize = 1_000_000;
    
    // 标准库 mpsc
    {
        let (tx, rx) = mpsc::channel();
        let start = Instant::now();
        
        let handle = thread::spawn(move || {
            for i in 0..MESSAGES {
                tx.send(i).unwrap();
            }
        });
        
        let mut count = 0;
        for _ in rx {
            count += 1;
            if count == MESSAGES {
                break;
            }
        }
        
        handle.join().unwrap();
        let duration = start.elapsed();
        println!("标准库 mpsc: {:?} 用于 {} 条消息", duration, MESSAGES);
    }
    
    // crossbeam 通道
    {
        let (tx, rx) = crossbeam::channel::unbounded();
        let start = Instant::now();
        
        let handle = thread::spawn(move || {
            for i in 0..MESSAGES {
                tx.send(i).unwrap();
            }
        });
        
        let mut count = 0;
        for _ in rx {
            count += 1;
            if count == MESSAGES {
                break;
            }
        }
        
        handle.join().unwrap();
        let duration = start.elapsed();
        println!("crossbeam 通道: {:?} 用于 {} 条消息", duration, MESSAGES);
    }
}
```

### 5.2 并行模式实现对比

Rust 提供了多种实现并行模式的方法，每种方法都有其优缺点：

#### 2.2.1 数据并行对比

```rust
// 方法1: 手动线程管理
fn manual_threading_example() {
    let data: Vec<i32> = (0..1000).collect();
    let chunks = 4;
    let chunk_size = data.len() / chunks;
    
    let mut handles = Vec::new();
    let mut results = vec![0; chunks];
    
    for (i, chunk) in data.chunks(chunk_size).enumerate() {
        let chunk_data = chunk.to_vec();
        let handle = thread::spawn(move || {
            chunk_data.iter().map(|&x| x * x).sum::<i32>()
        });
        handles.push((i, handle));
    }
    
    for (i, handle) in handles {
        results[i] = handle.join().unwrap();
    }
    
    let total: i32 = results.iter().sum();
    println!("手动线程结果: {}", total);
}

// 方法2: 使用 Rayon
fn rayon_example() {
    use rayon::prelude::*;
    
    let data: Vec<i32> = (0..1000).collect();
    
    let total: i32 = data.par_iter().map(|&x| x * x).sum();
    println!("Rayon 结果: {}", total);
}

// 方法3: 使用 Tokio 并行任务
async fn tokio_parallel_example() {
    let data: Vec<i32> = (0..1000).collect();
    let chunks = 4;
    let chunk_size = data.len() / chunks;
    
    let mut tasks = Vec::new();
    
    for chunk in data.chunks(chunk_size) {
        let chunk_data = chunk.to_vec();
        let task = tokio::spawn(async move {
            chunk_data.iter().map(|&x| x * x).sum::<i32>()
        });
        tasks.push(task);
    }
    
    let mut total = 0;
    for task in tasks {
        total += task.await.unwrap();
    }
    
    println!("Tokio 并行结果: {}", total);
}

// 性能对比
fn parallel_performance_comparison() {
    use std::time::Instant;
    
    const SIZE: usize = 10_000_000;
    let data: Vec<i32> = (0..SIZE as i32).collect();
    
    // 串行处理
    {
        let start = Instant::now();
        let sum: i64 = data.iter().map(|&x| x as i64 * x as i64).sum();
        let duration = start.elapsed();
        println!("串行处理: {:?}, 结果: {}", duration, sum);
    }
    
    // 手动线程
    {
        let start = Instant::now();
        let chunks = num_cpus::get();
        let chunk_size = data.len() / chunks;
        
        let mut handles = Vec::new();
        
        for chunk in data.chunks(chunk_size) {
            let chunk_data = chunk.to_vec();
            let handle = thread::spawn(move || {
                chunk_data.iter().map(|&x| x as i64 * x as i64).sum::<i64>()
            });
            handles.push(handle);
        }
        
        let mut sum = 0;
        for handle in handles {
            sum += handle.join().unwrap();
        }
        
        let duration = start.elapsed();
        println!("手动线程: {:?}, 结果: {}", duration, sum);
    }
    
    // Rayon
    {
        use rayon::prelude::*;
        
        let start = Instant::now();
        let sum: i64 = data.par_iter().map(|&x| x as i64 * x as i64).sum();
        let duration = start.elapsed();
        println!("Rayon: {:?}, 结果: {}", duration, sum);
    }
}
```

#### 2.2.2 分而治之模式对比

```rust
// 方法1: 递归线程
fn recursive_threading_quicksort(slice: &mut [i32]) {
    if slice.len() <= 1 {
        return;
    }
    
    let mid = partition(slice);
    
    // 只在数组足够大时创建新线程
    if slice.len() > 1000 {
        let (left, right) = slice.split_at_mut(mid);
        
        let handle = thread::spawn(move || {
            recursive_threading_quicksort(left);
        });
        
        recursive_threading_quicksort(right);
        
        handle.join().unwrap();
    } else {
        let (left, right) = slice.split_at_mut(mid);
        recursive_threading_quicksort(left);
        recursive_threading_quicksort(right);
    }
}

// 方法2: 使用 Rayon
fn rayon_quicksort(slice: &mut [i32]) {
    if slice.len() <= 1 {
        return;
    }
    
    let mid = partition(slice);
    let (left, right) = slice.split_at_mut(mid);
    
    rayon::join(
        || rayon_quicksort(left),
        || rayon_quicksort(right),
    );
}

// 方法3: 使用线程池
fn threadpool_quicksort(pool: &threadpool::ThreadPool, slice: &mut [i32]) {
    if slice.len() <= 1 {
        return;
    }
    
    let mid = partition(slice);
    
    if slice.len() > 1000 {
        let (left, right) = slice.split_at_mut(mid);
        
        let left_data = left.to_vec();
        let (tx, rx) = mpsc::channel();
        
        pool.execute(move || {
            let mut left_sorted = left_data;
            sequential_quicksort(&mut left_sorted);
            tx.send(left_sorted).unwrap();
        });
        
        sequential_quicksort(right);
        
        // 接收排序后的左半部分并复制回原数组
        let left_sorted = rx.recv().unwrap();
        left.copy_from_slice(&left_sorted);
    } else {
        let (left, right) = slice.split_at_mut(mid);
        sequential_quicksort(left);
        sequential_quicksort(right);
    }
}

// 串行快速排序
fn sequential_quicksort(slice: &mut [i32]) {
    if slice.len() <= 1 {
        return;
    }
    
    let mid = partition(slice);
    let (left, right) = slice.split_at_mut(mid);
    
    sequential_quicksort(left);
    sequential_quicksort(right);
}

// 性能对比
fn quicksort_performance_comparison() {
    use std::time::Instant;
    
    const SIZE: usize = 1_000_000;
    
    // 生成随机数据
    let mut rng = rand::thread_rng();
    let mut data: Vec<i32> = (0..SIZE as i32).collect();
    data.shuffle(&mut rng);
    
    // 串行快速排序
    {
        let mut data_copy = data.clone();
        let start = Instant::now();
        sequential_quicksort(&mut data_copy);
        let duration = start.elapsed();
        println!("串行快速排序: {:?}", duration);
        assert!(is_sorted(&data_copy));
    }
    
    // 递归线程快速排序
    {
        let mut data_copy = data.clone();
        let start = Instant::now();
        recursive_threading_quicksort(&mut data_copy);
        let duration = start.elapsed();
        println!("递归线程快速排序: {:?}", duration);
        assert!(is_sorted(&data_copy));
    }
    
    // Rayon 快速排序
    {
        let mut data_copy = data.clone();
        let start = Instant::now();
        rayon_quicksort(&mut data_copy);
        let duration = start.elapsed();
        println!("Rayon 快速排序: {:?}", duration);
        assert!(is_sorted(&data_copy));
    }
    
    // 线程池快速排序
    {
        let pool = threadpool::ThreadPool::new(num_cpus::get());
        let mut data_copy = data.clone();
        let start = Instant::now();
        threadpool_quicksort(&pool, &mut data_copy);
        let duration = start.elapsed();
        println!("线程池快速排序: {:?}", duration);
        assert!(is_sorted(&data_copy));
    }
}

fn is_sorted(slice: &[i32]) -> bool {
    slice.windows(2).all(|w| w[0] <= w[1])
}
```

### 5.3 分布式模式实现对比

Rust 提供了多种实现分布式模式的方法，每种方法都有其优缺点：

#### 3.3.1 RPC 模式对比

```rust
// 方法1: 使用 JSON-RPC
fn json_rpc_example() {
    use jsonrpc_core::{IoHandler, Params, Value, Error};
    use jsonrpc_http_server::{ServerBuilder};
    use serde_json::json;
    
    // 服务器端
    fn setup_server() -> jsonrpc_http_server::Server {
        let mut io = IoHandler::default();
        
        io.add_method("add", |params: Params| {
            let parsed: (i64, i64) = params.parse().map_err(|_| Error::invalid_params("需要两个整数参数"))?;
            let (a, b) = parsed;
            Ok(Value::from(a + b))
        });
        
        io.add_method("echo", |params: Params| {
            let parsed: String = params.parse().map_err(|_| Error::invalid_params("需要字符串参数"))?;
            Ok(Value::from(parsed))
        });
        
        ServerBuilder::new(io)
            .start_http(&"127.0.0.1:3030".parse().unwrap())
            .expect("无法启动服务器")
    }
    
    // 客户端
    async fn client_request() {
        use reqwest::Client;
        
        let client = Client::new();
        
        // 添加请求
        let add_response = client.post("http://127.0.0.1:3030")
            .json(&json!({
                "jsonrpc": "2.0",
                "method": "add",
                "params": [5, 3],
                "id": 1
            }))
            .send()
            .await
            .unwrap()
            .json::<serde_json::Value>()
            .await
            .unwrap();
        
        println!("加法结果: {}", add_response["result"]);
        
        // 回显请求
        let echo_response = client.post("http://127.0.0.1:3030")
            .json(&json!({
                "jsonrpc": "2.0",
                "method": "echo",
                "params": "Hello, JSON-RPC!",
                "id": 2
            }))
            .send()
            .await
            .unwrap()
            .json::<serde_json::Value>()
            .await
            .unwrap();
        
        println!("回显结果: {}", echo_response["result"]);
    }
    
    println!("JSON-RPC 示例");
}

// 方法2: 使用 gRPC
fn grpc_example() {
    // 在实际应用中，你会使用 tonic 或 grpc-rust 库
    // 这里只是概念性示例
    
    // 定义服务 (通常在 .proto 文件中)
    /*
    syntax = "proto3";
    package calculator;
    
    service Calculator {
        rpc Add (AddRequest) returns (AddResponse);
        rpc Echo (EchoRequest) returns (EchoResponse);
    }
    
    message AddRequest {
        int32 a = 1;
        int32 b = 2;
    }
    
    message AddResponse {
        int32 result = 1;
    }
    
    message EchoRequest {
        string message = 1;
    }
    
    message EchoResponse {
        string message = 1;
    }
    */
    
    // 服务器实现
    /*
    #[derive(Default)]
    pub struct CalculatorService {}
    
    #[tonic::async_trait]
    impl Calculator for CalculatorService {
        async fn add(
            &self,
            request: Request<AddRequest>,
        ) -> Result<Response<AddResponse>, Status> {
            let req = request.into_inner();
            let result = req.a + req.b;
            
            Ok(Response::new(AddResponse { result }))
        }
        
        async fn echo(
            &self,
            request: Request<EchoRequest>,
        ) -> Result<Response<EchoResponse>, Status> {
            let req = request.into_inner();
            
            Ok(Response::new(EchoResponse {
                message: req.message,
            }))
        }
    }
    */
    
    println!("gRPC 示例 (概念性)");
}

// 方法3: 使用自定义二进制协议
fn custom_binary_protocol_example() {
    use bincode::{serialize, deserialize};
    use serde::{Serialize, Deserialize};
    
    #[derive(Serialize, Deserialize, Debug)]
    enum Request {
        Add { a: i32, b: i32 },
        Echo { message: String },
    }
    
    #[derive(Serialize, Deserialize, Debug)]
    enum Response {
        AddResult { result: i32 },
        EchoResult { message: String },
        Error { message: String },
    }
    
    // 处理请求
    fn handle_request(request: &Request) -> Response {
        match request {
            Request::Add { a, b } => {
                Response::AddResult { result: a + b }
            }
            Request::Echo { message } => {
                Response::EchoResult { message: message.clone() }
            }
        }
    }
    
    // 模拟客户端-服务器通信
    let add_request = Request::Add { a: 5, b: 3 };
    let echo_request = Request::Echo { message: "Hello, Binary Protocol!".to_string() };
    
    // 序列化请求
    let add_bytes = serialize(&add_request).unwrap();
    let echo_bytes = serialize(&echo_request).unwrap();
    
    println!("二进制协议 - 加法请求大小: {} 字节", add_bytes.len());
    println!("二进制协议 - 回显请求大小: {} 字节", echo_bytes.len());
    
    // 反序列化并处理
    let deserialized_add: Request = deserialize(&add_bytes).unwrap();
    let add_response = handle_request(&deserialized_add);
    
    let deserialized_echo: Request = deserialize(&echo_bytes).unwrap();
    let echo_response = handle_request(&deserialized_echo);
    
    println!("加法响应: {:?}", add_response);
    println!("回显响应: {:?}", echo_response);
}

// 性能对比
fn rpc_performance_comparison() {
    use std::time::Instant;
    
    // 这里只是概念性比较，实际测试需要完整实现各种协议
    
    println!("RPC 性能比较:");
    println!("1. JSON-RPC: 优点 - 易于调试，广泛支持；缺点 - 序列化开销大");
    println!("2. gRPC: 优点 - 高性能，强类型，支持流；缺点 - 需要 .proto 文件，设置复杂");
    println!("3. 自定义二进制: 优点 - 最小传输大小；缺点 - 缺乏标准，调试困难");
    
    // 序列化性能比较
    let test_data = (1..100).collect::<Vec<i32>>();
    
    // JSON
    {
        let start = Instant::now();
        for _ in 0..10000 {
            let json = serde_json::to_string(&test_data).unwrap();
            let _: Vec<i32> = serde_json::from_str(&json).unwrap();
        }
        println!("JSON 序列化/反序列化: {:?}", start.elapsed());
    }
    
    // Bincode
    {
        let start = Instant::now();
        for _ in 0..10000 {
            let bin = bincode::serialize(&test_data).unwrap();
            let _: Vec<i32> = bincode::deserialize(&bin).unwrap();
        }
        println!("Bincode 序列化/反序列化: {:?}", start.elapsed());
    }
}
```

## 6 六、结论与最佳实践

### 6.1 Rust 2024 并发、并行和分布式设计模式的选择指南

根据上述分析，我们可以总结出以下选择指南：

#### 1.1.1 并发模式选择

| 场景 | 推荐模式 | 理由 |
|:----:|:----|:----|
| 共享状态 | 互斥锁模式 | 当多个线程需要读写共享数据时 |
| 读多写少 | 读写锁模式 | 允许多个读取者同时访问 |
| 线程间通信 | 通道模式 | 避免共享状态的复杂性 |
| 复杂状态管理 | Actor 模式 | 封装状态和行为，通过消息通信 |
| I/O 密集型任务 | 异步任务模式 | 高效处理大量 I/O 操作 |

```rust
// 并发模式选择示例

// 1. 共享状态 - 使用互斥锁
fn shared_state_example() {
    let counter = Arc::new(Mutex::new(0));
    // 适用于: 需要多线程读写同一数据
}

// 2. 读多写少 - 使用读写锁
fn read_heavy_example() {
    let data = Arc::new(RwLock::new(Vec::<String>::new()));
    // 适用于: 读取操作远多于写入操作
}

// 3. 线程间通信 - 使用通道
fn communication_example() {
    let (tx, rx) = mpsc::channel();
    // 适用于: 线程间传递消息，避免共享状态
}

// 4. 复杂状态管理 - 使用 Actor
fn actor_example() {
    // 使用消息传递封装状态
    // 适用于: 复杂状态管理，事件驱动系统
}

// 5. I/O 密集型 - 使用异步
async fn io_heavy_example() {
    // 使用 async/await 处理 I/O
    // 适用于: 网络服务器，文件处理等
}
```

#### 1.1.2 并行模式选择

| 场景             | 推荐模式       | 理由                         |
|------------------|---------------|------------------------------|
| 大数据集处理      | 数据并行模式   | 将数据分割成块并行处理         |
| 递归问题         | 分而治之模式   | 将问题分解为子问题并行解决      |
| 不均衡工作负载    | 工作窃取模式   | 动态平衡线程间的工作量         |
| 图像/矩阵处理     | 数据并行模式   | 独立处理数据的不同部分         |
| 流水线处理       | 管道并行模式   | 将处理分为多个阶段            |

```rust
// 并行模式选择示例

// 1. 大数据集处理 - 使用数据并行
fn big_data_example() {
    use rayon::prelude::*;
    let data: Vec<i32> = (0..1_000_000).collect();
    let sum: i32 = data.par_iter().sum();
    // 适用于: 大型数据集的处理
}

// 2. 递归问题 - 使用分而治之
fn recursive_example() {
    // 使用递归分解问题
    // 适用于: 排序、搜索、图算法等
}

// 3. 不均衡工作负载 - 使用工作窃取
fn unbalanced_workload_example() {
    // 使用工作窃取调度器
    // 适用于: 任务大小不一致的场景
}

// 4. 图像处理 - 使用数据并行
fn image_processing_example() {
    // 将图像分割成块并行处理
    // 适用于: 图像滤镜、转换等
}

// 5. 流水线处理 - 使用管道并行
fn pipeline_example() {
    // 将处理分为多个阶段
    // 适用于: 数据转换、ETL 过程等
}
```

#### 1.1.3 分布式模式选择

| 场景 | 推荐模式 | 理由 |
|------|----------|------|
| 任务分发 | 主从模式 | 中央协调器分发任务给工作节点 |
| 事件驱动系统 | 发布-订阅模式 | 解耦发布者和订阅者 |
| 服务间通信 | RPC 模式 | 透明地调用远程服务 |
| 资源协调 | 分布式锁模式 | 协调对共享资源的访问 |
| 负载均衡 | 一致性哈希模式 | 分布式缓存和服务发现 |

```rust
// 分布式模式选择示例

// 1. 任务分发 - 使用主从模式
fn task_distribution_example() {
    // 主节点分发任务给工作节点
    // 适用于: 分布式计算、任务队列
}

// 2. 事件驱动 - 使用发布-订阅
fn event_driven_example() {
    // 发布者发送事件，订阅者接收
    // 适用于: 事件通知、消息系统
}

// 3. 服务间通信 - 使用 RPC
fn service_communication_example() {
    // 远程过程调用
    // 适用于: 微服务架构、API 调用
}

// 4. 资源协调 - 使用分布式锁
fn resource_coordination_example() {
    // 协调对共享资源的访问
    // 适用于: 分布式调度、领导者选举
}

// 5. 负载均衡 - 使用一致性哈希
fn load_balancing_example() {
    // 分布式缓存和服务发现
    // 适用于: 缓存系统、服务路由
}
```

### 6.2 Rust 2024 设计模式实现的最佳实践

### 6.3 并发编程最佳实践

1. **优先使用消息传递而非共享状态**
   - 使用通道（channels）传递消息
   - 避免复杂的锁逻辑

2. **正确使用 `Send` 和 `Sync` 特征**
   - 确保跨线程安全
   - 利用类型系统验证并发安全性

3. **避免过度使用互斥锁**
   - 考虑使用读写锁（`RwLock`）
   - 使用原子类型（`AtomicXXX`）代替简单计数器

4. **合理选择锁实现**
   - 标准库 `Mutex` 用于通用场景
   - `parking_lot` 用于高性能需求

5. **异步编程注意事项**
   - 避免在异步上下文中阻塞
   - 使用 `tokio::spawn` 而非 `thread::spawn`
   - 注意 `Future` 的生命周期

```rust
// 并发最佳实践示例

// 1. 消息传递优于共享状态
fn message_passing_best_practice() {
    let (tx, rx) = mpsc::channel();
    
    thread::spawn(move || {
        // 工作线程
        let result = compute_something();
        tx.send(result).unwrap();
    });
    
    // 主线程接收结果
    let result = rx.recv().unwrap();
    println!("结果: {}", result);
}

fn compute_something() -> i32 {
    // 模拟计算
    42
}

// 2. 正确使用 Send 和 Sync
struct ThreadSafeCache<T: Send + Sync> {
    data: Arc<RwLock<HashMap<String, T>>>,
}

// 3. 避免过度使用互斥锁
fn atomic_counter_example() {
    let counter = Arc::new(AtomicUsize::new(0));
    
    let counter_clone = Arc::clone(&counter);
    thread::spawn(move || {
        counter_clone.fetch_add(1, Ordering::SeqCst);
    });
    
    // 比使用 Mutex<usize> 更高效
}

// 4. 合理选择锁实现
fn lock_selection_example() {
    // 高竞争场景使用 parking_lot
    let counter = Arc::new(parking_lot::Mutex::new(0));
    
    // 低竞争场景使用标准库
    let data = Arc::new(std::sync::Mutex::new(Vec::<String>::new()));
}

// 5. 异步编程注意事项
async fn async_best_practice() {
    // 在异步上下文中不要使用阻塞操作
    // 错误示例:
    // thread::sleep(Duration::from_secs(1));
    
    // 正确示例:
    tokio::time::sleep(Duration::from_secs(1)).await;
    
    // 使用 tokio::spawn 而非 thread::spawn
    let handle = tokio::spawn(async {
        // 异步工作
        "结果".to_string()
    });
    
    let result = handle.await.unwrap();
    println!("异步结果: {}", result);
}
```

### 6.4 并行编程最佳实践

1. **使用 Rayon 简化数据并行**
   - 利用 `par_iter()` 替代手动线程管理
   - 使用 `join()` 实现任务并行

2. **避免过细粒度的并行**
   - 确保每个并行任务有足够的工作量
   - 使用阈值控制并行粒度

3. **减少线程间数据移动**
   - 尽量避免克隆大型数据结构
   - 使用引用或切片共享数据

4. **注意负载均衡**
   - 使用工作窃取调度器
   - 动态调整任务大小

5. **避免过度并行**
   - 考虑 CPU 核心数量
   - 监控线程竞争和上下文切换

```rust
// 并行最佳实践示例

// 1. 使用 Rayon 简化数据并行
fn rayon_best_practice() {
    use rayon::prelude::*;
    
    let data: Vec<i32> = (0..10000).collect();
    
    // 数据并行
    let sum: i32 = data.par_iter()
                      .map(|&x| x * x)
                      .sum();
    
    // 任务并行
    let (sum1, sum2) = rayon::join(
        || data[0..5000].iter().sum::<i32>(),
        || data[5000..].iter().sum::<i32>()
    );
    
    assert_eq!(sum1 + sum2, data.iter().sum::<i32>());
}

// 2. 避免过细粒度的并行
fn granularity_best_practice() {
    use rayon::prelude::*;
    
    fn parallel_process<T: Send + Sync>(data: &[T], threshold: usize) {
        if data.len() <= threshold {
            // 数据量小时使用串行处理
            sequential_process(data);
        } else {
            // 数据量大时并行处理
            data.par_chunks(data.len() / rayon::current_num_threads())
               .for_each(|chunk| sequential_process(chunk));
        }
    }
    
    fn sequential_process<T>(_data: &[T]) {
        // 串行处理逻辑
    }
}

// 3. 减少线程间数据移动
fn data_movement_best_practice() {
    use rayon::prelude::*;
    
    let large_data = vec![0; 1_000_000];
    
    // 不好的做法 - 克隆大型数据
    let bad_approach = (0..4).into_par_iter().map(|i| {
        let data_copy = large_data.clone(); // 克隆整个数据
        process_chunk(&data_copy, i)
    }).sum::<i32>();
    
    // 好的做法 - 共享引用
    let good_approach = (0..4).into_par_iter().map(|i| {
        process_chunk(&large_data, i) // 共享引用
    }).sum::<i32>();
    
    fn process_chunk(_data: &[i32], _index: i32) -> i32 {
        // 处理逻辑
        42
    }
}

// 4. 注意负载均衡
fn load_balancing_best_practice() {
    use rayon::prelude::*;
    
    // 不均衡的工作负载
    let tasks: Vec<usize> = (0..100).map(|i| i * i % 1000).collect();
    
    // 使用动态调度
    let results: Vec<_> = tasks.into_par_iter()
        .map(|work_amount| {
            // 模拟不同工作量
            let mut result = 0;
            for i in 0..work_amount {
                result += i;
            }
            result
        })
        .collect();
}

// 5. 避免过度并行
fn avoid_over_parallelization() {
    use rayon::prelude::*;
    use std::cmp::min;
    
    let data: Vec<i32> = (0..10000).collect();
    
    // 限制并行度
    let num_threads = min(num_cpus::get(), 8); // 最多使用8个线程
    
    rayon::ThreadPoolBuilder::new()
        .num_threads(num_threads)
        .build_global()
        .unwrap();
    
    let sum: i32 = data.par_iter().sum();
}
```

### 6.5 分布式编程最佳实践

1. **设计容错系统**
   - 实现重试机制
   - 使用断路器模式
   - 处理部分失败

2. **最小化网络通信**
   - 批处理请求
   - 压缩数据
   - 使用高效序列化格式

3. **状态管理策略**
   - 明确定义状态所有权
   - 考虑最终一致性
   - 使用适当的同步机制

4. **监控和可观测性**
   - 实现健康检查
   - 收集指标和日志
   - 跟踪分布式事务

5. **安全通信**
   - 使用 TLS 加密
   - 实现身份验证和授权
   - 防止常见攻击

```rust
// 分布式最佳实践示例

// 1. 设计容错系统
fn fault_tolerance_best_practice() {
    // 重试机制
    fn with_retry<F, T, E>(operation: F, max_retries: usize) -> Result<T, E>
    where
        F: Fn() -> Result<T, E>,
    {
        let mut attempts = 0;
        loop {
            match operation() {
                Ok(result) => return Ok(result),
                Err(err) => {
                    attempts += 1;
                    if attempts >= max_retries {
                        return Err(err);
                    }
                    // 指数退避
                    thread::sleep(Duration::from_millis(100 * 2u64.pow(attempts as u32)));
                }
            }
        }
    }
    
    // 断路器模式
    struct CircuitBreaker {
        // 实现见前面的示例
    }
}

// 2. 最小化网络通信
fn minimize_network_best_practice() {
    // 批处理请求
    fn batch_requests<T>(requests: Vec<T>) -> Vec<T> {
        // 将多个请求合并为一个批处理
        requests
    }
    
    // 使用高效序列化
    fn efficient_serialization() {
        // 使用 Protocol Buffers, FlatBuffers 或 Cap'n Proto
        // 而不是 JSON
    }
}

// 3. 状态管理策略
fn state_management_best_practice() {
    // 明确状态所有权
    enum StateOwnership {
        Single, // 单一所有者
        Replicated, // 复制到多个节点
        Sharded, // 分片存储
    }
    
    // 最终一致性
    struct EventuallyConsistentStore<T> {
        data: T,
        version: u64,
        last_updated: Instant,
    }
}

// 4. 监控和可观测性
fn observability_best_practice() {
    // 健康检查
    async fn health_check() -> bool {
        // 检查系统健康状态
        true
    }
    
    // 指标收集
    struct Metrics {
        requests_total: u64,
        errors_total: u64,
        response_time_ms: Vec<u64>,
    }
    
    // 分布式跟踪
    struct Span {
        trace_id: String,
        span_id: String,
        parent_id: Option<String>,
        operation: String,
        start_time: Instant,
        end_time: Option<Instant>,
    }
}

// 5. 安全通信
fn secure_communication_best_practice() {
    // TLS 配置
    fn configure_tls() {
        // 配置 TLS 证书和密钥
    }
    
    // 身份验证
    struct AuthToken {
        user_id: String,
        expiration: Instant,
        signature: Vec<u8>,
    }
    
    // 授权检查
    fn check_permission(user_id: &str, resource: &str, action: &str) -> bool {
        // 检查用户是否有权限执行操作
        true
    }
}
```

### 6.6 总结

Rust 2024 为并发、并行和分布式编程提供了强大而灵活的工具和抽象。
通过所有权系统和类型安全，Rust 能够在编译时捕获许多常见的并发错误，同时保持高性能。

选择合适的设计模式应基于具体问题的特性：

- **并发模式**适用于在单机多核环境中处理多任务
- **并行模式**适用于加速计算密集型任务
- **分布式模式**适用于跨网络协调多个节点

Rust 的表达能力使其成为实现这些模式的理想语言，无论是低级系统编程还是高级分布式系统。
通过遵循最佳实践，开发者可以充分利用 Rust 的安全性和性能优势，构建可靠、高效的并发、并行和分布式系统。

随着 Rust 生态系统的不断发展，我们可以期待更多专门针对这些领域的库和工具，进一步简化复杂系统的开发。
