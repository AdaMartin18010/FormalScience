# Rust设计模式速查 🦀

> 20个常见Rust设计模式，包含代码示例和适用场景

---

## 📑 目录

- [Rust设计模式速查 🦀](#rust设计模式速查-)
  - [📑 目录](#-目录)
  - [1. 所有权相关模式](#1-所有权相关模式)
    - [1.1 RAII (资源获取即初始化)](#11-raii-资源获取即初始化)
    - [1.2 借用与内部可变性](#12-借用与内部可变性)
    - [1.3 Cow (写时克隆)](#13-cow-写时克隆)
    - [1.4 生命周期标注](#14-生命周期标注)
  - [2. 类型系统模式](#2-类型系统模式)
    - [2.1 Newtype模式](#21-newtype模式)
    - [2.2 类型状态模式](#22-类型状态模式)
    - [2.3 Builder模式](#23-builder模式)
    - [2.4 类型擦除与虚表](#24-类型擦除与虚表)
  - [3. 行为模式](#3-行为模式)
    - [3.1 策略模式](#31-策略模式)
    - [3.2 迭代器模式](#32-迭代器模式)
    - [3.3 访问者模式](#33-访问者模式)
    - [3.4 命令模式](#34-命令模式)
  - [4. 并发模式](#4-并发模式)
    - [4.1 Actor模式](#41-actor模式)
    - [4.2 通道通信](#42-通道通信)
    - [4.3 读写锁模式](#43-读写锁模式)
    - [4.4 工作窃取](#44-工作窃取)
  - [5. 错误处理模式](#5-错误处理模式)
    - [5.1 结果传播](#51-结果传播)
    - [5.2 选项组合](#52-选项组合)
    - [5.3 错误累积](#53-错误累积)
  - [6. 性能优化模式](#6-性能优化模式)
    - [6.1 零拷贝解析](#61-零拷贝解析)
    - [6.2 内存池](#62-内存池)
    - [6.3 SIMD优化](#63-simd优化)
  - [🔗 相关资源](#-相关资源)

---

## 1. 所有权相关模式

### 1.1 RAII (资源获取即初始化)

**场景**: 自动管理资源生命周期

```rust
use std::fs::File;
use std::io::{self, Write};

struct FileGuard {
    file: File,
}

impl FileGuard {
    fn new(path: &str) -> io::Result<Self> {
        Ok(Self { file: File::create(path)? })
    }
}

impl Drop for FileGuard {
    fn drop(&mut self) {
        // 自动刷新和关闭
        let _ = self.file.flush();
    }
}

// 使用
{
    let guard = FileGuard::new("data.txt")?;
    // 作用域结束时自动调用drop
} // <- 自动清理
```

### 1.2 借用与内部可变性

**场景**: 在不可变引用下修改数据

```rust
use std::cell::RefCell;
use std::rc::Rc;

// RefCell: 运行时借用检查
struct Cache {
    data: RefCell<Vec<u32>>,
}

impl Cache {
    fn add(&self, value: u32) {
        self.data.borrow_mut().push(value);  // 不可变self，可变数据
    }

    fn get(&self, index: usize) -> Option<u32> {
        self.data.borrow().get(index).copied()
    }
}

// 组合: Rc<RefCell<T>> 实现共享可变
let shared = Rc::new(RefCell::new(Vec::new()));
let clone1 = Rc::clone(&shared);
let clone2 = Rc::clone(&shared);

clone1.borrow_mut().push(1);
clone2.borrow_mut().push(2);
```

### 1.3 Cow (写时克隆)

**场景**: 避免不必要的数据拷贝

```rust
use std::borrow::Cow;

fn process_string(input: &str) -> Cow<str> {
    if input.contains('\t') {
        // 需要修改时才分配
        Cow::Owned(input.replace('\t', "    "))
    } else {
        // 无需修改，零拷贝
        Cow::Borrowed(input)
    }
}

let borrowed = process_string("hello");  // 无分配
let owned = process_string("hello\tworld");  // 需要分配
```

### 1.4 生命周期标注

**场景**: 复杂引用关系

```rust
// 结构体包含引用
struct Parser<'a> {
    input: &'a str,
    pos: usize,
}

impl<'a> Parser<'a> {
    fn new(input: &'a str) -> Self {
        Self { input, pos: 0 }
    }

    // 返回与self相同生命周期的引用
    fn peek(&self) -> Option<&'a str> {
        self.input.get(self.pos..self.pos + 1)
    }
}

// 多个生命周期参数
struct DoubleRef<'a, 'b> {
    first: &'a str,
    second: &'b str,
}
```

---

## 2. 类型系统模式

### 2.1 Newtype模式

**场景**: 类型安全，区分相同底层类型

```rust
// 避免混淆不同单位的值
struct UserId(u64);
struct ProductId(u64);

fn find_user(id: UserId) -> Option<User> { /* ... */ }
fn find_product(id: ProductId) -> Option<Product> { /* ... */ }

// 编译时防止错误
let uid = UserId(42);
find_product(uid);  // 编译错误! 类型不匹配
```

### 2.2 类型状态模式

**场景**: 在类型层面编码状态机

```rust
// 使用泛型参数表示状态
struct Connection<State> {
    stream: TcpStream,
    _state: PhantomData<State>,
}

struct Disconnected;
struct Connected;
struct Authenticated;

// 状态转换作为类型转换
impl Connection<Disconnected> {
    fn connect(addr: &str) -> io::Result<Connection<Connected>> {
        let stream = TcpStream::connect(addr)?;
        Ok(Connection { stream, _state: PhantomData })
    }
}

impl Connection<Connected> {
    fn authenticate(self, token: &str) -> Result<Connection<Authenticated>, Self> {
        // 验证token...
        if valid {
            Ok(Connection { stream: self.stream, _state: PhantomData })
        } else {
            Err(self)
        }
    }
}

// 只有认证后才能发送
impl Connection<Authenticated> {
    fn send(&mut self, data: &[u8]) -> io::Result<()> { /* ... */ }
}
```

### 2.3 Builder模式

**场景**: 复杂对象的逐步构造

```rust
#[derive(Debug)]
struct Config {
    host: String,
    port: u16,
    timeout: Duration,
    retries: u32,
}

struct ConfigBuilder {
    host: Option<String>,
    port: Option<u16>,
    timeout: Option<Duration>,
    retries: Option<u32>,
}

impl ConfigBuilder {
    fn new() -> Self {
        Self {
            host: None,
            port: None,
            timeout: Some(Duration::from_secs(30)),
            retries: Some(3),
        }
    }

    fn host(mut self, host: impl Into<String>) -> Self {
        self.host = Some(host.into());
        self
    }

    fn port(mut self, port: u16) -> Self {
        self.port = Some(port);
        self
    }

    fn build(self) -> Result<Config, BuildError> {
        Ok(Config {
            host: self.host.ok_or(BuildError::MissingHost)?,
            port: self.port.unwrap_or(8080),
            timeout: self.timeout.unwrap(),
            retries: self.retries.unwrap(),
        })
    }
}

// 流畅API
let config = ConfigBuilder::new()
    .host("localhost")
    .port(3000)
    .build()?;
```

### 2.4 类型擦除与虚表

**场景**: 运行时多态，统一处理不同类型

```rust
// Trait对象
pub trait Draw {
    fn draw(&self);
}

pub struct Screen {
    pub components: Vec<Box<dyn Draw>>,  // 类型擦除
}

impl Screen {
    pub fn run(&self) {
        for component in &self.components {
            component.draw();  // 动态分发
        }
    }
}

// 或者使用枚举实现ADT
tenum Widget {
    Button(Button),
    Label(Label),
    TextInput(TextInput),
}

impl Widget {
    fn render(&self) {
        match self {
            Self::Button(b) => b.render(),
            Self::Label(l) => l.render(),
            Self::TextInput(t) => t.render(),
        }
    }
}
```

---

## 3. 行为模式

### 3.1 策略模式

**场景**: 运行时切换算法

```rust
trait SortStrategy {
    fn sort(&self, data: &mut [i32]);
}

struct QuickSort;
struct MergeSort;
struct HeapSort;

impl SortStrategy for QuickSort {
    fn sort(&self, data: &mut [i32]) { /* ... */ }
}

impl SortStrategy for MergeSort {
    fn sort(&self, data: &mut [i32]) { /* ... */ }
}

struct Sorter<'a> {
    strategy: &'a dyn SortStrategy,
}

impl<'a> Sorter<'a> {
    fn sort(&self, data: &mut [i32]) {
        self.strategy.sort(data);
    }
}

// 运行时切换
let sorter = if data.len() < 100 {
    Sorter { strategy: &QuickSort }
} else {
    Sorter { strategy: &MergeSort }
};
```

### 3.2 迭代器模式

**场景**: 统一遍历接口

```rust
// 自定义迭代器
struct Fibonacci {
    curr: u64,
    next: u64,
}

impl Iterator for Fibonacci {
    type Item = u64;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.curr;
        self.curr = self.next;
        self.next = current + self.next;
        Some(current)
    }
}

fn fibonacci() -> Fibonacci {
    Fibonacci { curr: 0, next: 1 }
}

// 使用
for i in fibonacci().take(10) {
    println!("{}", i);
}

// 迭代器适配器链
let sum: u32 = (1..=100)
    .filter(|x| x % 2 == 0)
    .map(|x| x * x)
    .sum();
```

### 3.3 访问者模式

**场景**: 分离操作与数据结构

```rust
// AST节点
trait Expr {
    fn accept(&self, visitor: &mut dyn ExprVisitor);
}

struct Number { value: f64 }
struct Binary { left: Box<dyn Expr>, op: char, right: Box<dyn Expr> }

trait ExprVisitor {
    fn visit_number(&mut self, n: &Number);
    fn visit_binary(&mut self, b: &Binary);
}

impl Expr for Number {
    fn accept(&self, visitor: &mut dyn ExprVisitor) {
        visitor.visit_number(self);
    }
}

impl Expr for Binary {
    fn accept(&self, visitor: &mut dyn ExprVisitor) {
        visitor.visit_binary(self);
    }
}

// 不同访问者实现
struct Evaluator { result: f64 }
struct Printer { output: String }

impl ExprVisitor for Evaluator {
    fn visit_number(&mut self, n: &Number) {
        self.result = n.value;
    }
    fn visit_binary(&mut self, b: &Binary) {
        // 递归求值...
    }
}
```

### 3.4 命令模式

**场景**: 将请求封装为对象

```rust
trait Command {
    fn execute(&self);
    fn undo(&self);
}

struct InsertText {
    document: Rc<RefCell<Document>>,
    position: usize,
    text: String,
}

impl Command for InsertText {
    fn execute(&self) {
        self.document.borrow_mut().insert(self.position, &self.text);
    }

    fn undo(&self) {
        let len = self.text.len();
        self.document.borrow_mut().delete(self.position, len);
    }
}

// 命令历史
struct Editor {
    history: Vec<Box<dyn Command>>,
    document: Rc<RefCell<Document>>,
}

impl Editor {
    fn execute(&mut self, cmd: Box<dyn Command>) {
        cmd.execute();
        self.history.push(cmd);
    }

    fn undo(&mut self) {
        if let Some(cmd) = self.history.pop() {
            cmd.undo();
        }
    }
}
```

---

## 4. 并发模式

### 4.1 Actor模式

**场景**: 隔离状态的并发实体

```rust
use std::sync::mpsc::{channel, Sender};
use std::thread;

enum Message {
    Increment(u32),
    GetValue(Sender<u32>),
    Stop,
}

struct CounterActor {
    sender: Sender<Message>,
}

impl CounterActor {
    fn new() -> Self {
        let (tx, rx) = channel::<Message>();

        thread::spawn(move || {
            let mut count = 0u32;

            for msg in rx {
                match msg {
                    Message::Increment(n) => count += n,
                    Message::GetValue(reply) => { let _ = reply.send(count); }
                    Message::Stop => break,
                }
            }
        });

        Self { sender: tx }
    }

    fn increment(&self, n: u32) {
        self.sender.send(Message::Increment(n)).unwrap();
    }

    fn get_value(&self) -> u32 {
        let (tx, rx) = channel();
        self.sender.send(Message::GetValue(tx)).unwrap();
        rx.recv().unwrap()
    }
}
```

### 4.2 通道通信

**场景**: 线程间安全通信

```rust
use std::sync::mpsc;
use std::thread;

// 多生产者单消费者
let (tx, rx) = mpsc::channel();

// 多个生产者
for i in 0..5 {
    let tx = tx.clone();
    thread::spawn(move || {
        tx.send(i * i).unwrap();
    });
}

drop(tx);  // 关闭原始发送端

// 收集结果
let mut results: Vec<i32> = rx.iter().collect();
results.sort();

// async通道 (tokio)
use tokio::sync::mpsc;

let (tx, mut rx) = mpsc::channel(100);  // 有界通道

tokio::spawn(async move {
    while let Some(msg) = rx.recv().await {
        process(msg).await;
    }
});
```

### 4.3 读写锁模式

**场景**: 多读单写场景

```rust
use std::sync::RwLock;
use std::collections::HashMap;

type Cache = RwLock<HashMap<String, Vec<u8>>>;

fn get_cached(cache: &Cache, key: &str) -> Option<Vec<u8>> {
    // 多个读者可同时持有
    let read_guard = cache.read().unwrap();
    read_guard.get(key).cloned()
}  // 读锁在此释放

fn update_cache(cache: &Cache, key: String, value: Vec<u8>) {
    // 写者独占
    let mut write_guard = cache.write().unwrap();
    write_guard.insert(key, value);
}  // 写锁在此释放
```

### 4.4 工作窃取

**场景**: 任务调度优化

```rust
use rayon::prelude::*;

// 并行迭代器自动处理工作窃取
let sum: u64 = (0..1_000_000)
    .into_par_iter()
    .map(|x| x * x)
    .sum();

// 并行递归
fn parallel_merge_sort<T: Ord + Send>(data: &mut [T]) {
    if data.len() <= 1000 {
        data.sort();
        return;
    }

    let mid = data.len() / 2;
    let (left, right) = data.split_at_mut(mid);

    rayon::join(
        || parallel_merge_sort(left),
        || parallel_merge_sort(right),
    );

    // 合并...
}
```

---

## 5. 错误处理模式

### 5.1 结果传播

**场景**: 错误向上传播

```rust
use std::fs::File;
use std::io::{self, Read};

fn read_config() -> io::Result<String> {
    let mut file = File::open("config.toml")?;  // ? 传播错误
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;
    Ok(contents)
}

// 自定义错误类型
#[derive(Debug)]
enum AppError {
    Io(io::Error),
    Parse(String),
    Config(String),
}

impl From<io::Error> for AppError {
    fn from(err: io::Error) -> Self {
        AppError::Io(err)
    }
}

fn load_app() -> Result<App, AppError> {
    let config = read_config()?;  // 自动转换错误类型
    let app = parse_config(&config)?;
    Ok(app)
}
```

### 5.2 选项组合

**场景**: 处理可能缺失的值

```rust
fn find_user(id: u64) -> Option<User> { /* ... */ }
fn get_department(user: &User) -> Option<Department> { /* ... */ }
fn get_manager(dept: &Department) -> Option<Employee> { /* ... */ }

// 链式处理
let manager_name: Option<String> = find_user(42)
    .and_then(|u| get_department(&u))
    .and_then(|d| get_manager(&d))
    .map(|m| m.name);

// 提供默认值
let name = manager_name.unwrap_or_else(|| "Unknown".to_string());

// 或者使用 ? 在Option中
fn get_manager_name(user_id: u64) -> Option<String> {
    let user = find_user(user_id)?;
    let dept = get_department(&user)?;
    let manager = get_manager(&dept)?;
    Some(manager.name)
}
```

### 5.3 错误累积

**场景**: 收集多个错误

```rust
use std::collections::VecDeque;

#[derive(Debug, Default)]
struct ValidationError {
    errors: VecDeque<String>,
}

struct UserInput {
    name: String,
    email: String,
    age: u32,
}

impl UserInput {
    fn validate(&self) -> Result<(), ValidationError> {
        let mut errs = ValidationError::default();

        if self.name.is_empty() {
            errs.errors.push_back("Name is required".into());
        }
        if !self.email.contains('@') {
            errs.errors.push_back("Invalid email format".into());
        }
        if self.age < 18 {
            errs.errors.push_back("Must be 18 or older".into());
        }

        if errs.errors.is_empty() {
            Ok(())
        } else {
            Err(errs)
        }
    }
}
```

---

## 6. 性能优化模式

### 6.1 零拷贝解析

**场景**: 避免不必要的内存分配

```rust
// 使用&str而非String
struct ParsedLine<'a> {
    command: &'a str,
    args: Vec<&'a str>,
}

fn parse_line(line: &str) -> ParsedLine<'_> {
    let parts: Vec<&str> = line.split_whitespace().collect();
    ParsedLine {
        command: parts[0],
        args: parts[1..].to_vec(),
    }
}

// 使用Bytes库处理二进制数据
use bytes::Bytes;

fn process_packet(data: Bytes) -> Bytes {
    // Bytes是引用计数，clone几乎无成本
    let header = data.slice(0..4);
    let payload = data.slice(4..);
    // 无需拷贝底层数据
    payload
}
```

### 6.2 内存池

**场景**: 减少分配开销

```rust
use bumpalo::Bump;

fn process_items(items: &[Item]) -> Vec<&Result> {
    let arena = Bump::new();
    let mut results = Vec::new();

    for item in items {
        // 在arena中分配
        let result = arena.alloc(process(item));
        results.push(result);
    }

    // arena一次性释放所有内存
    results
}

// 对象池
use std::sync::Mutex;

struct Pool<T> {
    items: Mutex<Vec<T>>,
    create: fn() -> T,
}

impl<T> Pool<T> {
    fn get(&self) -> Pooled<T> {
        let item = self.items.lock().unwrap()
            .pop()
            .unwrap_or_else(self.create);
        Pooled { pool: self, item: Some(item) }
    }
}
```

### 6.3 SIMD优化

**场景**: 向量化计算

```rust
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::*;

// 自动向量化
fn sum_array(data: &[f32]) -> f32 {
    data.iter().sum()
}

// 手动SIMD (使用packed_simd或std::simd)
use std::simd::f32x4;

fn simd_sum(data: &[f32]) -> f32 {
    let mut sum = f32x4::splat(0.0);
    let chunks = data.chunks_exact(4);
    let remainder = chunks.remainder();

    for chunk in chunks {
        sum += f32x4::from_slice(chunk);
    }

    sum.horizontal_sum() + remainder.iter().sum::<f32>()
}
```

---

## 🔗 相关资源

- [Lean策略手册](./lean_tactics.md) - 形式化证明
- [对比表集合](./comparison_tables.md) - 类型系统对比
- [术语查询工具](./glossary_tool.md) - Rust术语

---

_Rust版本: 1.75+ | 最后更新: 2026-04-11_
