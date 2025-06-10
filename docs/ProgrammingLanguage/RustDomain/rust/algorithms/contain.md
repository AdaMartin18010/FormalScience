# Rust容器类型详解

Rust提供了丰富的容器类型，每种容器都有其特定的用途和性能特点。
下面我将按照不同的分类详细解释这些容器类型，并提供使用案例。

## 目录

- [Rust容器类型详解](#rust容器类型详解)
  - [目录](#目录)
  - [一、序列容器](#一序列容器)
    - [1. `Vec<T>` - 动态数组](#1-vect---动态数组)
    - [2. `VecDeque<T>` - 双端队列](#2-vecdequet---双端队列)
    - [3. `LinkedList<T>` - 双向链表](#3-linkedlistt---双向链表)
  - [二、关联容器](#二关联容器)
    - [1. HashMap\<K, V\> - 哈希映射](#1-hashmapk-v---哈希映射)
    - [2. BTreeMap\<K, V\> - 有序映射](#2-btreemapk-v---有序映射)
    - [3. `HashSet<T>` - 哈希集合](#3-hashsett---哈希集合)
    - [4. `BTreeSet<T>` - 有序集合](#4-btreesett---有序集合)
  - [三、特殊容器](#三特殊容器)
    - [1. `BinaryHeap<T>` - 二叉堆（优先队列）](#1-binaryheapt---二叉堆优先队列)
    - [2. String - 字符串](#2-string---字符串)
  - [四、智能指针容器](#四智能指针容器)
    - [1. `Box<T>` - 堆分配值](#1-boxt---堆分配值)
    - [2. `Rc<T>` - 引用计数指针](#2-rct---引用计数指针)
    - [3. `Arc<T>` - 原子引用计数指针](#3-arct---原子引用计数指针)
    - [4. `Cell<T>` 和 `RefCell<T>` - 内部可变性](#4-cellt-和-refcellt---内部可变性)
  - [五、并发容器](#五并发容器)
    - [1. `Mutex<T>` - 互斥锁](#1-mutext---互斥锁)
    - [2. `RwLock<T>` - 读写锁](#2-rwlockt---读写锁)
    - [3. `Atomic`类型](#3-atomic类型)
  - [六、特殊用途容器](#六特殊用途容器)
    - [1. `Option<T>` - 可选值](#1-optiont---可选值)
    - [2. `Result<T, E>` - 成功或错误](#2-resultt-e---成功或错误)
  - [容器类型使用规范与用途总结](#容器类型使用规范与用途总结)
  - [选择容器的一般原则](#选择容器的一般原则)
  - [各容器类型的最佳用途](#各容器类型的最佳用途)
  - [容器性能比较](#容器性能比较)
  - [内存使用考虑](#内存使用考虑)
  - [最佳实践](#最佳实践)

## 一、序列容器

### 1. `Vec<T>` - 动态数组

```rust
// 创建与初始化
let mut numbers: Vec<i32> = Vec::new();
let mut numbers = vec![1, 2, 3, 4, 5];  // 使用宏创建
let zeros = vec![0; 10];  // 创建10个0

// 常用操作
numbers.push(6);  // 添加元素
numbers.pop();    // 移除并返回最后一个元素
numbers.insert(1, 10);  // 在索引1处插入10
numbers.remove(2);  // 移除索引2处的元素
numbers.clear();    // 清空向量

// 访问元素
let third = numbers[2];  // 索引访问（越界会panic）
let third = numbers.get(2);  // 返回Option<&T>

// 迭代
for num in &numbers {
    println!("{}", num);
}

// 容量管理
numbers.reserve(10);  // 预留空间
numbers.shrink_to_fit();  // 收缩到实际大小
```

**使用场景**：

- 需要动态增长的集合
- 需要随机访问元素
- 需要在末尾频繁添加/删除元素
- 作为栈使用

### 2. `VecDeque<T>` - 双端队列

```rust
use std::collections::VecDeque;

// 创建
let mut queue: VecDeque<i32> = VecDeque::new();
let mut queue = VecDeque::from(vec![1, 2, 3]);

// 双端操作
queue.push_back(4);   // 在尾部添加
queue.push_front(0);  // 在头部添加
let first = queue.pop_front();  // 从头部移除
let last = queue.pop_back();    // 从尾部移除

// 其他操作
queue.insert(1, 10);  // 在索引1处插入
queue.remove(2);      // 移除索引2处的元素
queue.swap(0, 1);     // 交换两个索引的元素

// 旋转
queue.rotate_left(2);  // 左旋2个位置
queue.rotate_right(1); // 右旋1个位置
```

**使用场景**：

- 实现队列（FIFO）或双端队列
- 需要在两端高效添加/删除元素
- 实现缓冲区
- 滑动窗口算法

### 3. `LinkedList<T>` - 双向链表

```rust
use std::collections::LinkedList;

// 创建
let mut list: LinkedList<i32> = LinkedList::new();
let mut list = LinkedList::from([1, 2, 3]);

// 操作
list.push_back(4);    // 在尾部添加
list.push_front(0);   // 在头部添加
let first = list.pop_front();  // 从头部移除
let last = list.pop_back();    // 从尾部移除

// 拆分与合并
let mut other = list.split_off(2);  // 从索引2处拆分
list.append(&mut other);  // 合并两个链表

// 迭代
for item in &list {
    println!("{}", item);
}
```

**使用场景**：

- 需要在任意位置频繁插入/删除元素
- 实现需要频繁拆分/合并的数据结构
- 不需要随机访问的场景

## 二、关联容器

### 1. HashMap<K, V> - 哈希映射

```rust
use std::collections::HashMap;

// 创建
let mut scores: HashMap<String, i32> = HashMap::new();
let mut scores = HashMap::from([
    ("Blue".to_string(), 10),
    ("Red".to_string(), 50),
]);

// 插入与更新
scores.insert("Yellow".to_string(), 30);
scores.entry("Blue".to_string()).or_insert(15);  // 不存在时插入
*scores.entry("Blue".to_string()).or_insert(0) += 5;  // 更新现有值

// 访问
let blue_score = scores.get("Blue");  // 返回Option<&V>
if let Some(score) = scores.get_mut("Blue") {
    *score += 10;  // 修改值
}

// 删除
scores.remove("Red");

// 迭代
for (key, value) in &scores {
    println!("{}: {}", key, value);
}

// 容量管理
scores.reserve(10);
scores.shrink_to_fit();
```

**使用场景**：

- 需要键值对映射
- 需要快速查找、插入和删除
- 缓存实现
- 计数器和频率统计

### 2. BTreeMap<K, V> - 有序映射

```rust
use std::collections::BTreeMap;

// 创建
let mut map: BTreeMap<i32, &str> = BTreeMap::new();
let mut map = BTreeMap::from([
    (1, "one"),
    (2, "two"),
    (3, "three"),
]);

// 插入与访问
map.insert(4, "four");
let value = map.get(&2);

// 范围操作
for (key, value) in map.range(1..3) {
    println!("{}: {}", key, value);
}

// 查找操作
if let Some((key, value)) = map.first_key_value() {
    println!("First: {} = {}", key, value);
}
if let Some((key, value)) = map.last_key_value() {
    println!("Last: {} = {}", key, value);
}

// 分割
let mut upper = map.split_off(&3);  // 键>=3的部分
```

**使用场景**：

- 需要按键排序的映射
- 需要范围查询
- 需要找到最大/最小键
- 内存受限环境（比HashMap更节省空间）

### 3. `HashSet<T>` - 哈希集合

```rust
use std::collections::HashSet;

// 创建
let mut set: HashSet<i32> = HashSet::new();
let mut set = HashSet::from([1, 2, 3, 4]);

// 添加与删除
set.insert(5);
set.remove(&1);

// 查询
if set.contains(&3) {
    println!("包含3");
}

// 集合操作
let mut set2 = HashSet::from([3, 4, 5, 6]);
let union: HashSet<_> = set.union(&set2).cloned().collect();  // 并集
let intersection: HashSet<_> = set.intersection(&set2).cloned().collect();  // 交集
let difference: HashSet<_> = set.difference(&set2).cloned().collect();  // 差集
let sym_difference: HashSet<_> = set.symmetric_difference(&set2).cloned().collect();  // 对称差

// 子集与相等性
if set.is_subset(&union) {
    println!("set是union的子集");
}
```

**使用场景**：

- 需要快速查找、插入和删除的无序集合
- 去重
- 集合运算（交集、并集等）
- 成员资格测试

### 4. `BTreeSet<T>` - 有序集合

```rust
use std::collections::BTreeSet;

// 创建
let mut set: BTreeSet<i32> = BTreeSet::new();
let mut set = BTreeSet::from([1, 2, 3, 4, 5]);

// 添加与删除
set.insert(6);
set.remove(&1);

// 范围操作
for value in set.range(2..5) {
    println!("{}", value);
}

// 查找操作
if let Some(value) = set.first() {
    println!("First: {}", value);
}
if let Some(value) = set.last() {
    println!("Last: {}", value);
}

// 分割
let mut upper = set.split_off(&4);  // 值>=4的部分
```

**使用场景**：

- 需要按值排序的集合
- 需要范围查询
- 需要找到最大/最小值
- 有序数据去重

## 三、特殊容器

### 1. `BinaryHeap<T>` - 二叉堆（优先队列）

```rust
use std::collections::BinaryHeap;

// 创建（默认为最大堆）
let mut heap: BinaryHeap<i32> = BinaryHeap::new();
let mut heap = BinaryHeap::from([1, 5, 2, 7, 3]);

// 添加与删除
heap.push(10);
let max = heap.pop();  // 移除并返回最大元素

// 查看最大元素但不移除
if let Some(max) = heap.peek() {
    println!("最大元素: {}", max);
}

// 创建最小堆（使用Reverse包装器）
use std::cmp::Reverse;
let mut min_heap = BinaryHeap::new();
min_heap.push(Reverse(5));
min_heap.push(Reverse(1));
min_heap.push(Reverse(10));
if let Some(Reverse(min)) = min_heap.pop() {
    println!("最小元素: {}", min);  // 输出1
}
```

**使用场景**：

- 优先队列实现
- 任务调度
- 图算法（如Dijkstra算法）
- 事件处理系统

### 2. String - 字符串

```rust
// 创建
let mut s = String::new();
let s = String::from("Hello");
let s = "Hello".to_string();

// 添加内容
s.push('!');  // 添加单个字符
s.push_str(", world");  // 添加字符串
s += " and everyone";  // 使用+=运算符

// 连接
let s1 = String::from("Hello, ");
let s2 = String::from("world!");
let s3 = s1 + &s2;  // s1被移动

// 格式化
let s = format!("{} {}!", "Hello", "world");

// 切片
let hello = &s[0..5];

// 迭代
for c in s.chars() {
    println!("{}", c);
}
for b in s.bytes() {
    println!("{}", b);
}
```

**使用场景**：

- 文本处理
- 动态构建字符串
- 国际化文本（UTF-8编码）

## 四、智能指针容器

### 1. `Box<T>` - 堆分配值

```rust
// 创建
let b = Box::new(5);
let b = Box::new(vec![1, 2, 3]);

// 递归数据结构
enum List {
    Cons(i32, Box<List>),
    Nil,
}
use List::{Cons, Nil};
let list = Cons(1, Box::new(Cons(2, Box::new(Cons(3, Box::new(Nil))))));

// 解引用
let value = *b;  // 如果T实现了Copy trait
```

**使用场景**：

- 编译时大小未知的类型
- 递归数据结构
- 堆分配大对象
- 转移所有权而不是复制数据

### 2. `Rc<T>` - 引用计数指针

```rust
use std::rc::Rc;

// 创建
let data = Rc::new(vec![1, 2, 3]);

// 克隆（增加引用计数）
let data2 = Rc::clone(&data);
let data3 = data.clone();  // 同上

// 获取引用计数
println!("引用计数: {}", Rc::strong_count(&data));  // 输出3

// 访问数据
println!("第一个元素: {}", data[0]);
```

**使用场景**：

- 多所有权场景
- 缓存数据
- 实现图形结构
- 避免大数据复制

### 3. `Arc<T>` - 原子引用计数指针

```rust
use std::sync::Arc;
use std::thread;

// 创建
let data = Arc::new(vec![1, 2, 3]);

// 在多线程间共享
let data1 = Arc::clone(&data);
let thread1 = thread::spawn(move || {
    println!("线程1: {:?}", data1);
});

let data2 = Arc::clone(&data);
let thread2 = thread::spawn(move || {
    println!("线程2: {:?}", data2);
});

thread1.join().unwrap();
thread2.join().unwrap();
```

**使用场景**：

- 线程间共享不可变数据
- 实现线程安全的缓存
- 并发数据结构

### 4. `Cell<T>` 和 `RefCell<T>` - 内部可变性

```rust
use std::cell::{Cell, RefCell};

// Cell - 适用于Copy类型
let cell = Cell::new(10);
cell.set(20);
let value = cell.get();  // 获取值的副本

// RefCell - 适用于任何类型
let ref_cell = RefCell::new(vec![1, 2, 3]);
ref_cell.borrow_mut().push(4);  // 可变借用
let v = ref_cell.borrow();  // 不可变借用
println!("长度: {}", v.len());
```

**使用场景**：

- 在不可变引用中修改数据
- 实现内部可变性模式
- 实现自引用数据结构
- 模拟垃圾回收行为

## 五、并发容器

### 1. `Mutex<T>` - 互斥锁

```rust
use std::sync::{Mutex, Arc};
use std::thread;

// 创建
let counter = Arc::new(Mutex::new(0));

// 在多线程中使用
let mut handles = vec![];
for _ in 0..10 {
    let counter = Arc::clone(&counter);
    let handle = thread::spawn(move || {
        let mut num = counter.lock().unwrap();
        *num += 1;
    });
    handles.push(handle);
}

// 等待所有线程完成
for handle in handles {
    handle.join().unwrap();
}

println!("结果: {}", *counter.lock().unwrap());
```

**使用场景**：

- 线程间共享可变数据
- 实现线程安全的数据结构
- 资源互斥访问

### 2. `RwLock<T>` - 读写锁

```rust
use std::sync::{RwLock, Arc};
use std::thread;

// 创建
let data = Arc::new(RwLock::new(vec![1, 2, 3]));

// 读取线程
let data1 = Arc::clone(&data);
let reader = thread::spawn(move || {
    let values = data1.read().unwrap();
    println!("读取: {:?}", *values);
});

// 写入线程
let data2 = Arc::clone(&data);
let writer = thread::spawn(move || {
    let mut values = data2.write().unwrap();
    values.push(4);
    println!("写入后: {:?}", *values);
});

reader.join().unwrap();
writer.join().unwrap();
```

**使用场景**：

- 读多写少的并发场景
- 实现线程安全的缓存
- 数据库连接池

### 3. `Atomic`类型

```rust
use std::sync::atomic::{AtomicI32, Ordering};
use std::sync::Arc;
use std::thread;

// 创建
let counter = Arc::new(AtomicI32::new(0));

// 在多线程中使用
let mut handles = vec![];
for _ in 0..10 {
    let counter = Arc::clone(&counter);
    let handle = thread::spawn(move || {
        counter.fetch_add(1, Ordering::SeqCst);
    });
    handles.push(handle);
}

// 等待所有线程完成
for handle in handles {
    handle.join().unwrap();
}

println!("结果: {}", counter.load(Ordering::SeqCst));
```

**使用场景**：

- 无锁并发编程
- 计数器和标志位
- 高性能并发数据结构

## 六、特殊用途容器

### 1. `Option<T>` - 可选值

```rust
// 创建
let some_value = Some(42);
let no_value: Option<i32> = None;

// 模式匹配
match some_value {
    Some(value) => println!("有值: {}", value),
    None => println!("没有值"),
}

// 方法
if let Some(value) = some_value {
    println!("有值: {}", value);
}

let value = some_value.unwrap_or(0);  // 提供默认值
let value = some_value.expect("没有值!");  // 自定义panic消息

// 转换
let mapped = some_value.map(|x| x * 2);  // Option<i32> -> Option<i32>
let result = some_value.ok_or("没有值");  // Option<T> -> Result<T, E>
```

**使用场景**：

- 表示可能不存在的值
- 函数返回值可能为空
- 避免使用null

### 2. `Result<T, E>` - 成功或错误

```rust
use std::fs::File;
use std::io::{self, Read};

// 创建
let success: Result<i32, &str> = Ok(42);
let failure: Result<i32, &str> = Err("出错了");

// 模式匹配
match File::open("file.txt") {
    Ok(file) => println!("文件打开成功"),
    Err(error) => println!("打开文件失败: {}", error),
}

// 方法
let file = File::open("file.txt").unwrap();  // 失败时panic
let file = File::open("file.txt").expect("无法打开文件");  // 自定义panic消息
let file = File::open("file.txt").unwrap_or_else(|_| {
    // 创建一个默认文件
    File::open("default.txt").unwrap()
});

// 传播错误
fn read_file() -> Result<String, io::Error> {
    let mut file = File::open("file.txt")?;  // 使用?运算符
    let mut content = String::new();
    file.read_to_string(&mut content)?;
    Ok(content)
}
```

**使用场景**：

- 错误处理
- 可能失败的操作
- 函数返回值

## 容器类型使用规范与用途总结

## 选择容器的一般原则

1. **访问模式**：
   - 随机访问 → Vec
   - 两端访问 → VecDeque
   - 任意位置插入/删除 → LinkedList
   - 键值查找 → HashMap/BTreeMap
   - 集合操作 → HashSet/BTreeSet
   - 优先级访问 → BinaryHeap

2. **性能考虑**：
   - 时间复杂度：不同容器的操作复杂度不同
   - 空间效率：某些容器比其他容器更节省空间
   - 缓存友好性：连续内存布局(Vec)通常比分散布局(LinkedList)更快

3. **排序需求**：
   - 需要保持元素顺序 → Vec, VecDeque, LinkedList
   - 需要按键/值排序 → BTreeMap/BTreeSet
   - 不需要排序 → HashMap/HashSet

4. **并发需求**：
   - 单线程 → 标准容器
   - 多线程共享不可变数据 → Arc<容器>
   - 多线程共享可变数据 → Arc<Mutex<容器>> 或 Arc<RwLock<容器>>

## 各容器类型的最佳用途

| 容器类型 | 最佳用途 | 避免使用场景 |
|:----:|:----|:----|
| `Vec<T>` | 连续数据、随机访问、尾部操作 | 频繁在中间插入/删除 |
| `VecDeque<T>` | 队列、双端队列、滑动窗口 | 需要连续内存布局 |
| `LinkedList<T>` | 频繁拆分/合并、任意位置插入/删除 | 随机访问、内存受限 |
| `HashMap<K,V>` | 快速查找、无序键值对 | 需要按键排序、内存受限 |
| `BTreeMap<K,V>` | 有序键值对、范围查询 | 需要最快的单点查找 |
| `HashSet<T>` | 快速成员检查、去重 | 需要有序集合 |
| `BTreeSet<T>` | 有序集合、范围操作 | 需要最快的单点查找 |
| `BinaryHeap<T>` | 优先队列、任务调度 | 需要FIFO队列 |
| `String` | 文本处理、UTF-8字符串 | 需要固定大小字符串 |
| `Box<T>` | 堆分配、递归类型 | 小型值类型 |
| `Rc<T>` | 单线程共享所有权 | 多线程场景 |
| `Arc<T>` | 多线程共享所有权 | 单线程场景(有性能开销) |
| `Cell/RefCell` | 内部可变性(单线程) | 多线程场景 |
| `Mutex/RwLock` | 多线程可变共享 | 单线程场景(有性能开销) |

## 容器性能比较

| 操作 | Vec | VecDeque | LinkedList | HashMap | BTreeMap | HashSet | BTreeSet | BinaryHeap |
|:----:|:----|:----|:----|:----|:----|:----|:----|:----|
| 随机访问 | O(1) | O(1) | O(n) | O(1)* | O(log n) | O(1)* | O(log n) | O(1) 仅顶部 |
| 插入/删除(开头) | O(n) | O(1) | O(1) | - | - | - | - | - |
| 插入/删除(结尾) | O(1) | O(1) | O(1) | - | - | - | - | - |
| 插入/删除(中间) | O(n) | O(n) | O(1)** | - | - | - | - | - |
| 查找 | O(n) | O(n) | O(n) | O(1)* | O(log n) | O(1)* | O(log n) | O(n) |
| 最大/最小元素 | O(n) | O(n) | O(n) | O(n) | O(log n) | O(n) | O(log n) | O(1) |

*平均情况，最坏O(n)
**需要先找到位置，查找是O(n)

## 内存使用考虑

1. **内存开销**：
   - HashMap/HashSet: 有额外的哈希表开销
   - LinkedList: 每个节点有额外指针开销
   - Vec/VecDeque: 可能有未使用的容量
   - BTreeMap/BTreeSet: 节点开销相对较小

2. **内存布局**：
   - Vec: 连续内存，缓存友好
   - LinkedList: 分散内存，缓存不友好
   - HashMap/BTreeMap: 复杂内存布局

## 最佳实践

1. **默认选择Vec**：除非有特定需求，Vec通常是最佳选择
2. **基于需求选择**：根据访问模式和操作频率选择合适的容器
3. **考虑性能权衡**：时间复杂度、空间复杂度和实际性能可能不同
4. **避免过早优化**：先使用最简单的容器，有性能问题时再优化
5. **考虑数据规模**：小数据集上不同容器的性能差异可能不明显
6. **使用标准库**：尽量使用标准库容器，而不是自己实现
7. **考虑线程安全**：多线程环境下使用适当的同步机制

通过理解每种容器的特点和适用场景，你可以为你的Rust程序选择最合适的数据结构，从而获得最佳的性能和可维护性。
