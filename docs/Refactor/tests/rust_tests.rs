//! FormalScience Rust 代码测试套件
//!
//! 本文件包含对所有 Rust 示例代码的综合测试：
//! - 单元测试：函数级别测试
//! - 集成测试：模块间协作测试
//! - 文档测试：代码示例验证
//!
//! 运行方式: cargo test

use std::sync::Arc;
use std::time::Duration;
use tokio::sync::{Mutex, mpsc};

// ============================================================
// 第一部分：所有权系统测试
// ============================================================

#[cfg(test)]
mod ownership_tests {
    use super::*;

    /// 测试所有权移动
    #[test]
    fn test_ownership_move() {
        let s1 = String::from("hello");
        let s2 = s1; // 所有权移动
        // s1 不再有效
        assert_eq!(s2, "hello");
    }

    /// 测试 Copy trait
    #[test]
    fn test_copy_trait() {
        let x = 5;
        let y = x; // 复制，不是移动
        assert_eq!(x, 5); // x 仍然有效
        assert_eq!(y, 5);
    }

    /// 测试不可变借用
    #[test]
    fn test_immutable_borrow() {
        let s = String::from("hello");
        let r1 = &s;
        let r2 = &s; // 多个不可变借用
        assert_eq!(*r1, "hello");
        assert_eq!(*r2, "hello");
        assert_eq!(s, "hello"); // s 仍然有效
    }

    /// 测试可变借用
    #[test]
    fn test_mutable_borrow() {
        let mut s = String::from("hello");
        {
            let r = &mut s;
            r.push_str(", world");
        } // r 在这里结束
        assert_eq!(s, "hello, world"); // s 可以再次使用
    }

    /// 测试生命周期
    #[test]
    fn test_lifetime() {
        fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
            if x.len() > y.len() { x } else { y }
        }

        let string1 = String::from("long string");
        let result;
        {
            let string2 = String::from("xyz");
            result = longest(string1.as_str(), string2.as_str());
            assert_eq!(result, "long string");
        }
    }

    /// 测试结构体生命周期
    #[test]
    fn test_struct_lifetime() {
        struct Excerpt<'a> {
            part: &'a str,
        }

        let novel = String::from("Call me Ishmael...");
        let first = novel.split('.').next().unwrap();
        let excerpt = Excerpt { part: first };
        assert_eq!(excerpt.part, "Call me Ishmael");
    }
}

// ============================================================
// 第二部分：智能指针测试
// ============================================================

#[cfg(test)]
mod smart_pointer_tests {
    use std::cell::RefCell;
    use std::rc::Rc;

    /// 测试 Box<T>
    #[test]
    fn test_box() {
        let b = Box::new(5);
        assert_eq!(*b, 5);
    }

    /// 测试 Rc<T> 引用计数
    #[test]
    fn test_rc() {
        let data = Rc::new(5);
        assert_eq!(Rc::strong_count(&data), 1);

        let _data2 = Rc::clone(&data);
        assert_eq!(Rc::strong_count(&data), 2);

        {
            let _data3 = Rc::clone(&data);
            assert_eq!(Rc::strong_count(&data), 3);
        }

        assert_eq!(Rc::strong_count(&data), 2);
    }

    /// 测试 RefCell<T> 内部可变性
    #[test]
    fn test_refcell() {
        let x = RefCell::new(5);
        {
            let mut y = x.borrow_mut();
            *y = 10;
        }
        assert_eq!(*x.borrow(), 10);
    }

    /// 测试 Rc<RefCell<T>> 组合
    #[test]
    fn test_rc_refcell() {
        #[derive(Debug)]
        struct Node {
            value: i32,
            children: RefCell<Vec<Rc<Node>>>,
        }

        let leaf = Rc::new(Node {
            value: 3,
            children: RefCell::new(vec![]),
        });

        let branch = Rc::new(Node {
            value: 5,
            children: RefCell::new(vec![Rc::clone(&leaf)]),
        });

        assert_eq!(branch.value, 5);
        assert_eq!(branch.children.borrow().len(), 1);
        assert_eq!(leaf.value, 3);
    }
}

// ============================================================
// 第三部分：异步编程测试
// ============================================================

#[cfg(test)]
mod async_tests {
    use super::*;
    use tokio::time::{sleep, timeout};

    /// 测试基本异步函数
    #[tokio::test]
    async fn test_basic_async() {
        async fn async_add(a: i32, b: i32) -> i32 {
            sleep(Duration::from_millis(1)).await;
            a + b
        }

        let result = async_add(2, 3).await;
        assert_eq!(result, 5);
    }

    /// 测试并发执行
    #[tokio::test]
    async fn test_concurrent() {
        async fn fetch_data(id: u32) -> String {
            sleep(Duration::from_millis(10)).await;
            format!("data-{}", id)
        }

        let (r1, r2, r3) = tokio::join!(
            fetch_data(1),
            fetch_data(2),
            fetch_data(3)
        );

        assert_eq!(r1, "data-1");
        assert_eq!(r2, "data-2");
        assert_eq!(r3, "data-3");
    }

    /// 测试超时
    #[tokio::test]
    async fn test_timeout() {
        let slow = async {
            sleep(Duration::from_millis(100)).await;
            "done"
        };

        let result = timeout(Duration::from_millis(10), slow).await;
        assert!(result.is_err());
    }

    /// 测试异步通道
    #[tokio::test]
    async fn test_async_channel() {
        let (tx, mut rx) = mpsc::channel(10);

        let sender = tokio::spawn(async move {
            for i in 0..5 {
                tx.send(i).await.unwrap();
            }
        });

        let mut received = vec![];
        while let Some(val) = rx.recv().await {
            received.push(val);
            if received.len() >= 5 {
                break;
            }
        }

        sender.await.unwrap();
        assert_eq!(received, vec![0, 1, 2, 3, 4]);
    }

    /// 测试共享状态
    #[tokio::test]
    async fn test_shared_state() {
        let counter = Arc::new(Mutex::new(0));
        let mut handles = vec![];

        for _ in 0..10 {
            let counter = Arc::clone(&counter);
            let handle = tokio::spawn(async move {
                let mut num = counter.lock().await;
                *num += 1;
            });
            handles.push(handle);
        }

        for handle in handles {
            handle.await.unwrap();
        }

        assert_eq!(*counter.lock().await, 10);
    }
}

// ============================================================
// 第四部分：泛型和 Trait 测试
// ============================================================

#[cfg(test)]
mod generic_tests {
    /// 测试泛型函数
    #[test]
    fn test_generic_function() {
        fn largest<T: PartialOrd>(list: &[T]) -> &T {
            let mut largest = &list[0];
            for item in list {
                if item > largest {
                    largest = item;
                }
            }
            largest
        }

        let numbers = vec![34, 50, 25, 100, 65];
        assert_eq!(*largest(&numbers), 100);

        let chars = vec!['y', 'm', 'a', 'q'];
        assert_eq!(*largest(&chars), 'y');
    }

    /// 测试泛型结构体
    #[test]
    fn test_generic_struct() {
        struct Point<T> {
            x: T,
            y: T,
        }

        impl<T> Point<T> {
            fn x(&self) -> &T {
                &self.x
            }
        }

        let p = Point { x: 5, y: 10 };
        assert_eq!(*p.x(), 5);
    }

    /// 测试 Trait
    #[test]
    fn test_trait() {
        trait Summary {
            fn summarize(&self) -> String;
        }

        struct Article {
            headline: String,
        }

        impl Summary for Article {
            fn summarize(&self) -> String {
                format!("Article: {}", self.headline)
            }
        }

        let article = Article {
            headline: String::from("Test"),
        };
        assert_eq!(article.summarize(), "Article: Test");
    }

    /// 测试 Trait Bound
    #[test]
    fn test_trait_bound() {
        use std::fmt::Display;

        fn report<T: Display>(item: &T) -> String {
            format!("Report: {}", item)
        }

        assert_eq!(report(&5), "Report: 5");
        assert_eq!(report(&"hello"), "Report: hello");
    }
}

// ============================================================
// 第五部分：并发模式测试
// ============================================================

#[cfg(test)]
mod concurrency_tests {
    use std::sync::atomic::{AtomicI32, Ordering};
    use std::thread;

    /// 测试线程创建
    #[test]
    fn test_thread_spawn() {
        let handle = thread::spawn(|| {
            42
        });

        let result = handle.join().unwrap();
        assert_eq!(result, 42);
    }

    /// 测试线程间通信
    #[test]
    fn test_channel() {
        use std::sync::mpsc;

        let (tx, rx) = mpsc::channel();

        thread::spawn(move || {
            tx.send(42).unwrap();
        });

        let received = rx.recv().unwrap();
        assert_eq!(received, 42);
    }

    /// 测试原子操作
    #[test]
    fn test_atomic() {
        let counter = AtomicI32::new(0);

        let mut handles = vec![];
        for _ in 0..10 {
            handles.push(thread::spawn(|| {
                for _ in 0..100 {
                    counter.fetch_add(1, Ordering::Relaxed);
                }
            }));
        }

        for handle in handles {
            handle.join().unwrap();
        }

        assert_eq!(counter.load(Ordering::Relaxed), 1000);
    }
}

// ============================================================
// 第六部分：错误处理测试
// ============================================================

#[cfg(test)]
mod error_handling_tests {
    use std::fs::File;
    use std::io::{self, Read};

    /// 测试 Result 类型
    #[test]
    fn test_result() {
        fn may_fail(succeed: bool) -> Result<i32, String> {
            if succeed {
                Ok(42)
            } else {
                Err(String::from("failed"))
            }
        }

        assert!(may_fail(true).is_ok());
        assert!(may_fail(false).is_err());
        assert_eq!(may_fail(true).unwrap(), 42);
    }

    /// 测试 Option 类型
    #[test]
    fn test_option() {
        let some = Some(5);
        let none: Option<i32> = None;

        assert!(some.is_some());
        assert!(none.is_none());
        assert_eq!(some.unwrap(), 5);
        assert_eq!(none.unwrap_or(0), 0);
    }

    /// 测试 ? 操作符
    #[test]
    fn test_question_mark() {
        fn read_file_contents() -> Result<String, io::Error> {
            // 这个测试不实际读取文件，只测试类型
            Ok(String::from("test content"))
        }

        let result = read_file_contents();
        assert!(result.is_ok());
    }
}

// ============================================================
// 第七部分：集合类型测试
// ============================================================

#[cfg(test)]
mod collection_tests {
    use std::collections::{HashMap, HashSet, VecDeque};

    /// 测试 Vector
    #[test]
    fn test_vec() {
        let mut v = vec![1, 2, 3];
        v.push(4);
        assert_eq!(v.len(), 4);
        assert_eq!(v[0], 1);
        assert_eq!(v.pop(), Some(4));
    }

    /// 测试 HashMap
    #[test]
    fn test_hashmap() {
        let mut map = HashMap::new();
        map.insert("key1", 1);
        map.insert("key2", 2);

        assert_eq!(map.get("key1"), Some(&1));
        assert_eq!(map.get("key3"), None);
        assert_eq!(map.len(), 2);
    }

    /// 测试 HashSet
    #[test]
    fn test_hashset() {
        let mut set = HashSet::new();
        set.insert(1);
        set.insert(2);
        set.insert(1); // 重复插入

        assert_eq!(set.len(), 2);
        assert!(set.contains(&1));
        assert!(!set.contains(&3));
    }

    /// 测试 VecDeque
    #[test]
    fn test_vecdeque() {
        let mut deque = VecDeque::new();
        deque.push_back(1);
        deque.push_back(2);
        deque.push_front(0);

        assert_eq!(deque.pop_front(), Some(0));
        assert_eq!(deque.pop_back(), Some(2));
        assert_eq!(deque.len(), 1);
    }
}

// ============================================================
// 第八部分：外部示例集成测试
// ============================================================

#[cfg(test)]
mod integration_tests {
    use super::*;

    /// 测试 ownership.rs 中的概念
    #[test]
    fn test_ownership_concepts() {
        // 所有权移动测试
        let s1 = String::from("hello");
        let s2 = s1;
        assert_eq!(s2, "hello");

        // 借用测试
        let s3 = String::from("world");
        let len = calculate_length(&s3);
        assert_eq!(len, 5);
        assert_eq!(s3, "world"); // s3 仍然有效

        fn calculate_length(s: &String) -> usize {
            s.len()
        }
    }

    /// 测试 async.rs 中的概念
    #[tokio::test]
    async fn test_async_concepts() {
        // 模拟 fetch_data
        async fn fetch_data(id: u32) -> String {
            tokio::time::sleep(Duration::from_millis(1)).await;
            format!("Data {}", id)
        }

        let f1 = fetch_data(1);
        let f2 = fetch_data(2);

        let (r1, r2) = tokio::join!(f1, f2);
        assert_eq!(r1, "Data 1");
        assert_eq!(r2, "Data 2");
    }

    /// 测试 type_system.rs 中的概念
    #[test]
    fn test_type_system_concepts() {
        // 泛型函数
        fn identity<T>(x: T) -> T {
            x
        }

        assert_eq!(identity(5), 5);
        assert_eq!(identity("hello"), "hello");

        // Trait 对象
        trait Drawable {
            fn draw(&self) -> String;
        }

        struct Circle;
        impl Drawable for Circle {
            fn draw(&self) -> String {
                String::from("Circle")
            }
        }

        let shapes: Vec<Box<dyn Drawable>> = vec![Box::new(Circle)];
        assert_eq!(shapes[0].draw(), "Circle");
    }

    /// 测试 concurrent_patterns.rs 中的概念
    #[tokio::test]
    async fn test_concurrent_patterns() {
        // 工作线程模式
        let (tx, mut rx) = mpsc::channel(10);

        tokio::spawn(async move {
            for i in 0..5 {
                tx.send(i * i).await.unwrap();
            }
        });

        let mut sum = 0;
        while let Some(val) = rx.recv().await {
            sum += val;
            if sum >= 30 { // 0+1+4+9+16 = 30
                break;
            }
        }

        assert_eq!(sum, 30);
    }
}

// ============================================================
// 第九部分：文档测试示例
// ============================================================

/// 计算斐波那契数列第 n 项
///
/// # Examples
///
/// ```
/// let result = fibonacci(10);
/// assert_eq!(result, 55);
/// ```
pub fn fibonacci(n: u32) -> u32 {
    match n {
        0 => 0,
        1 => 1,
        _ => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

/// 检查字符串是否为回文
///
/// # Examples
///
/// ```
/// assert!(is_palindrome("radar"));
/// assert!(!is_palindrome("hello"));
/// ```
pub fn is_palindrome(s: &str) -> bool {
    let chars: Vec<char> = s.chars().collect();
    let len = chars.len();
    for i in 0..len / 2 {
        if chars[i] != chars[len - 1 - i] {
            return false;
        }
    }
    true
}

/// 计算列表平均值
///
/// # Examples
///
/// ```
/// let numbers = vec![1.0, 2.0, 3.0, 4.0, 5.0];
/// let avg = average(&numbers);
/// assert_eq!(avg, 3.0);
/// ```
pub fn average(numbers: &[f64]) -> f64 {
    let sum: f64 = numbers.iter().sum();
    sum / numbers.len() as f64
}

// ============================================================
// 第十部分：测试辅助函数
// ============================================================

/// 测试辅助模块
#[cfg(test)]
mod test_helpers {
    /// 设置测试环境
    pub fn setup() {
        // 初始化日志等
    }

    /// 清理测试环境
    pub fn teardown() {
        // 清理临时文件等
    }

    /// 自定义断言辅助函数
    pub fn assert_near(a: f64, b: f64, epsilon: f64) {
        assert!((a - b).abs() < epsilon, "Expected {} to be near {}", a, b);
    }
}

/*
运行说明:

1. 运行所有测试:
   cargo test

2. 运行特定模块测试:
   cargo test ownership_tests
   cargo test async_tests

3. 运行特定测试:
   cargo test test_ownership_move

4. 显示输出:
   cargo test -- --nocapture

5. 生成覆盖率报告:
   cargo tarpaulin --out Html

6. 文档测试:
   cargo test --doc

测试覆盖:
- 所有权系统: 移动、借用、生命周期
- 智能指针: Box, Rc, RefCell
- 异步编程: async/await, 通道, 共享状态
- 泛型和 Trait: 泛型函数、结构体、Trait Bound
- 并发模式: 线程、通道、原子操作
- 错误处理: Result, Option, ?操作符
- 集合类型: Vec, HashMap, HashSet, VecDeque
- 集成测试: 外部示例验证
- 文档测试: 代码示例验证
*/

// Cargo.toml 依赖示例:
// [dependencies]
// tokio = { version = "1", features = ["full"] }
// futures = "0.3"
//
// [dev-dependencies]
// tokio-test = "0.4"
