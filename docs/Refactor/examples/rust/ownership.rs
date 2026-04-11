/// # 所有权系统示例
/// 
/// 本文件展示 Rust 所有权系统的核心概念：
/// - 所有权规则
/// - 借用（Borrowing）
/// - 生命周期（Lifetimes）
/// - 智能指针
/// 
/// 对应理论：线性类型论、资源管理

use std::ops::Drop;

// ============================================================
// 第一部分：所有权基础
// ============================================================

/// 演示所有权的基本规则
fn ownership_basics() {
    println!("=== 所有权基础 ===");
    
    // 规则1：每个值都有一个所有者
    let s1 = String::from("hello");  // s1 拥有这个字符串
    
    // 规则2：值只能有一个所有者
    let s2 = s1;  // 所有权从 s1 移动到 s2
    // println!("{}", s1);  // 错误！s1 不再有效
    println!("s2: {}", s2);  // 正确：s2 是现在的所有者
    
    // 规则3：所有者离开作用域，值被丢弃
    {
        let s3 = String::from("temporary");
        println!("s3 in scope: {}", s3);
    }  // s3 在这里被丢弃
    // println!("{}", s3);  // 错误！s3 已经离开作用域
    
    println!();
}

/// 演示 Copy trait
fn copy_trait_demo() {
    println!("=== Copy Trait ===");
    
    // 标量类型实现了 Copy trait
    let x = 5;
    let y = x;  // 复制，不是移动
    println!("x: {}, y: {}", x, y);  // 两者都有效
    
    // 元组（如果所有元素都实现 Copy）
    let t1 = (1, 2);
    let t2 = t1;
    println!("t1: {:?}, t2: {:?}", t1, t2);
    
    // 自定义类型默认不实现 Copy
    #[derive(Debug, Clone, Copy)]
    struct Point {
        x: i32,
        y: i32,
    }
    
    let p1 = Point { x: 1, y: 2 };
    let p2 = p1;  // 因为实现了 Copy，这是复制
    println!("p1: {:?}, p2: {:?}", p1, p2);
    
    println!();
}

// ============================================================
// 第二部分：借用（Borrowing）
// ============================================================

/// 演示不可变借用
fn immutable_borrow() {
    println!("=== 不可变借用 ===");
    
    let s = String::from("hello");
    
    // 可以同时有多个不可变借用
    let r1 = &s;
    let r2 = &s;
    
    println!("r1: {}, r2: {}", r1, r2);
    // s 仍然有效，因为我们只是借用
    println!("s still valid: {}", s);
    
    println!();
}

/// 演示可变借用
fn mutable_borrow() {
    println!("=== 可变借用 ===");
    
    let mut s = String::from("hello");
    
    // 只能有一个可变借用
    let r = &mut s;
    r.push_str(", world");
    
    // println!("{}", s);  // 错误！不能同时有可变借用和所有权访问
    
    println!("r: {}", r);
    // r 不再使用后，s 恢复所有权
    println!("s after borrow: {}", s);
    
    println!();
}

/// 演示借用规则：不能同时有可变和不可变借用
fn borrow_rules() {
    println!("=== 借用规则 ===");
    
    let mut s = String::from("hello");
    
    let r1 = &s;  // 不可变借用
    let r2 = &s;  // 另一个不可变借用（OK）
    
    println!("{} and {}", r1, r2);
    // r1 和 r2 最后一次使用后，可以创建可变借用
    
    let r3 = &mut s;  // 现在可以了
    r3.push_str("!");
    println!("r3: {}", r3);
    
    println!();
}

// ============================================================
// 第三部分：生命周期
// ============================================================

/// 显式生命周期标注
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}

fn lifetime_demo() {
    println!("=== 生命周期 ===");
    
    let string1 = String::from("long string is long");
    {
        let string2 = String::from("xyz");
        let result = longest(string1.as_str(), string2.as_str());
        println!("The longest string is '{}'", result);
    }  // string2 在这里被丢弃
    
    println!();
}

/// 结构体中的生命周期
struct ImportantExcerpt<'a> {
    part: &'a str,
}

impl<'a> ImportantExcerpt<'a> {
    fn level(&self) -> i32 {
        3
    }
    
    fn announce_and_return_part(&self, announcement: &str) -> &str {
        println!("Attention please: {}", announcement);
        self.part
    }
}

fn struct_lifetime() {
    println!("=== 结构体生命周期 ===");
    
    let novel = String::from("Call me Ishmael. Some years ago...");
    let first_sentence = novel.split('.').next().expect("Could not find a '.'");
    let i = ImportantExcerpt {
        part: first_sentence,
    };
    
    println!("Important excerpt: {}", i.part);
    println!("Level: {}", i.level());
    
    println!();
}

// ============================================================
// 第四部分：智能指针
// ============================================================

use std::rc::Rc;
use std::cell::RefCell;

/// 演示 Box<T>
fn box_demo() {
    println!("=== Box<T> ===");
    
    // Box 在堆上分配
    let b = Box::new(5);
    println!("b = {}", b);
    
    // 递归类型需要 Box
    #[derive(Debug)]
    enum List {
        Cons(i32, Box<List>),
        Nil,
    }
    
    let list = List::Cons(1, Box::new(List::Cons(2, Box::new(List::Cons(3, Box::new(List::Nil))))));
    println!("{:?}", list);
    
    println!();
}

/// 演示 Rc<T>（引用计数）
fn rc_demo() {
    println!("=== Rc<T> ===");
    
    enum List {
        Cons(i32, Rc<List>),
        Nil,
    }
    
    let a = Rc::new(List::Cons(5, Rc::new(List::Cons(10, Rc::new(List::Nil)))));
    println!("count after creating a = {}", Rc::strong_count(&a));
    
    let b = List::Cons(3, Rc::clone(&a));
    println!("count after creating b = {}", Rc::strong_count(&a));
    
    {
        let c = List::Cons(4, Rc::clone(&a));
        println!("count after creating c = {}", Rc::strong_count(&a));
        // c 在这里离开作用域
    }
    
    println!("count after c goes out of scope = {}", Rc::strong_count(&a));
    
    println!();
}

/// 演示 RefCell<T>（运行时借用检查）
fn refcell_demo() {
    println!("=== RefCell<T> ===");
    
    let x = RefCell::new(5);
    
    // 创建不可变借用
    let y = x.borrow();
    println!("y = {}", y);
    drop(y);  // 显式释放
    
    // 现在可以创建可变借用
    let mut z = x.borrow_mut();
    *z = 10;
    println!("z = {}", z);
    drop(z);
    
    println!("x = {:?}", x);
    
    println!();
}

/// 组合 Rc 和 RefCell 实现内部可变性
fn rc_refcell_demo() {
    println!("=== Rc<RefCell<T>> ===");
    
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
    
    println!("leaf parent = {:?}", leaf);
    println!("branch = {:?}", branch);
    
    println!();
}

// ============================================================
// 第五部分：自定义智能指针
// ============================================================

/// 自定义 Box 类型
struct MyBox<T>(T);

impl<T> MyBox<T> {
    fn new(x: T) -> MyBox<T> {
        MyBox(x)
    }
}

use std::ops::Deref;

impl<T> Deref for MyBox<T> {
    type Target = T;
    
    fn deref(&self) -> &T {
        &self.0
    }
}

impl<T> Drop for MyBox<T> {
    fn drop(&mut self) {
        println!("Dropping MyBox!");
    }
}

fn custom_smart_pointer() {
    println!("=== 自定义智能指针 ===");
    
    let x = 5;
    let y = MyBox::new(x);
    
    assert_eq!(5, x);
    assert_eq!(5, *y);  // 使用 Deref trait
    
    println!("MyBox created and dereferenced successfully");
    
    println!();
}

// ============================================================
// 主函数
// ============================================================

fn main() {
    println!("╔══════════════════════════════════════════════════════════╗");
    println!("║          Rust 所有权系统示例                              ║");
    println!("╚══════════════════════════════════════════════════════════╝\n");
    
    ownership_basics();
    copy_trait_demo();
    immutable_borrow();
    mutable_borrow();
    borrow_rules();
    lifetime_demo();
    struct_lifetime();
    box_demo();
    rc_demo();
    refcell_demo();
    rc_refcell_demo();
    custom_smart_pointer();
    
    println!("╔══════════════════════════════════════════════════════════╗");
    println!("║          所有示例运行完成！                               ║");
    println!("╚══════════════════════════════════════════════════════════╝");
}

/*
输出说明：

编译和运行：
```bash
rustc --edition 2021 ownership.rs -o ownership
./ownership
```

预期输出：
```
╔══════════════════════════════════════════════════════════╗
║          Rust 所有权系统示例                              ║
╚══════════════════════════════════════════════════════════╝

=== 所有权基础 ===
s2: hello

=== Copy Trait ===
x: 5, y: 5
t1: (1, 2), t2: (1, 2)
p1: Point { x: 1, y: 2 }, p2: Point { x: 1, y: 2 }

=== 不可变借用 ===
r1: hello, r2: hello
s still valid: hello

=== 可变借用 ===
r: hello, world
s after borrow: hello, world

=== 借用规则 ===
hello and hello
r3: hello!

=== 生命周期 ===
The longest string is 'long string is long'

=== 结构体生命周期 ===
Important excerpt: Call me Ishmael
Level: 3

=== Box<T> ===
b = 5
Cons(1, Cons(2, Cons(3, Nil)))

=== Rc<T> ===
count after creating a = 1
count after creating b = 2
count after creating c = 3
count after c goes out of scope = 2

=== RefCell<T> ===
y = 5
z = 10
x = RefCell { value: 10 }

=== Rc<RefCell<T>> ===
leaf parent = Node { value: 3, children: RefCell { value: [] } }
branch = Node { value: 5, children: RefCell { value: [Node { value: 3, children: RefCell { value: [] } }] } }

=== 自定义智能指针 ===
MyBox created and dereferenced successfully
Dropping MyBox!

╔══════════════════════════════════════════════════════════╗
║          所有示例运行完成！                               ║
╚══════════════════════════════════════════════════════════╝
```

理论对应：
- 所有权系统 ↔ 线性类型论（Linear Type Theory）
- 借用检查 ↔ 能力安全（Capability Safety）
- 生命周期 ↔ 区域类型论（Region-Based Memory Management）
*/
