/// # 高级类型系统示例
/// 
/// 本文件展示 Rust 类型系统的高级特性：
/// - 泛型编程
/// - Trait 系统
/// - 关联类型
/// - 类型约束
/// - 高阶类型
/// 
/// 对应理论：类型论、子类型、特设多态

use std::fmt::Display;
use std::ops::Add;

// ============================================================
// 第一部分：泛型编程
// ============================================================

/// 泛型函数：交换两个值
fn swap<T>(a: T, b: T) -> (T, T) {
    (b, a)
}

/// 泛型结构体：点
struct Point<T> {
    x: T,
    y: T,
}

impl<T> Point<T> {
    fn new(x: T, y: T) -> Self {
        Point { x, y }
    }
    
    fn x(&self) -> &T {
        &self.x
    }
}

/// 多个泛型参数
struct Pair<T, U> {
    first: T,
    second: U,
}

fn generic_basics() {
    println!("=== 泛型基础 ===");
    
    // 泛型函数
    let (a, b) = swap(1, 2);
    println!("Swapped: ({}, {})", a, b);
    
    let (x, y) = swap("hello", "world");
    println!("Swapped: ({}, {})", x, y);
    
    // 泛型结构体
    let p1 = Point::new(5, 10);
    println!("p1.x = {}", p1.x());
    
    let p2 = Point::new(1.0, 4.0);
    println!("p2.x = {}", p2.x());
    
    // 多泛型参数
    let pair = Pair { first: 1, second: "one" };
    println!("Pair: ({}, {})", pair.first, pair.second);
    
    println!();
}

// ============================================================
// 第二部分：Trait 系统
// ============================================================

/// 定义一个 Trait
pub trait Summary {
    fn summarize(&self) -> String;
    
    // 默认实现
    fn summarize_author(&self) -> String {
        String::from("(Read more...)")
    }
}

/// 新闻文章
pub struct NewsArticle {
    pub headline: String,
    pub location: String,
    pub author: String,
    pub content: String,
}

impl Summary for NewsArticle {
    fn summarize(&self) -> String {
        format!("{}, by {} ({})", self.headline, self.author, self.location)
    }
}

/// 推文
pub struct Tweet {
    pub username: String,
    pub content: String,
    pub reply: bool,
    pub retweet: bool,
}

impl Summary for Tweet {
    fn summarize(&self) -> String {
        format!("{}: {}", self.username, self.content)
    }
    
    fn summarize_author(&self) -> String {
        format!("@ {}", self.username)
    }
}

/// Trait 作为参数
pub fn notify(item: &impl Summary) {
    println!("Breaking news! {}", item.summarize());
}

/// Trait Bound 语法
pub fn notify2<T: Summary>(item: &T) {
    println!("Breaking news! {}", item.summarize());
}

/// 多个 Trait Bound
pub fn notify3(item: &(impl Summary + Display)) {
    println!("Breaking news! {}", item.summarize());
}

fn trait_demo() {
    println!("=== Trait 系统 ===");
    
    let tweet = Tweet {
        username: String::from("horse_ebooks"),
        content: String::from("of course, as you probably already know, people"),
        reply: false,
        retweet: false,
    };
    
    println!("1 new tweet: {}", tweet.summarize());
    println!("Author: {}", tweet.summarize_author());
    
    notify(&tweet);
    
    let article = NewsArticle {
        headline: String::from("Penguins win the Stanley Cup Championship!"),
        location: String::from("Pittsburgh, PA, USA"),
        author: String::from("Iceburgh"),
        content: String::from("The Pittsburgh Penguins once again are the best hockey team in the NHL."),
    };
    
    println!("Article: {}", article.summarize());
    
    println!();
}

// ============================================================
// 第三部分：关联类型
// ============================================================

/// Iterator trait 使用关联类型
pub trait MyIterator {
    type Item;
    
    fn next(&mut self) -> Option<Self::Item>;
}

/// 自定义迭代器
struct Counter {
    count: u32,
}

impl Counter {
    fn new() -> Counter {
        Counter { count: 0 }
    }
}

impl MyIterator for Counter {
    type Item = u32;
    
    fn next(&mut self) -> Option<Self::Item> {
        if self.count < 5 {
            self.count += 1;
            Some(self.count)
        } else {
            None
        }
    }
}

fn associated_types_demo() {
    println!("=== 关联类型 ===");
    
    let mut counter = Counter::new();
    
    while let Some(num) = counter.next() {
        println!("Counter: {}", num);
    }
    
    println!();
}

// ============================================================
// 第四部分：类型约束
// ============================================================

/// 使用 where 子句的复杂约束
fn some_function<T, U>(t: &T, u: &U) -> i32
where
    T: Display + Clone,
    U: Clone + Summary,
{
    println!("t: {}", t);
    println!("u summary: {}", u.summarize());
    42
}

/// 返回实现了 Trait 的类型
fn returns_summarizable() -> impl Summary {
    Tweet {
        username: String::from("rust_language"),
        content: String::from("Rust 1.75 is out!"),
        reply: false,
        retweet: false,
    }
}

/// 条件方法实现
struct Number<T> {
    value: T,
}

impl<T> Number<T> {
    fn value(&self) -> &T {
        &self.value
    }
}

// 只有 T 实现了 PartialOrd 和 Display 才实现这个方法
impl<T: PartialOrd + Display> Number<T> {
    fn compare(&self, other: &Number<T>) -> String {
        if self.value > other.value {
            format!("{} > {}", self.value, other.value)
        } else if self.value < other.value {
            format!("{} < {}", self.value, other.value)
        } else {
            format!("{} = {}", self.value, other.value)
        }
    }
}

fn constraints_demo() {
    println!("=== 类型约束 ===");
    
    let num1 = Number { value: 10 };
    let num2 = Number { value: 20 };
    
    println!("{}", num1.compare(&num2));
    
    let summarizable = returns_summarizable();
    println!("{}", summarizable.summarize());
    
    println!();
}

// ============================================================
// 第五部分：运算符重载
// ============================================================

/// 自定义类型实现 Add trait
#[derive(Debug, Copy, Clone, PartialEq)]
struct Millimeters(u32);

#[derive(Debug, Copy, Clone, PartialEq)]
struct Meters(u32);

impl Add<Meters> for Millimeters {
    type Output = Millimeters;
    
    fn add(self, other: Meters) -> Millimeters {
        Millimeters(self.0 + (other.0 * 1000))
    }
}

/// 为自定义类型实现运算符
#[derive(Debug)]
struct Complex {
    real: f64,
    imag: f64,
}

impl Add for Complex {
    type Output = Complex;
    
    fn add(self, other: Complex) -> Complex {
        Complex {
            real: self.real + other.real,
            imag: self.imag + other.imag,
        }
    }
}

fn operator_overloading() {
    println!("=== 运算符重载 ===");
    
    let mm = Millimeters(500);
    let m = Meters(2);
    
    let result = mm + m;
    println!("500mm + 2m = {}mm", result.0);
    
    let c1 = Complex { real: 1.0, imag: 2.0 };
    let c2 = Complex { real: 3.0, imag: 4.0 };
    let c3 = c1 + c2;
    
    println!("Complex: {:?} + {:?} = {:?}", 
        Complex { real: 1.0, imag: 2.0 },
        Complex { real: 3.0, imag: 4.0 },
        c3);
    
    println!();
}

// ============================================================
// 第六部分：高级 Trait 技巧
// ============================================================

/// 完全限定语法
trait Animal {
    fn baby_name() -> String;
}

struct Dog;

impl Dog {
    fn baby_name() -> String {
        String::from("Spot")
    }
}

impl Animal for Dog {
    fn baby_name() -> String {
        String::from("puppy")
    }
}

/// Supertrait
trait PrettyPrint: Display {
    fn pretty_print(&self) {
        println!("*** {} ***", self);
    }
}

impl PrettyPrint for i32 {}

/// Newtype 模式
struct Wrapper(Vec<String>);

impl Display for Wrapper {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "[{}]", self.0.join(", "))
    }
}

fn advanced_traits() {
    println!("=== 高级 Trait 技巧 ===");
    
    // 完全限定语法
    println!("A baby dog is called a {}", <Dog as Animal>::baby_name());
    println!("Direct call: {}", Dog::baby_name());
    
    // Supertrait
    let num = 42;
    num.pretty_print();
    
    // Newtype 模式
    let w = Wrapper(vec![String::from("hello"), String::from("world")]);
    println!("Wrapper: {}", w);
    
    println!();
}

// ============================================================
// 第七部分：类型级编程
// ============================================================

/// 使用泛型进行类型级编程
struct TypeHolder<T>(std::marker::PhantomData<T>);

impl<T> TypeHolder<T> {
    fn new() -> Self {
        TypeHolder(std::marker::PhantomData)
    }
    
    fn type_name(&self) -> &'static str {
        std::any::type_name::<T>()
    }
}

/// 编译时类型检查
fn type_level_demo() {
    println!("=== 类型级编程 ===");
    
    let int_holder = TypeHolder::<i32>::new();
    let string_holder = TypeHolder::<String>::new();
    
    println!("Type: {}", int_holder.type_name());
    println!("Type: {}", string_holder.type_name());
    
    println!();
}

// ============================================================
// 主函数
// ============================================================

fn main() {
    println!("╔══════════════════════════════════════════════════════════╗");
    println!("║          Rust 高级类型系统示例                            ║");
    println!("╚══════════════════════════════════════════════════════════╝\n");
    
    generic_basics();
    trait_demo();
    associated_types_demo();
    constraints_demo();
    operator_overloading();
    advanced_traits();
    type_level_demo();
    
    println!("╔══════════════════════════════════════════════════════════╗");
    println!("║          所有示例运行完成！                               ║");
    println!("╚══════════════════════════════════════════════════════════╝");
}

/*
输出说明：

编译和运行：
```bash
rustc --edition 2021 type_system.rs -o type_system
./type_system
```

预期输出：
```
╔══════════════════════════════════════════════════════════╗
║          Rust 高级类型系统示例                            ║
╚══════════════════════════════════════════════════════════╝

=== 泛型基础 ===
Swapped: (2, 1)
Swapped: (world, hello)
p1.x = 5
p2.x = 1
Pair: (1, one)

=== Trait 系统 ===
1 new tweet: horse_ebooks: of course, as you probably already know, people
Author: @ horse_ebooks
Breaking news! horse_ebooks: of course, as you probably already know, people
Article: Penguins win the Stanley Cup Championship!, by Iceburgh (Pittsburgh, PA, USA)

=== 关联类型 ===
Counter: 1
Counter: 2
Counter: 3
Counter: 4
Counter: 5

=== 类型约束 ===
10 < 20
rust_language: Rust 1.75 is out!

=== 运算符重载 ===
500mm + 2m = 2500mm
Complex: Complex { real: 1.0, imag: 2.0 } + Complex { real: 3.0, imag: 4.0 } = Complex { real: 4.0, imag: 6.0 }

=== 高级 Trait 技巧 ===
A baby dog is called a puppy
Direct call: Spot
*** 42 ***
Wrapper: [hello, world]

=== 类型级编程 ===
Type: i32
Type: alloc::string::String

╔══════════════════════════════════════════════════════════╗
║          所有示例运行完成！                               ║
╚══════════════════════════════════════════════════════════╝
```

理论对应：
- Trait 系统 ↔ 特设多态（Ad-hoc Polymorphism）
- 关联类型 ↔ 类型族（Type Families）
- 生命周期参数 ↔ 区域多态（Region Polymorphism）
- 类型约束 ↔ 限定多态（Bounded Polymorphism）
*/
