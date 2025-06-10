# Rust 变量与类型系统

## 目录

- [Rust 变量与类型系统](#rust-变量与类型系统)
  - [目录](#目录)
  - [变量与类型的关系](#变量与类型的关系)
  - [类型的核心模型-可以理解为Rust的类型系统有那些语义model](#类型的核心模型-可以理解为rust的类型系统有那些语义model)
  - [完全的解释](#完全的解释)
  - [编译器如何查看变量](#编译器如何查看变量)
    - [静态检查（Static Checking）](#静态检查static-checking)
    - [动态行为（Dynamic Behavior）](#动态行为dynamic-behavior)
  - [总结](#总结)
  - [Rust 中的变体性与多态：关系、证明与安全保证](#rust-中的变体性与多态关系证明与安全保证)
    - [一、变体性与多态的关系](#一变体性与多态的关系)
      - [1. 基本关系](#1-基本关系)
      - [2. 具体联系](#2-具体联系)
    - [二、变体性规则的推理与证明](#二变体性规则的推理与证明)
      - [1. 协变性推理](#1-协变性推理)
      - [2. 逆变性推理](#2-逆变性推理)
      - [3. 不变性推理](#3-不变性推理)
    - [三、变体性如何保证类型安全和内存安全](#三变体性如何保证类型安全和内存安全)
      - [1. 协变与安全保证](#1-协变与安全保证)
      - [2. 逆变与安全保证](#2-逆变与安全保证)
      - [3. 不变性与安全保证](#3-不变性与安全保证)
    - [四、运行时安全与变体性](#四运行时安全与变体性)
      - [1. 防止悬垂引用](#1-防止悬垂引用)
      - [2. 防止数据竞争](#2-防止数据竞争)
      - [3. 保证 trait 对象安全](#3-保证-trait-对象安全)
    - [五、形式化证明示例](#五形式化证明示例)
      - [1. 协变安全性证明](#1-协变安全性证明)
      - [2. 逆变安全性证明](#2-逆变安全性证明)
      - [3. 不变性安全性证明](#3-不变性安全性证明)
    - [六、变体性与多态的实际应用](#六变体性与多态的实际应用)
      - [1. 构建灵活的 API](#1-构建灵活的-api)
      - [2. 实现类型安全的回调系统](#2-实现类型安全的回调系统)
      - [3. 保证容器类型的安全](#3-保证容器类型的安全)
    - [七、总结](#七总结)

## 变量与类型的关系

在 Rust 中，变量和类型之间的关系是紧密且明确的。
以下是变量与类型关系的核心内容：

1. **变量声明与类型绑定**：
   - 在 Rust 中，变量通过 `let` 关键字声明，并且每个变量都必须有一个确定的类型。类型可以显式指定，也可以由编译器推断。
   - 例如：

     ```rust
     let x: i32 = 5; // 显式指定类型
     let y = 10; // 类型由编译器推断为 i32
     ```

   - 如果变量未初始化且未显式指定类型，编译器会报错，因为它无法推断类型。

2. **类型推断**：
   - Rust 编译器会根据变量的初始值自动推断其类型。例如：

     ```rust
     let a = 3.1; // 类型推断为 f64
     let b = "hello"; // 类型推断为 &str
     ```

   - 如果变量未初始化且未显式指定类型，编译器会报错。

3. **类型的作用**：
   - 类型决定了变量的存储结构和允许的操作。例如，整数类型（如 `i32`）可以进行加减乘除等操作，而字符串类型（如 `&str`）可以进行字符串拼接等操作。
   - 类型还影响变量的内存分配和生命周期管理。

4. **变量的重新绑定与类型变化**：
   - 在 Rust 中，变量可以被重新绑定到一个新的值，甚至可以改变其类型。例如：

     ```rust
     let x: i32 = 5;
     let x = "hello"; // 重新绑定变量 x，类型从 i32 变为 &str
     ```

   - **这种重新绑定称为变量遮蔽（shadowing），它允许在同一作用域中使用同名变量，但新的变量会遮蔽旧的变量**。

## 类型的核心模型-可以理解为Rust的类型系统有那些语义model

Rust 的核心模型主要包括以下几个方面：

1. **所有权系统（Ownership System）**：
   - Rust 的所有权系统是其核心特性之一，用于管理内存的安全性。每个值都有一个所有者（owner），当所有者离开作用域时，值会被自动释放。
   - 所有权系统通过以下规则确保内存安全：
     - 每个值都有一个所有者。
     - 一个值在任何时候只能有一个所有者。
     - 当所有者离开作用域时，值会被自动释放。

2. **借用与引用（Borrowing and References）**：
   - 借用机制允许在不转移所有权的情况下访问值。借用分为不可变借用和可变借用：
     - 不可变借用：通过 `&` 创建不可变引用。
     - 可变借用：通过 `&mut` 创建可变引用。
   - 借用确保在任何时候，一个值要么有一个可变引用，要么有多个不可变引用，但不能同时存在。

3. **生命周期（Lifetimes）**：
   - 生命周期用于描述引用的有效期。Rust 编译器会自动推断引用的生命周期，确保引用在有效期内使用。
   - 例如：

     ```rust
     fn longest(s1: &str, s2: &str) -> &str {
         if s1.len() > s2.len() {
             s1
         } else {
             s2
         }
     }
     ```

     在这个例子中，`s1` 和 `s2` 的生命周期决定了返回值的生命周期。

4. **类型系统（Type System）**：
   - Rust 的类型系统是静态的，类型在编译时确定。类型系统确保变量的类型安全，防止类型不匹配的错误。
   - 类型系统还支持泛型和特性（Trait），允许编写通用和可扩展的代码。

5. **模式匹配（Pattern Matching）**：
   - 模式匹配是 Rust 的一个强大特性，用于解构复杂数据类型（如元组和枚举）。例如：

     ```rust
     let point = (3, 5);
     let (x, y) = point;
     println!("x = {}, y = {}", x, y);
     ```

     模式匹配可以将元组分解为单个元素。

## 完全的解释

Rust 的核心模型通过所有权系统、借用与引用、生命周期、类型系统和模式匹配等机制，确保了内存安全和高性能。
这些机制共同作用，使得 Rust 能够在系统编程领域提供强大的功能和安全保障。

1. **所有权系统**：
   - 所有权系统通过明确的规则管理内存，避免了垃圾回收的开销，同时防止了内存泄漏和数据竞争等问题。

2. **借用与引用**：
   - 借用机制允许在不转移所有权的情况下访问值，确保了数据的共享和安全。

3. **生命周期**：
   - 生命周期确保引用在有效期内使用，防止了悬垂引用（dangling references）等问题。

4. **类型系统**：
   - 类型系统在编译时进行类型检查，确保变量的类型安全，防止类型不匹配的错误。

5. **模式匹配**：
   - 模式匹配允许解构复杂数据类型，使得代码更加简洁和可读。

通过这些机制，Rust 能够在保证内存安全的同时，提供高性能和灵活的编程能力。

在 Rust 中，变量的定义通过 `let` 关键字完成。
变量可以声明为不可变或可变的，
并且需要在声明时进行初始化（虽然可以使用模式匹配等方式延迟初始化，但大多数情况下变量需要初始化）。

1. **不可变变量**：

   ```rust
   let x = 5; // 不可变变量，一旦赋值后不能修改
   ```

   试图修改不可变变量会导致编译错误：

   ```rust
   let x = 5;
   x = 10; // Error: re-assignment of immutable variable `x`
   ```

2. **可变变量**：

   ```rust
   let mut y = 10; // 可变变量，可以修改其值
   y = 20; // 允许修改
   ```

3. **作用域**：
   变量的作用域从声明处开始，直到包含它的代码块结束：

   ```rust
   {
       let z = 15; // 变量 z 的作用域
       println!("{}", z); // 可以访问 z
   } // z 的作用域结束，此时无法访问 z
   ```

## 编译器如何查看变量

在 Rust 中，编译器对变量的处理主要体现在**静态检查**和**动态行为**两个方面。

### 静态检查（Static Checking）

静态检查是指编译器在编译阶段对代码进行的检查，目的是确保代码的正确性。
以下是一些关于变量的静态检查：

1. **不可变性检查**：
   编译器会确保不可变变量不会被重新赋值：

   ```rust
   let x = 5; // 编译器标记 x 为不可变
   x = 10; // 编译错误：不可变变量被重新赋值
   ```

2. **作用域检查**：
   确保变量只在其作用域内使用：

   ```rust
   {
       let z = 15; // z 的作用域开始
   }
   println!("{}", z); // 编译错误：试图使用已超出作用域的变量 z
   ```

3. **类型推断与检查**：
   Rust 编译器会根据上下文推断变量的类型，并确保类型一致：

   ```rust
   let a = "hello"; // 推断为 &str 类型
   a = 10; // 编译错误：类型不匹配
   ```

4. **变量遮蔽（Shadowing）**：
   允许在同一作用域内重新声明同名变量，但编译器会确保新的变量是独立的：

   ```rust
   let x = 5; // 第一次声明
   let x = x + 1; // 第二次声明，遮蔽第一次声明的变量
   println!("{}", x); // 输出 6
   ```

### 动态行为（Dynamic Behavior）

动态行为指的是变量在运行时的行为，以下是一些关于变量的动态行为：

1. **值的存储与访问**：
   在运行时，变量的实际值存储在内存中（栈或堆），可以通过变量名访问其值。例如：

   ```rust
   let mut count = 0;
   count += 1; // 动态修改变量的值
   println!("{}", count); // 打印 1
   ```

2. **变量的生命周期**：
   变量的生命周期决定了它在运行时的存活时间。
   编译器会在运行时管理变量的生命周期，确保资源不会被提前释放或访问非法内存：

   ```rust
   let x = vec![1, 2, 3]; // 分配堆内存
   drop(x); // 提前释放资源
   println!("{:?}", x); // 运行时错误：资源已被释放
   ```

3. **所有权移动与借用**：
   运行时，变量的所有权会在函数调用和数据结构之间转移，这可能导致变量的值在特定情况下不可用：

   ```rust
   let mut s = String::from("hello");
   let len = s.len(); // 借用 s，但未转移所有权
   println!("length: {}", len); // 输出长度
   println!("{}", s); // 仍然可以使用 s，因为所有权未转移
   ```

## 总结

- **静态检查** 确保变量在编译阶段符合语言的语义规则，如类型、作用域、不可变性等。
- **动态行为** 描述变量在运行时的实际操作和状态变化，如内存分配、值的修改和生命周期等。

通过这种静态和动态的结合，Rust 能够在提供高性能的同时，保证代码的安全性和正确性。

## Rust 中的变体性与多态：关系、证明与安全保证

### 一、变体性与多态的关系

#### 1. 基本关系

**多态** 是指代码可以适用于多种类型的能力，
而**变体性**（协变、逆变、不变性）则描述了在多态环境下，复合类型之间的子类型关系如何从其组成类型的子类型关系派生。

在 Rust 中，多态主要通过以下机制实现：

1. **泛型**（参数化多态）
2. **trait 对象**（子类型多态）
3. **生命周期参数**（生命周期多态）

变体性规则决定了在这些多态场景中，类型转换的合法性。

#### 2. 具体联系

| 多态形式 | 变体性应用 | 关系 |
|:----:|:----|:----|
| 泛型 | 泛型参数的变体性 | 决定泛型类型之间的转换规则 |
| trait 对象 | 引用的协变性 | 允许将具体类型引用转换为 trait 对象引用 |
| 生命周期多态 | 生命周期的协变性 | 允许长生命周期引用用于短生命周期上下文 |

```rust
// 泛型与变体性
struct Wrapper<T>(T);  // T 在这里是协变的

// trait 对象与变体性
trait Animal {}
struct Dog {}
impl Animal for Dog {}

fn example() {
    let dog = Dog {};
    let animal: &dyn Animal = &dog;  // 协变允许 &Dog -> &dyn Animal
}

// 生命周期多态与变体性
fn process<'a>(data: &'a str) {}

fn lifetime_example() {
    let static_str: &'static str = "hello";
    process(static_str);  // 协变允许 &'static str -> &'a str
}
```

### 二、变体性规则的推理与证明

#### 1. 协变性推理

**推理原则**：如果类型 A 是类型 B 的子类型，且 F 是协变的，则 `F<A>` 是 `F<B>` 的子类型。

**证明方法**：

1. 定义子类型关系：A <: B 表示 A 是 B 的子类型
2. 对于协变类型 F，证明：如果 A <: B，则 `F<A>` <: `F<B>`

**Rust 中的例子**：

```rust
// 证明不可变引用是协变的
fn takes_ref<'a, T>(r: &'a T) {}

fn covariance_proof<'long, 'short, T>(long_ref: &'long T) 
    where 'long: 'short  // 'long 比 'short 活得长，即 'long <: 'short
{
    // 如果 &T 对生命周期是协变的，那么应该可以传递
    takes_ref::<'short, T>(long_ref);  // 编译成功，证明协变
}
```

#### 2. 逆变性推理

**推理原则**：如果类型 A 是类型 B 的子类型，且 F 是逆变的，则 `F<B>` 是 `F<A>` 的子类型。

**证明方法**：

1. 定义子类型关系：A <: B
2. 对于逆变类型 F，证明：如果 A <: B，则 `F<B>` <: `F<A>`

**Rust 中的例子**：

```rust
// 证明函数参数位置是逆变的
fn short_lived<'a>(x: &'a i32) {}

fn contravariance_proof<'long, 'short>() 
    where 'long: 'short  // 'long <: 'short
{
    // 函数类型 fn(&'short i32) 应该是 fn(&'long i32) 的子类型
    let f: fn(&'short i32) = short_lived::<'long>;  // 编译成功，证明逆变
}
```

#### 3. 不变性推理

**推理原则**：如果类型 A 是类型 B 的子类型，且 F 是不变的，则 `F<A>` 和 `F<B>` 之间没有子类型关系。

**证明方法**：

1. 定义子类型关系：A <: B
2. 对于不变类型 F，证明：`F<A>` 不是 `F<B>` 的子类型，`F<B>` 也不是 `F<A>` 的子类型

**Rust 中的例子**：

```rust
// 证明可变引用是不变的
fn takes_mut_ref<'a, T>(r: &'a mut T) {}

fn invariance_proof<'long, 'short, T>(long_ref: &'long mut T) 
    where 'long: 'short  // 'long <: 'short
{
    // 如果 &mut T 对生命周期是不变的，那么下面应该编译失败
    // takes_mut_ref::<'short, T>(long_ref);  // 编译失败，证明不变性
}
```

### 三、变体性如何保证类型安全和内存安全

#### 1. 协变与安全保证

**类型安全保证**：

- 协变允许将"更具体"的类型用在需要"更一般"类型的地方
- 保证操作的语义一致性，因为子类型可以做父类型能做的所有事情

**内存安全保证**：

- 对于引用，协变允许长生命周期引用转换为短生命周期引用
- 这是安全的，因为长生命周期引用保证在短生命周期内保持有效

```rust
fn safety_example<'a>(data: &'a [u8]) {
    // 使用数据...
}

fn demonstrate_safety() {
    let long_lived = vec![1, 2, 3];
    
    // 协变允许将长生命周期引用传递给接受短生命周期引用的函数
    // 这保证了引用在使用期间一定有效
    safety_example(&long_lived);
}
```

#### 2. 逆变与安全保证

**类型安全保证**：

- 逆变允许将"更一般"的函数用在需要"更具体"函数的地方
- 保证函数能够处理所有预期的输入类型

**内存安全保证**：

- 对于函数参数，逆变允许接受任意生命周期引用的函数用在需要接受特定生命周期引用的地方
- 这是安全的，因为能处理任意生命周期的函数一定能处理特定生命周期

```rust
fn process_any<'a>(data: &'a [u8]) {
    // 处理任意生命周期的数据
}

fn demonstrate_contravariance() {
    // 函数类型中参数位置的逆变
    let specific_fn: fn(&'static [u8]) = process_any;
    
    // 安全：process_any 能处理任意生命周期，
    // 所以一定能处理静态生命周期
    specific_fn(&[1, 2, 3]);
}
```

#### 3. 不变性与安全保证

**类型安全保证**：

- 不变性防止潜在的不安全类型转换
- 对于可能导致类型不一致的情况，强制要求类型完全匹配

**内存安全保证**：

- 对于可变引用，不变性防止生命周期的不安全转换
- 防止数据竞争和悬垂引用

```rust
fn demonstrate_invariance() {
    let mut long_data = vec![1, 2, 3];
    let mut short_data = vec![4, 5];
    
    {
        // 可变引用的不变性
        let long_ref = &mut long_data;
        
        // 如果可变引用是协变的，下面的代码将编译通过：
        // let short_lifetime_ref: &mut Vec<i32> = long_ref;
        
        // 然后我们可以在外部作用域继续使用 long_ref，
        // 同时 short_lifetime_ref 已经失效，这将导致内存不安全
        
        // 不变性阻止了这种转换，保证了内存安全
    }
    
    // 现在可以安全地使用 long_data
    long_data.push(4);
}
```

### 四、运行时安全与变体性

虽然 Rust 的变体性规则主要在编译时强制执行，但它们直接影响运行时安全：

#### 1. 防止悬垂引用

```rust
fn prevent_dangling_references() {
    let mut data = String::from("hello");
    
    let r;
    {
        let inner = String::from("world");
        // r = &inner;  // 编译错误：inner 的生命周期太短
        // 协变性规则防止将短生命周期引用赋值给长生命周期引用变量
    }
    // 如果上面的赋值被允许，这里会访问已释放的内存
    // println!("{}", r);
}
```

#### 2. 防止数据竞争

```rust
fn prevent_data_races() {
    let mut data = vec![1, 2, 3];
    
    // 可变引用的不变性防止多个可变引用同时存在
    let r1 = &mut data;
    // let r2 = &mut data;  // 编译错误：不能同时有两个可变引用
    
    // 如果允许多个可变引用，将导致数据竞争
    r1.push(4);
    // r2.push(5);  // 如果这行被允许，将导致未定义行为
}
```

#### 3. 保证 trait 对象安全

```rust
trait Drawable {
    fn draw(&self);
}

struct Canvas {
    elements: Vec<Box<dyn Drawable>>,
}

impl Canvas {
    fn add<T: Drawable + 'static>(&mut self, element: T) {
        // 协变允许将具体类型装箱并存储为 trait 对象
        self.elements.push(Box::new(element));
    }
    
    fn draw_all(&self) {
        for element in &self.elements {
            // 安全地调用多态方法
            element.draw();
        }
    }
}
```

### 五、形式化证明示例

#### 1. 协变安全性证明

**命题**：如果类型 `&'a T` 对生命周期 `'a` 是协变的，那么将长生命周期引用赋值给短生命周期变量是安全的。

**证明**：

1. 假设 `'long: 'short`（`'long` 比 `'short` 活得长）
2. 根据协变性，`&'long T <: &'short T`
3. 当我们将 `&'long T` 类型的值赋给 `&'short T` 类型的变量时：
   - `'short` 的作用域内，`'long` 引用保证有效
   - 不会在 `'short` 结束后通过该引用访问数据
4. 因此，这种转换保证了内存安全

```rust
fn covariance_safety_proof<'long, 'short, T>(long_ref: &'long T) 
    where 'long: 'short
{
    let short_ref: &'short T = long_ref;  // 安全的协变转换
    
    // 在 'short 的作用域内使用 short_ref 是安全的
    // 因为 long_ref 保证在整个 'short 期间有效
}
```

#### 2. 逆变安全性证明

**命题**：如果函数类型 `fn(&'a T)` 对生命周期 `'a` 是逆变的，那么将接受任意生命周期引用的函数用在需要接受特定生命周期引用的地方是安全的。

**证明**：

1. 假设 `'long: 'short`
2. 根据逆变性，`fn(&'short T) <: fn(&'long T)`
3. 当我们将 `fn(&'short T)` 类型的函数赋给 `fn(&'long T)` 类型的变量时：
   - 该函数能处理任何满足 `'short` 约束的引用
   - `'long` 引用一定满足 `'short` 约束（因为 `'long: 'short`）
4. 因此，这种转换保证了类型安全

```rust
fn process_short<'a>(data: &'a [u8]) {
    // 处理短生命周期数据
}

fn contravariance_safety_proof<'long, 'short>() 
    where 'long: 'short
{
    // 逆变允许这种转换
    let long_fn: fn(&'long [u8]) = process_short::<'short>;
    
    // 安全：process_short 能处理 'short 生命周期，
    // 而 'long 引用一定满足 'short 约束
    let static_data: &'static [u8] = &[1, 2, 3];
    long_fn(static_data);
}
```

#### 3. 不变性安全性证明

**命题**：如果类型 `&'a mut T` 对生命周期 `'a` 是不变的，那么它防止了潜在的内存不安全操作。

**证明**：

1. 假设 `'long: 'short`
2. 如果 `&'a mut T` 对 `'a` 是协变的，则 `&'long mut T <: &'short mut T`
3. 这将允许以下不安全操作：

   ```rust
   fn unsafe_operation<'long, 'short, T>(long_ref: &'long mut T) 
       where 'long: 'short
   {
       let short_ref: &'short mut T = long_ref;  // 假设这是合法的
       
       // 现在 short_ref 和 long_ref 都指向同一数据
       // 当 'short 结束但 'long 仍然有效时：
       // - short_ref 已失效
       // - long_ref 仍然有效
       // - 可以通过 long_ref 访问已经被认为无效的数据
   }
   ```

4. 不变性阻止了这种转换，确保了内存安全

```rust
fn invariance_safety_proof<'long, 'short, T>(long_ref: &'long mut T) 
    where 'long: 'short
{
    // 下面的代码不能编译，证明了不变性的安全保证
    // let short_ref: &'short mut T = long_ref;
    
    // 如果上面的代码被允许，将导致潜在的内存不安全
}
```

### 六、变体性与多态的实际应用

#### 1. 构建灵活的 API

```rust
// 利用协变构建灵活的 API
struct DataProcessor<'a, T> {
    data: &'a [T],
}

impl<'a, T> DataProcessor<'a, T> {
    fn new(data: &'a [T]) -> Self {
        DataProcessor { data }
    }
    
    fn process(&self) {
        // 处理数据...
    }
}

fn flexible_api_example() {
    let long_lived_data = vec![1, 2, 3];
    
    // 协变允许将长生命周期数据用于短生命周期上下文
    {
        let processor = DataProcessor::new(&long_lived_data);
        processor.process();
    } // processor 的生命周期结束，但 long_lived_data 仍然有效
    
    println!("原始数据仍然可用: {:?}", long_lived_data);
}
```

#### 2. 实现类型安全的回调系统

```rust
// 利用逆变实现类型安全的回调系统
struct CallbackSystem<F> where F: Fn(&str) {
    callback: F,
}

impl<F> CallbackSystem<F> where F: Fn(&str) {
    fn new(callback: F) -> Self {
        CallbackSystem { callback }
    }
    
    fn notify(&self, message: &str) {
        (self.callback)(message);
    }
}

fn callback_system_example() {
    // 创建一个可以处理任意生命周期字符串的回调
    let process_any = |s: &str| {
        println!("处理消息: {}", s);
    };
    
    // 逆变允许将处理任意生命周期的回调用于特定生命周期
    let system = CallbackSystem::new(process_any);
    
    // 使用静态字符串
    system.notify("静态消息");
    
    // 使用动态创建的字符串
    let dynamic_message = String::from("动态消息");
    system.notify(&dynamic_message);
}
```

#### 3. 保证容器类型的安全

```rust
// 利用不变性保证容器安全
struct SafeContainer<T> {
    data: Vec<T>,
}

impl<T> SafeContainer<T> {
    fn new() -> Self {
        SafeContainer { data: Vec::new() }
    }
    
    fn add(&mut self, item: T) {
        self.data.push(item);
    }
    
    fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.data.get_mut(index)
    }
}

fn container_safety_example() {
    let mut int_container = SafeContainer::<i32>::new();
    int_container.add(42);
    
    // 不变性防止以下代码编译：
    // let float_container: SafeContainer<f64> = int_container;
    
    // 这保证了类型安全，防止在 float_container 中存储整数
    // 或尝试从 int_container 中读取浮点数
    
    if let Some(value) = int_container.get_mut(0) {
        *value = 100;
    }
}
```

### 七、总结

Rust 的变体性规则与多态系统紧密相连，共同构建了一个在编译时就能保证类型安全和内存安全的系统：

1. **协变**允许更具体的类型用于更一般的上下文，使多态代码更灵活，同时保证引用在使用期间始终有效。

2. **逆变**允许更一般的函数用于更具体的上下文，确保函数能够处理所有预期的输入类型。

3. **不变性**防止潜在的不安全类型转换，特别是对于可变引用，防止数据竞争和悬垂引用。

这些规则不仅是理论上的形式化保证，更是实际编程中防止常见内存和并发错误的重要机制。
Rust 的类型系统通过这些规则，在不牺牲表达能力的前提下，提供了强大的安全保证，
使得"没有垃圾回收的内存安全"和"没有数据竞争的并发"成为可能。
