# Rust 中的具体类型和抽象类型

## 目录

- [Rust 中的具体类型和抽象类型](#rust-中的具体类型和抽象类型)
  - [目录](#目录)
  - [1. 具体类型（Concrete Types）](#1-具体类型concrete-types)
  - [2. 抽象类型（Abstract Types）](#2-抽象类型abstract-types)
  - [总结](#总结)
    - [1. 类型别名（Type Alias）](#1-类型别名type-alias)
      - [示例](#示例)
    - [2. 新类型（Newtype）](#2-新类型newtype)
      - [2.1 示例](#21-示例)
    - [3 总结](#3-总结)
    - [1. `impl Trait` 是抽象类型](#1-impl-trait-是抽象类型)
      - [1.1 示例](#11-示例)
    - [2. `impl Trait` 是否可以用于类型别名](#2-impl-trait-是否可以用于类型别名)
      - [2.1 *示例*](#21-示例-1)
    - [3 *总结*](#3-总结-1)

在 Rust 中，类型可以分为两大类：具体类型（concrete types）和抽象类型（abstract types）。
以下是对这两类类型的定义、解释和示例：

## 1. 具体类型（Concrete Types）

具体类型是指在编译时已知大小和布局的类型。
这些类型的实例在内存中占据固定的空间。
具体类型包括：

- **标量类型（Scalar Types）**：
  - **整数类型**：如 `i32`, `u64` 等。

    ```rust
    let x: i32 = 10;
    ```

  - **浮点类型**：如 `f32`, `f64`。

    ```rust
    let y: f64 = 3.14;
    ```

  - **布尔类型**：`bool`。

    ```rust
    let is_active: bool = true;
    ```

  - **字符类型**：`char`。

    ```rust
    let letter: char = 'A';
    ```

- **复合类型（Compound Types）**：
  - **元组（Tuple）**：可以包含不同类型的值。

    ```rust
    let tuple: (i32, f64, char) = (42, 3.14, 'A');
    ```

  - **数组（Array）**：包含相同类型的固定大小的集合。

    ```rust
    let array: [i32; 3] = [1, 2, 3];
    ```

## 2. 抽象类型（Abstract Types）

抽象类型是指在编译时不确定具体实现的类型，通常用于定义接口或行为。
抽象类型包括：

- **特征（Traits）**：
  - 特征定义了一组方法的集合，可以被不同的类型实现。

    ```rust
    trait Shape {
        fn area(&self) -> f64;
    }

    struct Circle {
        radius: f64,
    }

    impl Shape for Circle {
        fn area(&self) -> f64 {
            std::f64::consts::PI * self.radius * self.radius
        }
    }
    ```

- **动态大小类型（DSTs）**：
  - 例如 `str` 和 trait 对象（如 `Box<dyn Trait>`），它们的大小在编译时未知。

    ```rust
    let s: &str = "Hello, Rust!";
    let boxed: Box<dyn Shape> = Box::new(Circle { radius: 5.0 });
    ```

## 总结

具体类型在编译时已知其大小和布局，适合用于存储和操作数据。
抽象类型则用于定义行为和接口，允许不同类型实现相同的功能。
通过这两种类型的结合，Rust 提供了强大的类型系统，确保了安全性和灵活性。

在 Rust 中，类型别名和新类型（newtype）是两种不同的概念，它们可以用于具体类型和抽象类型。以下是对这两者的解释以及它们的使用示例。

### 1. 类型别名（Type Alias）

类型别名是使用 `type` 关键字创建的，它为现有类型提供一个新的名称。类型别名不会创建新的类型，而只是为现有类型提供一个别名。可以用于具体类型和抽象类型。

#### 示例

- **具体类型的类型别名**：

    ```rust
    type Kilometers = i32;

    fn distance_travelled(distance: Kilometers) {
        println!("Distance: {} km", distance);
    }
    ```

- **抽象类型的类型别名**：

    ```rust
    trait Shape {
        fn area(&self) -> f64;
    }

    type ShapeRef = Box<dyn Shape>;

    struct Circle {
        radius: f64,
    }

    impl Shape for Circle {
        fn area(&self) -> f64 {
            std::f64::consts::PI * self.radius * self.radius
        }
    }

    fn print_area(shape: ShapeRef) {
        println!("Area: {}", shape.area());
    }
    ```

### 2. 新类型（Newtype）

新类型是通过创建一个结构体来封装现有类型，从而创建一个新的类型。新类型在类型系统中是独立的，具有自己的类型标识符。新类型通常用于类型安全和封装。

#### 2.1 示例

- **具体类型的新类型**：

    ```rust
    struct Meters(i32);

    fn distance_travelled(distance: Meters) {
        println!("Distance: {} m", distance.0);
    }
    ```

- **抽象类型的新类型**：

    ```rust
    trait Shape {
        fn area(&self) -> f64;
    }

    struct Circle {
        radius: f64,
    }

    impl Shape for Circle {
        fn area(&self) -> f64 {
            std::f64::consts::PI * self.radius * self.radius
        }
    }

    struct ShapeWrapper(Box<dyn Shape>);

    fn print_area(shape: ShapeWrapper) {
        println!("Area: {}", shape.0.area());
    }
    ```

### 3 总结

- **类型别名**：为现有类型提供一个新的名称，不创建新的类型，可以用于具体类型和抽象类型。
- **新类型**：通过结构体封装现有类型，创建一个新的类型，具有独立的类型标识符，通常用于类型安全和封装。

因此，类型别名和新类型都可以用于具体类型和抽象类型，但它们的用途和行为有所不同。

在 Rust 中，`impl Trait` 是一种用于定义抽象类型的语法，它允许你在函数签名中指定返回某种特征的类型，而不需要明确指定具体的类型。
这种方式可以用于隐藏具体实现，提供更大的灵活性。

### 1. `impl Trait` 是抽象类型

`impl Trait` 确实可以被视为一种抽象类型，因为它表示某种特征的实现，但并不暴露具体的类型。这使得函数可以返回实现了特定特征的任何类型，而不需要在函数签名中指定具体类型。

#### 1.1 示例

```rust
trait Shape {
    fn area(&self) -> f64;
}

struct Circle {
    radius: f64,
}

impl Shape for Circle {
    fn area(&self) -> f64 {
        std::f64::consts::PI * self.radius * self.radius
    }
}

fn create_shape() -> impl Shape {
    Circle { radius: 5.0 }
}
```

在上面的示例中，`create_shape` 函数返回一个实现了 `Shape` 特征的类型，但具体类型是隐藏的。

### 2. `impl Trait` 是否可以用于类型别名

`impl Trait` 不能直接用于类型别名。类型别名只能用于具体类型，而 `impl Trait` 是一种语法，用于在函数返回类型中表示某种特征的实现。你不能像使用类型别名那样直接将 `impl Trait` 赋值给一个类型别名。

#### 2.1 *示例*

```rust
// 这是不合法的
type ShapeType = impl Shape; // 错误：不能将 `impl Trait` 用于类型别名
```

### 3 *总结*

- `impl Trait` 是一种抽象类型，允许在函数中返回实现特定特征的类型，但不暴露具体类型。
- `impl Trait` 不能用于类型别名，类型别名只能用于具体类型。如果需要使用 `impl Trait`，通常是在函数签名中，而不是作为类型别名。
