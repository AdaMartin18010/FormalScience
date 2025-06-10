# Rust std::ops

在 Rust 中，`std::ops` 模块提供了许多 trait，用于定义不同类型的操作符行为。
这些 trait 可以被实现以支持自定义类型的操作符重载。
以下是一些常见的 `std::ops` trait 及其用途：

## 1. **算术操作符**

- **`Add`**：用于定义 `+` 操作符的行为。
- **`Sub`**：用于定义 `-` 操作符的行为。
- **`Mul`**：用于定义 `*` 操作符的行为。
- **`Div`**：用于定义 `/` 操作符的行为。
- **`Rem`**：用于定义 `%` 操作符的行为。

## 2. **位操作符**

- **`BitAnd`**：用于定义 `&` 操作符的行为。
- **`BitOr`**：用于定义 `|` 操作符的行为。
- **`BitXor`**：用于定义 `^` 操作符的行为。
- **`Shl`**：用于定义 `<<` 操作符的行为。
- **`Shr`**：用于定义 `>>` 操作符的行为。

## 3. **赋值操作符**

- **`AddAssign`**：用于定义 `+=` 操作符的行为。
- **`SubAssign`**：用于定义 `-=` 操作符的行为。
- **`MulAssign`**：用于定义 `*=` 操作符的行为。
- **`DivAssign`**：用于定义 `/=` 操作符的行为。
- **`RemAssign`**：用于定义 `%=` 操作符的行为。
- **`BitAndAssign`**：用于定义 `&=` 操作符的行为。
- **`BitOrAssign`**：用于定义 `|=` 操作符的行为。
- **`BitXorAssign`**：用于定义 `^=` 操作符的行为。
- **`ShlAssign`**：用于定义 `<<=` 操作符的行为。
- **`ShrAssign`**：用于定义 `>>=` 操作符的行为。

## 4. **一元操作符**

- **`Neg`**：用于定义 `-`（取负）操作符的行为。
- **`Not`**：用于定义 `!`（取反）操作符的行为。

## 5. **索引操作符**

- **`Index`**：用于定义 `[]` 操作符的行为。
- **`IndexMut`**：用于定义 `[]` 操作符的可变版本。

### 示例代码

以下是一些示例代码，展示了如何实现这些 trait：

#### 1. **实现 `Add` 和 `Sub`**

```rust
use std::ops::{Add, Sub};

#[derive(Debug, Copy, Clone, PartialEq)]
struct Point {
    x: i32,
    y: i32,
}

impl Add for Point {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Self {
            x: self.x + other.x,
            y: self.y + other.y,
        }
    }
}

impl Sub for Point {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        Self {
            x: self.x - other.x,
            y: self.y - other.y,
        }
    }
}

fn main() {
    let p1 = Point { x: 1, y: 2 };
    let p2 = Point { x: 3, y: 4 };

    let p3 = p1 + p2;
    let p4 = p1 - p2;

    assert_eq!(p3, Point { x: 4, y: 6 });
    assert_eq!(p4, Point { x: -2, y: -2 });
}
```

#### 2. **实现 `BitAnd` 和 `BitOr`**

```rust
use std::ops::{BitAnd, BitOr};

#[derive(Debug, Copy, Clone, PartialEq)]
struct BitFlags(u8);

impl BitAnd for BitFlags {
    type Output = Self;

    fn bitand(self, other: Self) -> Self {
        Self(self.0 & other.0)
    }
}

impl BitOr for BitFlags {
    type Output = Self;

    fn bitor(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }
}

fn main() {
    let a = BitFlags(0b1100);
    let b = BitFlags(0b1010);

    let c = a & b;
    let d = a | b;

    assert_eq!(c, BitFlags(0b1000));
    assert_eq!(d, BitFlags(0b1110));
}
```

#### 3. **实现 `AddAssign` 和 `SubAssign`**

```rust
use std::ops::{AddAssign, SubAssign};

#[derive(Debug, Copy, Clone, PartialEq)]
struct Counter {
    value: i32,
}

impl AddAssign for Counter {
    fn add_assign(&mut self, other: Self) {
        self.value += other.value;
    }
}

impl SubAssign for Counter {
    fn sub_assign(&mut self, other: Self) {
        self.value -= other.value;
    }
}

fn main() {
    let mut a = Counter { value: 5 };
    let b = Counter { value: 3 };

    a += b;
    assert_eq!(a, Counter { value: 8 });

    a -= b;
    assert_eq!(a, Counter { value: 5 });
}
```

#### 4. **实现 `Index` 和 `IndexMut`**

```rust
use std::ops::{Index, IndexMut};

#[derive(Debug, Default)]
struct Vector {
    elements: Vec<i32>,
}

impl Index<usize> for Vector {
    type Output = i32;

    fn index(&self, index: usize) -> &Self::Output {
        &self.elements[index]
    }
}

impl IndexMut<usize> for Vector {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.elements[index]
    }
}

fn main() {
    let mut vec = Vector { elements: vec![1, 2, 3] };

    assert_eq!(vec[1], 2);

    vec[1] = 4;
    assert_eq!(vec[1], 4);
}
```

### 总结

Rust 的 `std::ops` 模块提供了许多 trait，用于定义不同类型的操作符行为。
通过实现这些 trait，可以为自定义类型提供类似内置类型的操作符行为，从而提高代码的可读性和可维护性。
这些 trait 包括算术操作符、位操作符、赋值操作符、一元操作符和索引操作符等。

### Rust 中 `Neg` 和 `Not` 的用法示例

#### 1. `Neg`（一元负号）

`Neg` trait 用于定义一元负号（`-`）操作符的行为。它可以为自定义类型添加取负的支持。

**示例：**

```rust
use std::ops::Neg;

#[derive(Debug, PartialEq)]
struct Temperature {
    celsius: i32,
}

// 实现 Neg trait
impl Neg for Temperature {
    type Output = Temperature;

    fn neg(self) -> Self::Output {
        Temperature {
            celsius: -self.celsius,
        }
    }
}

fn main() {
    let temp = Temperature { celsius: 10 };
    let neg_temp = -temp;
    println!("Negative temperature: {:?}", neg_temp); // 输出: Negative temperature: Temperature { celsius: -10 }

    // 测试
    assert_eq!(neg_temp, Temperature { celsius: -10 });
    println!("Test passed.");
}
```

#### 2. `Not`（逻辑非）

`Not` trait 用于定义一元逻辑非（`!`）操作符的行为。
它可以为自定义类型添加逻辑非的支持。

**示例：**

```rust
use std::ops::Not;

#[derive(Debug, PartialEq)]
struct BooleanContainer {
    value: bool,
}

// 实现 Not trait
impl Not for BooleanContainer {
    type Output = BooleanContainer;

    fn not(self) -> Self::Output {
        BooleanContainer {
            value: !self.value,
        }
    }
}

fn main() {
    let container = BooleanContainer { value: true };
    let negated = !container;
    println!("Negated boolean: {:?}", negated); // 输出: Negated boolean: BooleanContainer { value: false }

    // 测试
    assert_eq!(negated.value, false);
    println!("Test passed.");
}
```

### *总结*

- `Neg` trait 用于定义一元负号（`-`）操作符的行为，可以为自定义类型添加取负功能。
- `Not` trait 用于定义一元逻辑非（`!`）操作符的行为，可以为自定义类型添加逻辑非功能。
- 通过实现这些 trait，可以为自定义类型提供类似内置类型的操作符行为，提高代码的可读性和可维护性。

### `Neg` 可用的数据类型

`Neg` 是用于实现一元负号（`-`）运算符的 trait，通常用于数值类型，表示取负。
它可以对以下数据类型生效：

- **整数类型**：如 `i8`、`i16`、`i32`、`i64`、`i128` 和 `isize`。
- **浮点数类型**：如 `f32` 和 `f64`。
- **自定义类型**：如果用户实现了 `Neg` trait，可以为自定义类型添加取负功能。

**示例**：

```rust
use std::ops::Neg;

#[derive(Debug, PartialEq)]
struct Temperature {
    celsius: i32,
}

impl Neg for Temperature {
    type Output = Temperature;

    fn neg(self) -> Self::Output {
        Temperature {
            celsius: -self.celsius,
        }
    }
}

fn main() {
    let temp = Temperature { celsius: 10 };
    let neg_temp = -temp;
    println!("Negative temperature: {:?}", neg_temp); // 输出: Negative temperature: Temperature { celsius: -10 }
}
```

### `Not` 可用的数据类型

`Not` 是用于实现一元逻辑非（`!`）运算符的 trait，通常用于布尔类型或位运算。
它可以对以下数据类型生效：

- **布尔类型**：如 `bool`。
- **整数类型**：如 `i8`、`i16`、`i32`、`i64`、`i128`、`isize`、`u8`、`u16`、`u32`、`u64`、`u128` 和 `usize`。
- **自定义类型**：如果用户实现了 `Not` trait，可以为自定义类型添加逻辑非功能。

**示例**：

```rust
use std::ops::Not;

#[derive(Debug, PartialEq)]
struct BooleanContainer {
    value: bool,
}

impl Not for BooleanContainer {
    type Output = BooleanContainer;

    fn not(self) -> Self::Output {
        BooleanContainer {
            value: !self.value,
        }
    }
}

fn main() {
    let container = BooleanContainer { value: true };
    let negated = !container;
    println!("Negated boolean: {:?}", negated); // 输出: Negated boolean: BooleanContainer { value: false }
}
```

### **总结**

`Neg` 和 `Not` 是 Rust 中用于实现一元运算符（`-` 和 `!`）的 trait。
`Neg` 主要用于数值类型，表示取负；
`Not` 主要用于布尔类型和位运算，表示逻辑非。
通过实现这些 trait，可以为自定义类型添加这些运算符的支持。
