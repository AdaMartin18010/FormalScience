# ToOwned

在 Rust 中，`ToOwned` trait 定义在标准库的 `std::borrow` 模块中，其主要作用是将借用的数据（例如 `&T`）转换成拥有所有权的数据（例如 `T::Owned`），也就是从不可变借用转换为可拥有的副本。
简单来说，它提供了一个公共接口，使得可以通过调用 `to_owned` 方法，从一个借用值中创建一个拥有独立所有权的克隆数据。

## 主要特点

1. **从借用转为拥有**：  
   `ToOwned` 允许你从一个借用的引用（比如 `&str`）创建其对应的拥有数据（比如 `String`）。这对于需要在不借用原数据的情况下，持有独立拷贝的数据场景非常有用。

2. **与 `Clone` 的关系**：  
   大部分实现了 `ToOwned` 的类型，其 `to_owned` 方法通常依赖于该类型的 `Clone` 实现。但 `ToOwned` 定义了一个更通用的抽象，因为它允许拥有类型（即 `Owned` 关联类型）与原始借用类型有所不同。

3. **关联类型 `Owned`**：  
   在 `ToOwned` trait 中，有一个关联类型 `Owned`，表示通过 `to_owned` 得到的拥有所有权的类型，该类型通常实现了 `Borrow<Self>`，这保证了可以将拥有的数据视作原始借用类型。

## 定义示例

下面是 `ToOwned` trait 的简化定义：

```rust:std/borrow/to_owned.rs
pub trait ToOwned {
    /// 所拥有数据的类型，例如对于 `&str` 来说，它的 Owned 类型为 `String`
    type Owned: Borrow<Self>;

    /// 从当前借用实例创建一个拥有所有权的数据
    fn to_owned(&self) -> Self::Owned;
}
```

## 使用示例

以字符串为例，`&str` 实现了 `ToOwned` trait，因此可以通过 `to_owned` 方法将一个字符串切片转换为 `String`：

```rust
fn main() {
    let s: &str = "Hello, Rust!";
    // 使用 `to_owned` 得到一个拥有所有权的 String
    let owned: String = s.to_owned();

    println!("{}", owned);
}
```

在这个例子中，`s.to_owned()` 会返回一个 `String`，即拥有独立所有权的数据，从而使得这个字符串数据可以自由地传递和修改，而不依赖原始的借用数据。

## 总结

- **用途**：`ToOwned` trait 提供了一个抽象接口，将借用的数据转换为拥有所有权的数据。
- **常见实现**：最常见的实现包括 `&str` → `String`、`[T]` → `Vec<T>` 等，通过调用 `to_owned` 方法实现数据的克隆或复制。
- **与 `Clone` 的关系**：虽然实现上可能会调用 `Clone`，但 `ToOwned` 更关注借用转换为拥有数据这一概念，其拥有类型（`Owned`）并不总是与原类型完全相同。

使用 `ToOwned` 可以让开发者在需要脱离借用生命周期的场景下，方便自然地获取数据的拥有拷贝。

下面具体解释一下 **ToOwned** trait 是否区分可变借用（mutable borrow）与不可变借用（immutable borrow）。

## 1. **ToOwned** Trait 的定义

在 Rust 标准库中，**ToOwned** trait 定义如下（简化表示）：

```rust:std/borrow/to_owned.rs
pub trait ToOwned {
    type Owned: Borrow<Self>;
    fn to_owned(&self) -> Self::Owned;
}
```

可以看到，`to_owned` 方法的签名是接受一个 `&self`（不可变引用），返回一个拥有所有权的值。也就是说，**ToOwned** trait 的设计就是基于不可变借用的。

## 2. 为什么不区分可变和不可变借用？

- **设计目的**：  
  **ToOwned** 的主要目的是根据一个借用的数据（通常是不可变借用，如 `&str` 或 `&[T]`）生成一个拥有所有权的副本（如 `String` 或 `Vec<T>`）。因此，它的接口就只需要 `&self`，不需要考虑可变借用。有了 `to_owned()`，你可以从借用中 “克隆” 出一个独立的拥有数据。

- **不可变引用的普适性**：  
  在很多应用场景中，即使你有一个 `&mut T`（可变引用），也可以隐式地将它视为 `&T` 来调用 `to_owned()`。Rust 的借用规则允许从可变引用隐式地获得不可变引用，这样调用 `to_owned()` 仍然合法，但其中只使用了不可变部分的信息。

- **与 Borrow / BorrowMut 的关系**：  
  Rust 中用来描述借用行为的另一个重要 trait 是 **Borrow** 和 **BorrowMut**。它们分别定义了不可变和可变的借用视图。相比之下，**ToOwned** 只关心如何从一个借用的数据生成一个拥有所有权的数据，不涉及区分其借用时是否是可变的。

## 3. 代码示例

### 示例 1：直接从不可变借用生成拥有数据

对于字符串切片 `&str`，通过 `to_owned()` 生成一个 `String`：

```rust:src/to_owned_immutable.rs
fn main() {
    let s: &str = "Hello, world!";
    // 调用 to_owned()，生成拥有所有权的 String
    let owned_string: String = s.to_owned();
    println!("Owned string: {}", owned_string);
}
```

### 示例 2：从可变引用调用 `to_owned()`

假设有一个可变引用，但调用 `to_owned()` 时隐式转为不可变引用：

```rust:src/to_owned_from_mut.rs
fn main() {
    let mut s = String::from("Hello");
    
    // 通过可变引用获取数据，但调用 to_owned() 时会隐式转为 &String -> &str(或 &String)
    // 注意：对于 String 类型来说，标准实现是针对 &String 实现了 ToOwned（返回 String）.
    let owned_string = (&s).to_owned();
    println!("Owned string: {}", owned_string);
}
```

在这个例子中，即使 `s` 是可变的，但调用 `(&s).to_owned()` 实际上是对 `&s`（不可变引用）的操作。**ToOwned** 本身不会区分 `&T` 和 `&mut T`；它只关心不可变借用。

## 4. 总结

- **ToOwned** trait 的定义仅基于不可变借用（`&self`），它并不区分或单独处理可变借用。
- 如果你有 `&mut T`，调用 `to_owned()` 时会按照 `&T` 的方式处理，也就是说不会利用其可变性。
- 区分可变与不可变借用的责任由 **Borrow** 和 **BorrowMut** 这对 trait 承担，而 **ToOwned** 只是用于将借用的数据复制或克隆为拥有类型。

因此，**ToOwned** trait 自身不区分可变和不可变借用，其接口设计就是针对不可变借用进行转换。
