# to_owned

在 Rust 中，`to_owned` 是一个方法，通常与 `Borrow` trait 配合使用。
它用于创建某个值的 "拥有" 版本（owned version），即该值的独立副本，而不是引用。
`to_owned` 方法本身并不直接转移所有权，但它可以用来创建一个可以拥有的新值。

**定义**：

```rust
trait ToOwned {
    type Owned: Borrow<Self>;
    fn to_owned(&self) -> Self::Owned;
}
```

**应用**：

- `to_owned` 通常用于从借用类型（如 `Cow`，即 "Copy-on-Write"）创建拥有类型（如 `String`）。

例如，`Cow`（`Cow<'a, T>`）类型可以包含一个对借用数据的借用或一个拥有的数据。
当你需要确保拥有数据时，可以调用 `to_owned` 方法来创建一个 `String`：

```rust
use std::borrow::Cow;

let borrowed = Cow::Borrowed("hello");
let owned: String = borrowed.to_owned(); // 创建 "hello" 的 String 类型的独立副本
```

在这个例子中，`to_owned` 方法被调用来创建 `String` 类型的值，它拥有自己的数据副本。
这个过程涉及到数据的复制，但原有的 `Cow` 类型的值（`borrowed`）仍然有效，并没有发生所有权的转移。

**转移所有权**：

- 要转移所有权，你需要使用值的移动语义，例如通过将值赋给另一个变量或将其作为参数传递给函数。

```rust
let s = String::from("hello");
let s2 = s; // s 的所有权被转移到 s2，s 不再可用
```

在这个例子中，`s` 的所有权被直接转移到了 `s2`，这是通过值的移动来实现的，而不是通过 `to_owned`。

总结来说，`to_owned` 是用来从借用类型创建拥有类型的一个方法，它本身不涉及所有权的转移，
但它可以用来创建一个新值，该值随后可以通过移动来转移其所有权。
