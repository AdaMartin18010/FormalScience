# NonNull

在 Rust 中，`NonNull` 是一个智能指针类型，它提供了对非空裸指针的安全封装。
`NonNull` 位于 `std::ptr` 模块中，主要用于确保指针非空，并且可以安全地转换为 `&T` 或 `&mut T` 类型的引用。

## 定义

`NonNull` 定义如下：

```rust
pub struct NonNull<T> {
    pointer: *const T,
}
```

这里，`NonNull<T>` 包含一个 `pointer` 字段，它是一个指向 `T` 类型的不可变引用的裸指针。
    `NonNull` 保证这个指针不是空指针（null）。

## 解释

`NonNull` 的设计有几个关键点：

1. **非空保证**：`NonNull` 的主要目的是提供对非空指针的封装。它不允许创建空指针的 `NonNull` 实例，这与 `Option<*const T>` 不同，后者可以用 `None` 来表示空指针。

2. **安全性**：通过使用 `NonNull`，Rust 编译器可以保证指针在使用前是非空的，这有助于避免空指针解引用导致的 panic。

3. **转换**：`NonNull` 可以很容易地转换为安全的引用。例如，`NonNull<T>` 可以转换为 `&T`，但这需要保证引用的生命周期是有效的。

4. **所有权和借用规则**：`NonNull` 本身不拥有它所指向的数据，它只是对现有指针的封装。因此，使用 `NonNull` 时，需要确保遵循 Rust 的所有权和借用规则。

### 应用

`NonNull` 在 Rust 中的应用场景包括：

1. **API 边界**：在与 C 语言 API 交互时，经常需要处理裸指针。使用 `NonNull` 可以安全地传递和管理这些指针。

2. **集合实现**：在实现自定义数据结构（如链表、树等）时，可能需要使用裸指针来表示节点链接。`NonNull` 可以用来确保这些指针非空。

3. **智能指针**：`NonNull` 可以作为构建其他智能指针的基础，例如 `Box`、`Rc`、`Arc` 等。

4. **类型安全**：在需要确保指针有效性的情况下，使用 `NonNull` 可以提供类型安全的保证。

### 创建 `NonNull`

`NonNull` 的创建通常是不安全的，因为它需要调用者保证指针非空。例如：

```rust
use std::ptr::NonNull;

let data = Box::new(42);
let non_null: NonNull<i32> = unsafe { NonNull::new_unchecked(Box::into_raw(data)) };
```

在这个例子中，我们使用 `Box::into_raw` 将 `Box` 转换为裸指针，然后使用 `NonNull::new_unchecked` 来创建 `NonNull` 实例。
这个过程是 `unsafe` 的，因为需要保证指针非空。

### 使用 `NonNull`

使用 `NonNull` 时，可以将其转换为引用，例如：

```rust
let data_ref: &i32 = non_null.as_ref();
```

这里，`as_ref` 方法将 `NonNull<i32>` 转换为 `&i32`。这个过程是安全的，因为 `NonNull` 保证了指针非空。

总的来说，`NonNull` 是 Rust 中处理裸指针的一种安全方式，它通过提供非空保证和类型安全，帮助开发者避免空指针相关的错误。
