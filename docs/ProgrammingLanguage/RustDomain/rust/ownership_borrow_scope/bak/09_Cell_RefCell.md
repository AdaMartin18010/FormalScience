# Cell 和 RefCell

在 Rust 中，`Cell` 和 `RefCell` 是两种不同的类型，它们都用于封装数据并提供运行时借用检查。
它们是 Rust 标准库中 `std::cell` 模块的一部分，用于在借用规则之外进行数据借用。

## Cell

**定义**：

```rust
struct Cell<T> {
    value: T,
}
```

`Cell` 提供了一种方式来存储一个值，并能够修改这个值，即使它被固定为不可变借用。

**应用**：

- `Cell` 允许你在保持外部借用的不变性的同时，改变内部的值。
- 它通常用于需要在编译时借用检查和运行时可变性之间进行权衡的场景。

```rust
use std::cell::Cell;

let c = Cell::new(5);
println!("Initial value: {}", c.get()); // 获取当前值

c.set(10); // 修改值
println!("After modification: {}", c.get());
```

### RefCell

**定义**：

```rust
struct RefCell<T> {
    value: T,
}
```

`RefCell` 允许你获取对内部数据的可变借用，即使在不可变借用的上下文中。

**应用**：

- `RefCell` 提供了运行时借用检查，如果违反了借用规则，比如数据竞争，程序将会导致 panic。
- 它通常用于数据需要在多个可变借用之间共享的场景。

```rust
use std::cell::RefCell;

let c = RefCell::new(5);
println!("Initial value: {}", *c.borrow()); // 获取当前值

*c.borrow_mut() = 10; // 修改值
println!("After modification: {}", *c.borrow());
```

### 区别和联系

- **可变性**：`Cell` 只允许不可变借用和修改内部值，而 `RefCell` 允许可变借用。
- **运行时检查**：`RefCell` 在运行时进行借用检查，违反借用规则会导致 panic，而 `Cell` 没有运行时检查。
- **使用场景**：`Cell` 适用于不需要可变借用的场景，`RefCell` 适用于需要在编译时借用检查和运行时可变性之间进行权衡的场景。

`Cell` 和 `RefCell` 都是 Rust 中处理借用和可变性的强大工具，它们提供了不同的方式来绕过 Rust 的严格借用规则，但使用它们时应谨慎，以避免潜在的运行时错误。
