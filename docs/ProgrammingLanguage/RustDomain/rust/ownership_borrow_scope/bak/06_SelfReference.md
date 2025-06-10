# Rust 中的自引用（Self-referential structure）

在 Rust 中实现自引用（Self-referential structure）
需要使用 `Box` 或 `Rc`（Reference Counted）智能指针，
因为 Rust 的所有权规则不允许直接在结构体中包含对自身的直接引用。

以下是几种实现自引用的方法：

## 使用 `Box`

`Box` 是一个智能指针，用于在堆上分配内存。
你可以使用 `Box` 来实现自引用，但通常这样做是为了创建一个指向相同内存块的循环引用。

```rust
enum List {
    Cons(i32, Box<List>),
    Nil,
}

fn main() {
    let list = List::Cons(1,
        Box::new(List::Cons(2, Box::new(List::Nil))));
    // 这里创建了一个自引用的链表
}
```

在这个例子中，`List` 是一个枚举，它可以是 `Cons`，包含一个 `i32` 和一个 `Box<List>`，或者 `Nil`，表示列表的结束。
使用 `Box` 允许我们在 `Cons` 变体中存储对 `List` 的引用。

## 使用 `Rc`

`Rc`（Reference Counted）智能指针允许多个引用指向同一数据。
这对于实现自引用的计数非常有效。

```rust
use std::rc::Rc;

struct Node {
    value: i32,
    next: Option<Rc<Node>>,
}

fn main() {
    let node1 = Rc::new(Node { value: 1, next: None });
    let node2 = Rc::new(Node { value: 2, next: Some(Rc::clone(&node1)) });
    // node2 的 next 指针引用了 node1，实现了自引用
}
```

在这个例子中，我们使用 `Rc` 来创建一个链表，`node2` 的 `next` 指针引用了 `node1`，从而实现了自引用。

## 使用 `RefCell`

`RefCell` 是 Rust 中的一个类型，它提供了运行时借用检查。
它允许在借用规则之外进行可变借用，但使用不当可能会导致 panic。

```rust
use std::cell::RefCell;

struct Circle {
    radius: f32,
    parent: RefCell<Option<Circle>>,
}

fn main() {
    let outer = Circle { radius: 5.0, parent: RefCell::new(None) };
    let inner = Circle { radius: 3.0, parent: RefCell::new(Some(outer)) };
    // 通过 RefCell 实现自引用
}
```

在这个例子中，`Circle` 结构体使用 `RefCell` 来包装其 `parent` 字段，允许在运行时改变其内部的值，即使 `Circle` 实例已经被借用。

## 注意事项

- 使用 `Box` 和 `Rc` 时，需要小心循环引用的问题，因为它们可能导致内存泄漏。
- `RefCell` 允许自引用，但需要谨慎使用，因为它的运行时借用检查可能会失败，导致程序 panic。

Rust 的所有权和借用规则虽然严格，但通过智能指针和 `RefCell`，仍然可以灵活地实现自引用结构。
