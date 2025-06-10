# deref

在 Rust 中，解引用操作符 `*` 用于从引用中取得其指向的值。
当存在嵌套引用时（比如 `&&T` 或者 `Box<Box<T>>`），
我们需要多次使用 `*` 运算符来逐层获取内部的值，
这种写法可以等价地写成一次连续书写的 `**p`，其实内部的含义就是 `*(*p)`。

例如，考虑下面这个简单例子：

```rust:src/main.rs
fn main() {
    let x = 123;
    let rx = &x;    // rx 的类型为 &i32
    let rrx = &&x;  // rrx 的类型为 &&i32

    // **rrx 等价于 *(*rrx)，即先解引用一次得到 &i32，再解引用得到 i32
    assert_eq!(x, **rrx);
}
```

在上面的代码中：

- `*rrx` 得到的是一个 `&i32`；
- 对 `*rrx` 再使用 `*`，即 `*(*rrx)`，得到的就是原始的 `i32` 值 `x`。

对于智能指针来说，Rust 通过实现 `Deref` trait 提供了类似的解引用方式。
例如，对 `Box<T>`、`Rc<T>` 或自定义的智能指针类型，当这些类型实现了 `Deref` 后，我们可以使用自动解引用机制。
下面是一个自定义智能指针的示例：

```rust:src/main.rs
use std::ops::Deref;

struct MyBox<T>(T);

impl<T> Deref for MyBox<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
    }
}

fn main() {
    let x = 10;
    let boxed = MyBox(MyBox(x));
    
    // boxed 的类型为 MyBox<MyBox<i32>>
    // *boxed 得到 MyBox<i32>，对其再解引用 **boxed 则得到 i32，即 x 的值
    assert_eq!(x, **boxed);
}
```

在这个例子中：

- `*boxed` 调用了 `MyBox<T>` 上的 `deref` 方法，结果是 `MyBox<i32>`；
- 对此再使用 `*`，即 `**boxed`，就得到了最内层的 `i32` 值。

总的来说，在 Rust 中：

- 嵌套的解引用操作 `**p` 就等价于 `*(*p)`；
- 编译器在需要时会自动沿用 `Deref` trait 对智能指针进行多次解引用（auto-deref），使得我们在调用方法或其他运算时无需手动写出所有的 `*` 操作。

这种多层解引用的等价化简让代码在面对复杂嵌套引用时依然可以保持清晰和简洁。
