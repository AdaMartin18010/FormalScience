# 1. Trait Object

## 目录

- [1. Trait Object](#1-trait-object)
  - [目录](#目录)
  - [1.1 使用 `dyn` 关键字和 `Any` trait](#11-使用-dyn-关键字和-any-trait)
  - [1.2 使用枚举](#12-使用枚举)
  - [1.3 使用泛型](#13-使用泛型)
  - [1.4 使用 `async-trait` crate](#14-使用-async-trait-crate)
  - [1.5 总结](#15-总结)

## 1.1 使用 `dyn` 关键字和 `Any` trait

Rust 的 `Any` trait 可以用来检查 trait object 的具体类型。
通过 `Any` trait 的 `type_id` 方法，可以获取 trait object 的类型信息，然后使用 `downcast_ref` 方法尝试将 trait object 转换为具体的类型。

```rust
use std::any::Any;

trait Draw {
    fn draw(&self) -> String;
}

impl Draw for u8 {
    fn draw(&self) -> String {
        format!("u8: {}", *self)
    }
}

impl Draw for f64 {
    fn draw(&self) -> String {
        format!("f64: {}", *self)
    }
}

fn draw1(x: &dyn Draw) {
    if let Some(u8_value) = x.downcast_ref::<u8>() {
        println!("u8: {}", u8_value);
    } else if let Some(f64_value) = x.downcast_ref::<f64>() {
        println!("f64: {}", f64_value);
    } else {
        println!("Unknown type");
    }
}

fn main() {
    let x = 1.1f64;
    let y = 8u8;

    draw1(&x);
    draw1(&y);
}
```

在上面的代码中，`downcast_ref` 方法用于尝试将 trait object 转换为具体的类型。
如果转换成功，则可以使用具体的类型进行操作。

## 1.2 使用枚举

枚举可以用来存储不同类型的值，并通过模式匹配来处理这些值。
虽然枚举不能直接存储 trait object，但可以通过将 trait object 包装在枚举中来实现类似的功能。

```rust
enum Widget {
    Button(Button),
    TextBox(TextBox),
}

impl Widget {
    fn render(&self) {
        match self {
            Widget::Button(b) => b.render(),
            Widget::TextBox(t) => t.render(),
        }
    }
}

struct Button;
impl Button {
    fn render(&self) {
        println!("Rendering Button");
    }
}

struct TextBox;
impl TextBox {
    fn render(&self) {
        println!("Rendering TextBox");
    }
}

fn main() {
    let widgets: Vec<Widget> = vec![Widget::Button(Button), Widget::TextBox(TextBox)];
    for widget in widgets {
        widget.render();
    }
}
```

在上面的代码中，`Widget` 枚举可以存储不同类型的值，通过 `match` 语句可以对这些值进行模式匹配和处理。

## 1.3 使用泛型

泛型可以用来定义可以处理多种类型的函数或结构体。
虽然泛型不能直接处理 trait object，但可以通过泛型和 trait bound 来实现类似的功能。

```rust
trait Draw {
    fn draw(&self);
}

struct Screen<T: Draw> {
    components: Vec<T>,
}

impl<T: Draw> Screen<T> {
    fn run(&self) {
        for component in self.components.iter() {
            component.draw();
        }
    }
}

struct Button;
impl Draw for Button {
    fn draw(&self) {
        println!("Drawing Button");
    }
}

struct TextBox;
impl Draw for TextBox {
    fn draw(&self) {
        println!("Drawing TextBox");
    }
}

fn main() {
    let screen = Screen {
        components: vec![Button, TextBox],
    };
    screen.run();
}
```

在上面的代码中，`Screen` 结构体使用泛型和 trait bound 来存储和处理实现了 `Draw` trait 的组件。

## 1.4 使用 `async-trait` crate

对于需要处理异步方法的 trait object，可以使用 `async-trait` crate。
这个 crate 允许定义异步方法的 trait，并将其转换为可以以 `dyn Trait` 形式访问的动态 trait 对象。

```rust
use async_trait::async_trait;

#[async_trait]
trait CostAsyncTrait {
    async fn example_func(&self) -> usize;
}

struct ImplCostAsyncTraitStruct;

#[async_trait]
impl CostAsyncTrait for ImplCostAsyncTraitStruct {
    async fn example_func(&self) -> usize {
        99
    }
}

async fn main() {
    let obj = ImplCostAsyncTraitStruct;
    let result = obj.example_func().await;
    println!("Result: {}", result);
}
```

在上面的代码中，`async-trait` crate 允许定义异步方法的 trait，并将其转换为可以以 `dyn Trait` 形式访问的动态 trait 对象。

## 1.5 总结

虽然 Rust 的解构语法不能直接用于匹配 trait object，
但可以通过使用 `Any` 和 `downcast_ref` 方法、枚举、泛型或 `async-trait` crate 等方法来处理 trait object。
这些方法在不同的场景下提供了灵活的解决方案，可以根据具体需求选择合适的方法。
