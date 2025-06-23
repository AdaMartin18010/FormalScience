# Rust 是否有类似 Golang package init 函数的机制？

在 Golang 中，每个 package 可以定义一个或多个 `init()` 函数，这些函数会在包被导入时自动执行，
用来做包级的初始化工作。而 Rust 并没有内置类似 Golang 那样的包级自动初始化机制。
下面介绍一下 Rust 中的替代方案和常用做法。

## 1. 显式初始化

Rust 倾向于显式调用初始化代码。
通常在 `main()` 函数或者模块的公共接口中定义一个初始化函数，开发者需要在程序启动时显式调用这些函数。
这样可以明确控制初始化的顺序和逻辑。例如：

```rust:path/to/file
mod config {
    pub fn init() {
        println!("配置初始化");
        // 读取配置文件、设置全局状态等初始化操作
    }
}

fn main() {
    // 显式调用各模块的初始化函数
    config::init();
    // 程序的其他部分
    println!("程序继续执行...");
}
```

---

## 2. 静态变量的延迟初始化

对于全局变量或配置数据等，可以使用延迟初始化工具，
例如 [`lazy_static`](https://crates.io/crates/lazy_static) 或 [`once_cell`](https://crates.io/crates/once_cell)。
这种方式在首次使用变量时自动初始化，相当于一种“按需初始化”的机制：

```rust:path/to/file
#[macro_use]
extern crate lazy_static;

use std::sync::Mutex;

lazy_static! {
    static ref CONFIG: Mutex<String> = Mutex::new(init_config());
}

fn init_config() -> String {
    println!("Initializing configuration...");
    "配置初始化完成".to_string()
}

fn main() {
    // CONFIG 在首次访问时自动初始化
    {
        let config = CONFIG.lock().unwrap();
        println!("Config: {}", config);
    }
    println!("程序继续执行...");
}
```

## 3. 使用第三方 crate 实现构造器

虽然 Rust 本身没有内建的包级 `init` 函数，但可以借助第三方库（例如 [ctor](https://crates.io/crates/ctor)）实现全局构造器。
该 crate 允许你标记某些函数，在 `main()` 之前自动执行。
不过这种方法需要谨慎使用，因为它引入了隐式的初始化顺序，可能会影响程序的可读性和维护性：

```rust:path/to/file
use ctor::ctor;

#[ctor]
fn global_init() {
    println!("全局构造器执行：初始化全局状态。");
}

fn main() {
    println!("主函数执行...");
}
```

---

## 总结

- **Rust 没有内置类似 Golang 的 `init()` 自动调用机制。**
- 推荐的做法是通过 **显式初始化**（在 `main()` 中调用各模块的初始化函数）来确保初始化顺序和逻辑的清晰。
- 对于全局变量的延迟初始化，可使用 [`lazy_static`](https://crates.io/crates/lazy_static)
或 [`once_cell`](https://crates.io/crates/once_cell) 等工具。
- 如果确实需要在程序启动前执行全局代码，也可以通过第三方 crate（如 `ctor`）实现，
- 但不属于官方推荐的方案。

这种显式初始化的方式符合 Rust 程序员倾向于透明控制流的编程风格，也有助于避免因隐式依赖所带来的潜在问题。
