# Rust panic

在 Rust 中，`panic` 是用于表示程序遇到了不可恢复错误的机制，其运行时行为主要涉及以下几个方面：

---

## 1. 引发 panic

当调用 `panic!` 宏或者运行时出现了不可恢复的错误时，会触发一次 panic。
这通常表明程序遇到了一种预期之外的情形。比如：

```rust:src/main.rs
fn might_fail(divisor: i32) {
    if divisor == 0 {
        panic!("除数不能为零");
    }
    println!("{}", 10 / divisor);
}

fn main() {
    might_fail(0);
}
```

在上面的代码中，传入 0 会直接调用 `panic!`，从而触发 panic 行为。

---

## 2. 栈展开（Stack Unwinding）

默认情况下（尤其是在调试模式下），Rust 采用**栈展开**的策略来处理 panic。
具体表现为：

- **调用 panic hook**  
  当 panic 发生时，首先会调用一个预设的 **panic hook**（可以通过 `std::panic::set_hook` 自定义），这个 hook 负责输出 panic 的信息（例如出错位置、堆栈跟踪等）。

- **展开调用栈**  
  Panic 会沿着当前线程的调用栈向上展开。
  在这个过程中，Rust 会依次调用各个栈帧中局部变量的析构函数（`Drop` 实现），以便进行必要的资源清理。
  这确保了动态分配的内存或其它资源能被正确释放，即便程序中断执行。

- **终止线程**  
  展开过程会一直进行，直到到达线程的入口点。
  如果在展开过程中某一层调用使用了 `catch_unwind` 捕获了 panic 信息，则可以恢复控制流，否则该线程会退出。
  如果触发 panic 的是主线程，通常会导致整个程序终止。

---

## 3. panic=abort 策略

可以通过修改编译器选项（例如在 Cargo.toml 中设置 `panic = "abort"`）来改变 panic 的行为，使其直接中止程序而不进行栈展开。
其特点是：

- **立即终止程序**  
  发生 panic 后，不调用任何析构函数，整个程序会立刻中止。
  这种策略常用于对代码体积有严格要求或性能要求极高的场景，但会牺牲部分安全性，比如局部资源不会被清理。

```toml
# Cargo.toml
[profile.release]
panic = "abort"
```

---

## 4. 捕获 panic

Rust 提供了 `std::panic::catch_unwind` 函数，可以在一个闭包中捕获 panic，从而防止 panic 迅速向上传播终止线程。
示例如下：

```rust:src/main.rs
use std::panic;

fn main() {
    let result = panic::catch_unwind(|| {
        println!("即将 panic");
        panic!("oops!");
    });

    match result {
        Ok(_) => println!("没有 panic"),
        Err(err) => println!("捕获到 panic: {:?}", err),
    }
}
```

在这个例子中，闭包中的 panic 被 `catch_unwind` 捕获，程序得以继续运行。

---

## 小结

- **触发 panic**：调用 `panic!` 或触发不可恢复错误时发生。
- **栈展开**：默认策略为展开调用栈，调用每个栈帧中的析构函数进行资源清理，并最终使线程终止。
- **panic=abort 模式**：可以配置为直接中止程序，跳过栈展开阶段，适用于某些特殊场景。
- **panic 捕获**：使用 `std::panic::catch_unwind` 可以捕获 panic 信息，防止它终止整个线程或程序。

这种设计让 Rust 在面对严重错误时能灵活处理：既提供了安全清理的机制，也允许在需要时完全放弃清理而快速终止程序。
