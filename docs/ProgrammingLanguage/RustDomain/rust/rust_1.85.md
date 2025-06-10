# Rust 1.85.0 新特性

Rust 1.85.0 发布了多项新特性和改进，以下是主要更新内容：

## 目录

- [Rust 1.85.0 新特性](#rust-1850-新特性)
  - [目录](#目录)
  - [语言特性](#语言特性)
  - [标准库和工具链](#标准库和工具链)

## 语言特性

- **异步闭包支持**：
  - Rust 现在支持异步闭包 `async || {}`，调用时返回 `futures`。
  - 标准库 prelude 中新增了 `AsyncFn`、`AsyncFnMut` 和 `AsyncFnOnce` 三个 trait，
  - 解决了之前无法让内部异步块借用闭包捕获值和用 `Fn` traits 正确表达高阶函数签名返回 `Future` 的问题。

- **隐藏 trait 实现诊断信息**：
  - 新增 `#[diagnostic::do_not_recommend]` 属性，
  - 可以让编译器在诊断消息中不显示注解的 trait 实现，避免给库作者提供无用或误导性的建议。

- **元组的 `FromIterator` 和 `Extend`**：
  - 现在这些特性扩展到了更多长度的元组，
  - 从单元素 `(T,)` 到 12 个元素 `(T1, T2, .., T11, T12)`，可以使用 `collect()` 同时将迭代器数据分散到多个集合中。

- **`std::env::home_dir()` 更新**：
  - 该函数多年来一直被弃用，因其在某些 Windows 配置下表现异常。现在更新其行为作为 bug 修复，后续版本将移除弃用状态。

- **稳定的 API**：
  - 多个 API 达到稳定状态，部分 API 在常量上下文中也稳定可用。

- **语言改进**：
  - 现在可以在某些内置属性中使用宏来表示值，主要允许在 `#[doc]` 属性中调用宏。例如，可以在 crate 中包含外部文档，如下所示：

```rust
#![doc = include_str!("README.md")]
```

- 现在可以在 `const fn` 中在无大小切片类型（以及包含无大小切片的类型）之间进行转换。
- 现在可以在 `impl Trait` 中使用多个泛型生命周期，而这些生命周期不需要明确地超出彼此。在代码中，现在可以有 `impl Trait<'a, 'b>`，而之前只能有 `impl Trait<'a, 'b> where 'b: 'a`。

## 标准库和工具链

- **Cargo 改进**：
  - Cargo 现在会去重编译器诊断信息，当使用 `cargo test` 等并行调用 `rustc` 时，终端上的诊断信息将不会重复。
  - `cargo metadata` 的包定义现在包括清单中的 `"default_run"` 字段。
  - 添加了 `cargo d` 作为 `cargo doc` 的别名。
  - 添加了 `{lib}` 作为 `cargo tree` 的格式化选项，用于打印包的 `"lib_name"`。

- **Rustdoc 改进**：
  - 添加了“Go to item on exact match”搜索选项。
  - “Implementors”部分不再显示冗余的方法定义。
  - 特性实现默认展开，以便工具如浏览器中的 `CTRL+F` 更容易搜索。
  - 文档链接现在正确解析通过类型别名的关联项（例如方法）。
  - 标记为 `#[doc(hidden)]` 的特性将不再出现在“Trait Implementations”部分。

- **兼容性更新**：
  - 标准库函数返回 `io::Error` 时不再使用 `ErrorKind::Other` 变体，以更好地反映这些错误可以分类为更新的更具体的 `ErrorKind` 变体，并且它们不代表用户错误。
  - 在 Windows 上使用 `process::Command` 时，环境变量名称现在按预期行为处理，之前使用 `Command` 会导致环境变量被 ASCII 大写化。
  - Rustdoc 现在会警告使用未以前缀 `rustdoc::` 的 rustdoc lints。
  - `RUSTFLAGS` 不再为构建脚本设置。构建脚本应改用 `CARGO_ENCODED_RUSTFLAGS`。

这些更新和新特性使得 Rust 1.85.0 在性能、功能和开发体验上都有了显著提升。

如果您有其他问题或需要进一步的信息，请随时告知。
