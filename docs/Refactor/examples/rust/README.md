# Rust 形式化系统示例库

本目录包含使用 Rust 编写的示例，展示 Rust 的类型系统、所有权模型和并发特性如何支持形式化方法。

## 文件说明

| 文件 | 内容 | 对应理论 |
|------|------|----------|
| `ownership.rs` | 所有权系统、借用检查、生命周期 | 线性类型论、资源管理 |
| `type_system.rs` | 高级类型系统特性（泛型、Trait、关联类型） | 类型论、子类型 |
| `async.rs` | 异步编程和 Future 机制 | 计算理论、并发模型 |
| `concurrent_patterns.rs` | 并发模式和线程安全 | 进程演算、并发理论 |

## 运行要求

- Rust (版本 ≥ 1.75.0)
- Cargo 构建工具

## 编译与运行

```bash
# 编译单个文件
rustc --edition 2021 ownership.rs -o ownership
./ownership

# 或使用 Cargo 创建项目
cargo new rust_examples
cd rust_examples
# 将示例文件复制到 src/bin/ 目录
cargo run --bin ownership
```

## 学习路径

1. **基础**: 从 `ownership.rs` 开始，理解 Rust 的核心特性
2. **进阶**: 阅读 `type_system.rs`，掌握高级类型技巧
3. **异步**: 查看 `async.rs`，学习现代异步编程
4. **并发**: 研究 `concurrent_patterns.rs`，理解线程安全

## 相关资源

- [The Rust Programming Language](https://doc.rust-lang.org/book/)
- [Rust by Example](https://doc.rust-lang.org/rust-by-example/)
- [Rustonomicon](https://doc.rust-lang.org/nomicon/)（高级主题）
