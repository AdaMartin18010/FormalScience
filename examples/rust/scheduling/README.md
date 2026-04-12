# Rust Scheduling Examples - 调度算法示例

> **目录**: `examples/rust/scheduling/`
> **用途**: 调度算法 Rust 实现示例
> **最后更新**: 2026-04-12

---

## 📁 示例文件

| 文件 | 描述 |
|------|------|
| `async_io.rs` | 异步 I/O 调度 |
| `buddy_allocator.rs` | 伙伴分配器 |
| `priority_scheduler.rs` | 优先级调度器 |
| `round_robin.rs` | 时间片轮转调度 |
| `thread_pool.rs` | 线程池实现 |

---

## 🚀 运行示例

```bash
# 运行特定示例
cargo run --example priority_scheduler
cargo run --example round_robin
cargo run --example thread_pool
cargo run --example buddy_allocator
cargo run --example async_io
```

---

## 🔗 相关链接

- [Rust Examples 首页](../README.md)
- [调度系统形式化视图](../../../Composed/schedule_formal_view/README.md)
- [Concurrency 并发示例](../concurrency/README.md)

---

**维护者**: FormalScience 团队
