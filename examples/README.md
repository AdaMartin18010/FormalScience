# Examples - 代码示例

> **目录**: `examples/`  
> **用途**: 形式科学相关的代码示例和实现  
> **最后更新**: 2026-04-12

---

## 📁 目录结构

```
examples/
├── lean/          # Lean 形式化证明示例
└── rust/          # Rust 代码示例
    ├── async/         # 异步编程示例
    ├── concurrency/   # 并发编程示例
    ├── scheduling/    # 调度算法示例
    └── system/        # 系统编程示例
```

---

## 🚀 快速开始

### Rust 示例

```bash
cd examples/rust/scheduling
cargo run --example priority_scheduler
```

### Lean 示例

```bash
cd examples/lean
lean --make <file.lean>
```

---

## 📚 示例分类

### 异步编程 (async/)
- `futures_pin.rs` - Future 和 Pin 基础
- `tokio_examples.rs` - Tokio 运行时示例
- `waker_executor.rs` - 自定义 Waker 和执行器

### 并发编程 (concurrency/)
- `atomic_memory.rs` - 原子操作和内存序
- `channels.rs` - 通道通信模式
- `locks.rs` - 锁和同步原语
- `lock_free.rs` - 无锁数据结构

### 调度算法 (scheduling/)
- `async_io.rs` - 异步 I/O 调度
- `buddy_allocator.rs` - 伙伴分配器
- `priority_scheduler.rs` - 优先级调度器
- `round_robin.rs` - 时间片轮转调度
- `thread_pool.rs` - 线程池实现

### 系统编程 (system/)
- `bpf_program.rs` - BPF 程序示例
- `memory_management.rs` - 内存管理
- `syscalls.rs` - 系统调用

---

## 🔗 相关资源

- [调度系统形式化视图](../Composed/schedule_formal_view/README.md)
- [类型系统形式化视图](../Composed/formal_lang_view/README.md)
- [docs/Refactor 示例](../docs/Refactor/examples/)

---

## 📝 贡献指南

添加新示例时，请确保：
1. 代码有完整的文档注释
2. 包含运行说明
3. 与项目主题相关

---

**维护者**: FormalScience 团队  
**许可证**: MIT
