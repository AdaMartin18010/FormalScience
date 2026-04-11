# FormalScience 性能基准测试

本目录包含 FormalScience 项目的性能基准测试套件，用于监控和优化各组件的性能表现。

## 📁 目录结构

```
benchmarks/
├── README.md                    # 本文件
├── lean_benchmarks.lean         # Lean 形式化证明性能测试
├── rust_benchmarks.rs           # Rust 调度系统性能测试
├── python_benchmarks.py         # Python 工具脚本性能测试
├── run_benchmarks.sh            # 一键运行所有测试脚本
└── results/                     # 测试结果存储目录
    ├── template.md              # 结果报告模板
    └── comparison_table.md      # 性能对比表格
```

## 🚀 快速开始

### 运行所有基准测试

```bash
# 赋予执行权限并运行
chmod +x run_benchmarks.sh
./run_benchmarks.sh
```

### 单独运行特定测试

```bash
# Lean 测试
cd ../ && lake build && time lake exe benchmark

# Rust 测试
cargo bench --manifest-path ../../FormalRE/Cargo.toml

# Python 测试
python python_benchmarks.py
```

## 📊 测试内容

### Lean 性能测试 (`lean_benchmarks.lean`)

| 测试项 | 描述 | 目标时间 |
|--------|------|----------|
| 定理证明检查 | 复杂定理的证明验证时间 | < 5s |
| 编译时间 | 项目整体编译耗时 | < 30s |
| 类型推断 | 复杂表达式的类型检查 | < 1s |
| 归约计算 | 表达式归约性能 | < 2s |

### Rust 性能测试 (`rust_benchmarks.rs`)

| 测试项 | 描述 | 目标时间 |
|--------|------|----------|
| 调度算法 | 核心调度算法执行时间 | < 10ms |
| 类型检查器 | 正则表达式类型检查 | < 5ms |
| 网络同步 | 多节点状态同步 | < 50ms |
| 内存分配 | 大规模数据结构操作 | < 20ms |

### Python 性能测试 (`python_benchmarks.py`)

| 测试项 | 描述 | 目标时间 |
|--------|------|----------|
| 文档生成 | Markdown/HTML 文档渲染 | < 5s |
| 链接检查 | 全站链接有效性检查 | < 30s |
| 代码统计 | 项目代码量统计 | < 10s |
| 依赖分析 | 模块依赖图生成 | < 15s |

## 📈 性能指标

### 关键性能指标 (KPIs)

1. **证明验证吞吐量**: 每秒验证的定理数量
2. **调度延迟**: 从请求到响应的时间 (P50, P95, P99)
3. **内存占用**: 峰值内存使用量
4. **并发处理能力**: 同时处理的请求数

### 基准配置

- **CPU**: 8 核心以上
- **内存**: 16GB 以上
- **存储**: SSD
- **Lean 版本**: 4.x
- **Rust 版本**: 1.75+
- **Python 版本**: 3.11+

## 🔄 CI/CD 集成

基准测试集成在 CI 流程中，每次提交自动运行：

```yaml
# .github/workflows/benchmark.yml
- name: Run Benchmarks
  run: |
    cd docs/Refactor/benchmarks
    ./run_benchmarks.sh
```

## 📝 结果解读

测试结果保存在 `results/` 目录，包含：

- `YYYYMMDD_HHMMSS_lean.json` - Lean 详细结果
- `YYYYMMDD_HHMMSS_rust.json` - Rust 详细结果
- `YYYYMMDD_HHMMSS_python.json` - Python 详细结果
- `YYYYMMDD_HHMMSS_summary.md` - 汇总报告

### 性能回归检测

当新结果比历史基线差 >10% 时，标记为性能回归：

```bash
# 对比历史结果
./run_benchmarks.sh --compare-with baseline.json
```

## 🛠️ 自定义测试

添加新的测试用例：

### Lean
```lean
benchmark "my_new_test" {
  -- 测试代码
  let result := myFunction input
  assert result = expected
}
```

### Rust
```rust
#[bench]
fn bench_my_function(b: &mut Bencher) {
    b.iter(|| my_function());
}
```

### Python
```python
def benchmark_my_function():
    """测试我的函数性能"""
    result = time_function(my_function, iterations=1000)
    return {"time_ms": result}
```

## 📚 参考文档

- [Criterion.rs 文档](https://bheisler.github.io/criterion.rs/book/)
- [Lean 性能优化指南](https://lean-lang.org/lean4/doc/perf.html)
- [Python timeit 模块](https://docs.python.org/3/library/timeit.html)

## 🤝 贡献

添加新的基准测试时，请确保：

1. 测试覆盖关键代码路径
2. 设置合理的性能目标
3. 更新本文档
4. 提交历史基线数据

---

*最后更新: 2026-04-11*
