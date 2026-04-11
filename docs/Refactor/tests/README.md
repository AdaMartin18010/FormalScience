# FormalScience 测试验证套件

## 概述

本测试套件用于验证 FormalScience 项目中 Lean 代码、Rust 代码和 Markdown 文档的正确性、一致性和完整性。

## 测试结构

```
tests/
├── README.md              # 本文件
├── lean_tests.lean        # Lean 代码测试
├── rust_tests.rs          # Rust 代码测试
├── validate_md.py         # Markdown 验证脚本
├── coverage_report.py     # 覆盖率报告生成
├── run_all.sh             # Linux/Mac 一键测试脚本
└── run_all.bat            # Windows 一键测试脚本
```

## 测试类型

### 1. Lean 测试 (`lean_tests.lean`)

验证所有 Lean 示例代码：

- **基础数学测试**：自然数、整数、代数结构
- **范畴论测试**：范畴定义、函子、自然变换
- **类型论测试**：类型系统、依赖类型
- **调度器测试**：工作流调度算法验证
- **证明实践测试**：定理证明正确性

运行方式：

```bash
# 单个文件测试
lean --run lean_tests.lean

# 验证所有 Lean 示例
lake build  # 如果使用 Lake 构建系统
```

### 2. Rust 测试 (`rust_tests.rs`)

验证所有 Rust 示例代码：

- **单元测试**：函数级别测试
- **集成测试**：模块间协作测试
- **文档测试**：代码示例验证

运行方式：

```bash
# 运行所有测试
cargo test

# 运行特定测试
cargo test test_ownership

# 生成覆盖率报告
cargo tarpaulin --out Html
```

### 3. Markdown 验证 (`validate_md.py`)

检查文档质量：

- ✅ Markdown 格式规范性
- ✅ 链接有效性检查
- ✅ 代码块闭合检查
- ✅ 标题层级一致性
- ✅ 图片引用有效性

运行方式：

```bash
python validate_md.py
python validate_md.py --fix  # 自动修复问题
```

### 4. 覆盖率报告 (`coverage_report.py`)

生成项目内容覆盖率：

- 文档覆盖率统计
- 代码示例覆盖率
- 可视化 HTML 报告
- 趋势分析图表

运行方式：

```bash
python coverage_report.py
python coverage_report.py --html --open
```

## 一键测试

### Windows

```batch
run_all.bat
```

### Linux/Mac

```bash
bash run_all.sh
```

## 测试覆盖范围

### Lean 示例文件

| 文件 | 描述 | 测试类型 |
|------|------|----------|
| `basic.lean` | 基础数学定义 | 定理证明、计算验证 |
| `category.lean` | 范畴论实现 | 函子律、自然变换 |
| `type_theory.lean` | 类型论基础 | 类型检查、归纳定义 |
| `scheduler.lean` | 调度器形式化 | 算法正确性证明 |
| `proof_practice.lean` | 证明练习 | 证明完整性检查 |

### Rust 示例文件

| 文件 | 描述 | 测试类型 |
|------|------|----------|
| `ownership.rs` | 所有权系统 | 内存安全、生命周期 |
| `async.rs` | 异步编程 | 并发正确性、超时处理 |
| `concurrent_patterns.rs` | 并发模式 | 线程安全、同步原语 |
| `type_system.rs` | 类型系统 | 泛型、trait 系统 |

### Markdown 文档

- 总计：1000+ 文档文件
- 主要目录：`docs/Matter/`, `docs/Refactor/`
- 验证内容：格式、链接、代码块

## CI/CD 集成

### GitHub Actions 示例

```yaml
name: Test Suite
on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3

      - name: Setup Lean
        uses: leanprover/lean-action@v1

      - name: Setup Rust
        uses: dtolnay/rust-action@stable

      - name: Setup Python
        uses: actions/setup-python@v4
        with:
          python-version: '3.11'

      - name: Run all tests
        run: bash docs/Refactor/tests/run_all.sh
```

## 测试结果说明

### 输出格式

```
═══════════════════════════════════════════════════════════
                   测试结果汇总
═══════════════════════════════════════════════════════════

✅ Lean 测试:     15/15 通过
✅ Rust 测试:     42/42 通过
✅ Markdown 检查: 1250/1250 通过
📊 代码覆盖率:    87.5%

═══════════════════════════════════════════════════════════
                   测试通过 ✓
═══════════════════════════════════════════════════════════
```

### 失败处理

当测试失败时：

1. 查看详细的错误日志
2. 定位到具体文件和行号
3. 修复问题后重新运行测试
4. 确保所有测试通过后再提交

## 扩展测试

### 添加新的 Lean 测试

```lean
-- 在 lean_tests.lean 中添加
@[test]
def test_new_feature : TestM Unit := do
  -- 测试逻辑
  assertEquals expected actual
```

### 添加新的 Rust 测试

```rust
#[cfg(test)]
mod new_tests {
    use super::*;

    #[test]
    fn test_new_feature() {
        assert_eq!(expected, actual);
    }
}
```

## 维护信息

- **创建日期**: 2026-04-11
- **维护者**: FormalScience 团队
- **更新频率**: 每次提交前运行
- **问题反馈**: 提交 Issue 到项目仓库

## 参考文档

- [Lean 4 手册](https://lean-lang.org/lean4/doc/)
- [Rust 测试指南](https://doc.rust-lang.org/book/ch11-00-testing.html)
- [Markdown 规范](https://commonmark.org/)
