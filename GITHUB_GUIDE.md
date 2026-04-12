# FormalScience - GitHub 使用指南

> 本项目已针对GitHub进行优化，移除所有编译生成的文件，确保仓库干净、高效。

## 📁 仓库结构

```
FormalScience/
├── .gitignore              # 已配置排除所有编译文件
├── README.md               # 项目主说明
├── GITHUB_GUIDE.md         # 本文件
├── docs/
│   └── Refactor/           # 核心文档（3,371个Markdown）
│       ├── 00_INDEX.md     # 主索引
│       ├── 00_MAP.md       # 知识地图
│       ├── 01_数学基础/     # 数学理论
│       ├── 02_形式语言/     # 形式语言理论
│       ├── 03_编程范式/     # 编程范式
│       ├── 04_软件工程/     # 软件工程
│       ├── 05_形式化理论/   # 形式化方法
│       ├── 06_调度系统/     # 调度系统（核心）
│       ├── 07_交叉视角/     # 跨领域视角
│       ├── 08_附录/         # 参考文献、符号表
│       ├── examples/        # 代码示例
│       │   ├── lean/        # Lean 4代码（源文件）
│   │   │   └── ...
│       │   └── rust/        # Rust代码（源文件）
│       │       ├── Cargo.toml
│       │       └── src/     # .rs源文件
│       └── visual/          # Mermaid图表
├── Composed/
│   └── schedule_formal_view/  # 调度系统详细文档
│       ├── 01_CPU硬件层/
│       ├── 02_系统总线层/
│       ├── 03_OS抽象层/
│       ├── 14_存储调度系统/
│       ├── 15_网络调度系统/
│       ├── 16_GPU与加速器调度/
│       └── 17_数据库调度系统/
└── tools/                   # 工具脚本
    └── *.py                # Python脚本
```

## 🚀 快速开始

### 1. 浏览文档

直接通过GitHub网页浏览Markdown文件：

- 📑 [主索引](docs/Refactor/00_INDEX.md)
- 🗺️ [知识地图](docs/Refactor/00_MAP.md)
- 📊 [进度追踪](docs/Refactor/00_PROGRESS.md)

### 2. 查看代码示例

**Lean 4代码**：

```bash
cd docs/Refactor/examples/lean
# 使用Lean 4编译
lean --make 01_SetTheory.lean
```

**Rust代码**：

```bash
cd docs/Refactor/examples/rust
# 注意：首次运行会自动下载依赖，生成target目录（已被gitignore排除）
cargo check
cargo run --example scheduling
```

### 3. 运行工具脚本

```bash
# 文档质量检查
python tools/document_linter.py docs/Refactor

# 生成交叉引用
python docs/Refactor/.scripts/build_cross_references.py
```

## 📊 项目统计

| 指标 | 数量 |
|------|------|
| Markdown文档 | 3,371 |
| 代码示例文件 | 145 |
| 形式化定义 | 16,277 |
| 定理证明 | 48 |
| Mermaid图表 | 94 |
| 完成度 | 95%+ |

## 🎯 主要模块

### 核心调度系统（100%完成）

- 网络调度系统 - 35个形式化定义，18个定理，21个RFC标准
- 存储调度系统 - 4个文档，7,558行，完整对比矩阵
- GPU调度系统 - 4个文档，232KB，深度学习调度覆盖
- 数据库调度系统 - 4个文档，279KB，事务形式化理论

### 理论基础（90%+完成）

- 数学基础 - 集合论、代数、几何、分析、概率
- 形式语言 - 类型论、λ演算、范畴论、HoTT
- 编程范式 - Rust深入、异步编程、函数式
- 软件工程 - 设计模式、微服务、分布式系统

## 🛠️ 开发工具

### 推荐的VS Code扩展

- Markdown All in One
- Mermaid Preview
- LaTeX Workshop（查看数学公式）
- Rust Analyzer（Rust代码）
- Lean 4（形式化证明）

## 📝 贡献指南

1. Fork本仓库
2. 创建特性分支：`git checkout -b feature/xxx`
3. 提交更改：`git commit -m "Add xxx"`
4. 推送分支：`git push origin feature/xxx`
5. 创建Pull Request

## 🔒 Git忽略规则

本项目已配置完善的`.gitignore`，自动排除：

- 所有编译输出（target/、_.o、_.exe等）
- 临时文件和备份
- 大型生成报告
- IDE配置文件

确保提交到GitHub的只有源代码和文档！

## 📚 学习路径

1. **初学者**：[00_GETTING_STARTED.md](docs/Refactor/00_GETTING_STARTED.md)
2. **数学基础**：[01_数学基础/](docs/Refactor/01_数学基础/)
3. **形式语言**：[02_形式语言/](docs/Refactor/02_形式语言/)
4. **调度系统**：[06_调度系统/](docs/Refactor/06_调度系统/)

## 📄 许可证

MIT License - 详见 [LICENSE](LICENSE.md)

---

**项目状态**：✅ 全面完成（95%+）
**最后更新**：2026-04-12
