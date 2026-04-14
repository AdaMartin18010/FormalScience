# docs/Refactor 目录清理报告

**日期**: 2026-04-14
**范围**: `docs/Refactor/` 及其子目录
**执行者**: Kimi Code CLI

---

## 1. 执行摘要

本次清理针对 `docs/Refactor/` 中存在的**重复/嵌套目录**、**占位符目录**和**命名不一致**问题进行了识别与修复。主要成果：

- 移除 **7 个重复或空占位目录**
- 重命名 **1 个嵌套命名冲突目录** (`docs/` → `.guides/`)
- 修复 **9 个 Markdown 文件**中的内部交叉引用链接（移除指向已删除 `FormalRE` 和 `Matter` 目录的断链）
- 更新 **3 个元数据/索引文件**以反映目录变更

---

## 2. 重复目录识别与处理

### 2.1 内容重复目录（已移除）

| 目录 | 重复对象 | 处理决定 | 理由 |
|------|----------|----------|------|
| `docs/Refactor/FormalRE/` | `docs/Refactor/06_调度系统/` | **移除** | `FormalRE` 下 4 个子目录（操作系统、硬件、算法复杂度、调度系统）共 5 个文件，其主题与 `06_调度系统/` 各子章完全重叠，且主章节文件更大、结构更规范（含 category/subcategory/order 等元数据）。 |
| `docs/Refactor/Matter/` | `docs/Refactor/06_调度系统/` | **移除** | 仅含 `01_操作系统/01.4_进程调度.md`，与 `06_调度系统/03_OS调度/03.1_进程调度.md` 重复。此外，`06_调度系统` 大量文件引用了 `Matter` 中并不存在的文件（如 `../../Matter/01_操作系统/01.7_IO系统.md`），移除 `Matter` 并清理引用反而修复了既有断链。 |

### 2.2 占位符/空壳目录（已移除）

| 目录 | 内容 | 处理决定 |
|------|------|----------|
| `docs/Refactor/examples/rust/scheduler/` | 仅 1 个 README.md（587 B，占位状态，已指向 `scheduling/`） | **移除** |
| `docs/Refactor/examples/rust/concurrent/` | 仅 1 个 README.md（601 B，占位状态） | **移除** |
| `docs/Refactor/examples/rust/distributed/` | 仅 1 个 README.md（512 B，占位状态） | **移除** |
| `docs/Refactor/.github/badges/` | 仅 1 个 README.md（指向 `assets/badges/`，无实际徽章资源） | **移除** |
| `docs/Refactor/projects/petri_net_simulator/__pycache__/` | Python 缓存文件（已在 `.gitignore` 中排除） | **移除** |

### 2.3 嵌套命名冲突目录（已重命名）

| 原路径 | 新路径 | 处理决定 | 理由 |
|--------|--------|----------|------|
| `docs/Refactor/docs/` | `docs/Refactor/.guides/` | **重命名** | `docs/` 嵌套在 `docs/Refactor/` 下造成语义重复与路径混乱。该目录仅存放 3 个元数据文件（CI/CD 指南、Docker 设置、文档质量报告），重命名为 `.guides/` 更符合其"项目内部指南"的定位。 |

---

## 3. 受影响的文件及链接修复

### 3.1 移除 `FormalRE` / `Matter` 引用（9 个文件）

以下 `06_调度系统` 章节文件的原 `related:` YAML 元数据及正文交叉引用块中包含了指向已删除目录的链接，已将其清理：

1. `06_调度系统/01_调度理论基础/01.1_调度模型抽象.md`
2. `06_调度系统/01_调度理论基础/01.2_调度算法分析.md`
3. `06_调度系统/01_调度理论基础/01.3_调度等价性.md`
4. `06_调度系统/02_硬件调度/02.2_GPU调度.md`
5. `06_调度系统/02_硬件调度/02.3_加速器调度.md`
6. `06_调度系统/03_OS调度/03.2_内存调度.md`
7. `06_调度系统/03_OS调度/03.3_IO调度.md`
8. `06_调度系统/04_分布式调度/04.2_大数据调度.md`
9. `06_调度系统/04_分布式调度/04.3_跨层调度协同.md`

**修复内容**：

- 从 `related:` 数组中删除所有 `"Matter: ..."` 和 `"FormalRE: ..."` 条目
- 删除正文中的 `> **交叉引用**: 源Matter中的...` 引用块（这些块中包含的链接大多早已指向不存在的文件）

### 3.2 更新 `.guides/` 重命名引用（3 个文件）

- `docs/Refactor/README.md`
  - 更新表格中的风格指南路径：`docs/document_style_guide.md` → `.guides/document_style_guide.md`
  - 更新正文引用路径
  - 更新文件树示例中的目录名
- `docs/Refactor/.guides/document_quality_implementation_report.md`
  - 更新自引用路径：`docs/Refactor/docs/...` → `docs/Refactor/.guides/...`
- `docs/Refactor/100_FINAL_COMPLETION_REPORT.md`
  - 更新路径引用

---

## 4. 命名不一致清单及建议更名方案

> **注意**：以下问题已在报告中记录，但**尚未执行批量重命名**，以避免大规模断链。建议在下一轮有自动化链接修复能力时再实施。

### 4.1 顶层命名风格不统一

| 现状 | 问题 | 建议 |
|------|------|------|
| `01_数学基础`, `02_形式语言`, `03_编程范式` ... `15_社会科学形式化` | 15 个章节使用 `NN_中文名` 编号格式 | 保持统一 ✅ |
| `RFC标准` | 无编号、中英混合 | 建议改为 `16_RFC标准` 或并入 `网络协议` |
| `网络协议` | 无编号纯中文 | 建议改为 `17_网络协议` 或作为 `16_RFC标准` 的子目录 |
| `FormalRE`（项目根也有同名目录） | 英文缩写、无编号 | 建议评估是否与 `02_形式语言` / `05_形式化理论` 合并，或统一为 `18_形式化需求工程` |
| `Matter`（已删除） | 英文、与主题体系脱节 | 已移除 ✅ |
| `quickref`, `benchmarks`, `tests`, `tools`, `scripts` | 小写英文、无编号 | 建议统一加前缀，如 `99_quickref`、`98_benchmarks`，或保持现状但写入规范文档 |
| `assets`, `examples`, `website`, `i18n` | 通用工程目录名，与编号章节并列 | 建议移入 `.support/` 或 `.project/` 等元目录下，减少顶层噪音 |

### 4.2 功能重叠目录

| 目录 A | 目录 B | 关系 | 建议 |
|--------|--------|------|------|
| `benchmarks/` | `data/benchmarks/` | 前者放基准测试代码（Lean/Python/Rust/Shell），后者放 CSV/JSON 结果数据 | 建议将 `data/benchmarks/` 合并为 `benchmarks/results/` 的子目录，统一数据入口 |
| `scripts/` | `tools/scripts/` | 前者为 Shell 脚本（dev/docker/release），后者为 Python 工具脚本（check_links/build_index） | 建议按职能拆分：`scripts/` → `.devops/`（部署/构建脚本），`tools/scripts/` 保持为工具脚本 |
| `assets/images/` | `website/images/` | 前者有 `hero-bg.svg` 和 `screenshot-placeholder.svg`，后者只有 `placeholder.svg` | 建议合并到 `assets/images/`，`website/` 通过相对路径引用，避免资源重复 |
| `assets/badges/` | `.github/badges/`（已删除） | 已清理 ✅ | — |

### 4.3 深度与编号不一致

- 当前 `docs/Refactor` 的文档深度已较为平整（Markdown 文件最大深度为 4），此前审计报告中提到的 8+ 层深度问题（如 `01_数学基础/02_形式语言/04_范畴论/`）**已不存在**，说明该问题在早前某次清理中已解决。
- 编号文件格式目前统一为 `NN.N_标题.md`，但少数文件仍缺少编号（主要在 `RFC标准/`、`网络协议/`、`examples/` 下的 README）。

---

## 5. 断链修复明细

### 5.1 本次操作**修复**的既有断链

在清理 `Matter` 目录时，发现 `06_调度系统` 中的多个文件引用了 `Matter` 子目录下**实际并不存在的文件**。清理引用后，这些断链被一并消除：

| 源文件 | 已删除的断链目标 |
|--------|------------------|
| `03.3_IO调度.md` | `../../Matter/01_操作系统/01.7_IO系统.md` |
| `03.3_IO调度.md` | `../../Matter/01_操作系统/01.8_磁盘调度.md` |
| `03.2_内存调度.md` | `../../Matter/01_操作系统/01.5_内存管理.md` |
| `03.2_内存调度.md` | `../../Matter/01_操作系统/01.6_虚拟内存.md` |
| `02.2_GPU调度.md` | `../../Matter/01_计算机组成原理/04.2_GPU架构.md` |
| `02.2_GPU调度.md` | `../../Matter/01_计算机组成原理/04.3_CUDA编程模型.md` |
| `02.3_加速器调度.md` | `../../Matter/01_计算机组成原理/04.4_TPU架构.md` |
| `02.3_加速器调度.md` | `../../Matter/01_计算机组成原理/04.5_AI加速器.md` |
| `04.2_大数据调度.md` | `../../Matter/02_分布式系统/02.6_Spark调度.md` |
| `04.2_大数据调度.md` | `../../Matter/02_分布式系统/02.7_Flink调度.md` |
| `04.3_跨层调度协同.md` | `../../Matter/02_分布式系统/02.8_跨层优化.md` |
| `01.1_调度模型抽象.md` | `../../Matter/02_分布式系统/02.3_分布式调度.md` |
| `01.3_调度等价性.md` | `../../Matter/02_分布式系统/02.3_分布式调度.md#调度等价性` |
| `01.2_调度算法分析.md` | `../../Matter/02_分布式系统/02.3_分布式调度.md#调度算法复杂度` |

### 5.2 本次操作**造成但已同步修复**的链接变更

| 变更 | 受影响文件 | 修复方式 |
|------|------------|----------|
| `docs/` → `.guides/` | `README.md` | 更新 3 处相对路径引用及文件树 |
| `docs/` → `.guides/` | `.guides/document_quality_implementation_report.md` | 更新自引用路径 |
| `docs/` → `.guides/` | `100_FINAL_COMPLETION_REPORT.md` | 更新路径引用 |

---

## 6. 操作命令日志

```powershell
# 移除重复/占位目录
Remove-Item -Recurse -Force docs/Refactor/examples/rust/scheduler
Remove-Item -Recurse -Force docs/Refactor/examples/rust/concurrent
Remove-Item -Recurse -Force docs/Refactor/examples/rust/distributed
Remove-Item -Recurse -Force docs/Refactor/.github/badges
Remove-Item -Recurse -Force docs/Refactor/projects/petri_net_simulator/__pycache__
Remove-Item -Recurse -Force docs/Refactor/FormalRE
Remove-Item -Recurse -Force docs/Refactor/Matter

# 重命名嵌套 docs 目录
Rename-Item docs/Refactor/docs .guides

# 链接修复：Python 脚本批量处理 9 个 06_调度系统文件
# - 清理 related 中的 Matter/FormalRE 条目
# - 删除正文交叉引用块
```

---

## 7. 后续建议

1. **建立目录命名规范文档**：明确顶层目录应采用 `NN_中文名` 还是统一放入 `.project/` / `.support/` 等元目录。
2. **清理 `data/benchmarks` 与 `benchmarks/results` 的数据边界**：避免用户困惑。
3. **合并 `scripts/` 与 `tools/scripts`**：或至少通过 README 清晰说明两个目录的职责边界。
4. **迁移 `assets/images/` 与 `website/images`**：将 `website/images/placeholder.svg` 移入 `assets/images/` 并更新 `website/` 中的 HTML 引用。
5. **处理 `RFC标准` 与 `网络协议`**：二者内容高度相关（协议分析 vs RFC 原文），建议统一编号并建立清晰的从属关系。

---

**报告结束**
