# Formal Science 自动化工具集 🔧

> **目录**: 用于文档质量保证、自动化处理和分析的工具脚本  
> **语言**: Python 3.8+  
> **状态**: 🚀 开发中

---

## 📋 目录

- [1 工具列表](#1-工具列表)
  - [1.1 已实现](#11-已实现)
    - [1.1.1 链接检查器Link Validator](#111-链接检查器link-validator)
  - [1.2 计划开发](#12-计划开发)
    - [2.2.1 格式验证器Format Checker](#221-格式验证器format-checker)
    - [2.2.2 概念关系图谱生成器Graph Builder](#222-概念关系图谱生成器graph-builder)
    - [2.2.3 主权矩阵分析器Sovereignty Analyzer](#223-主权矩阵分析器sovereignty-analyzer)
- [2 快速开始](#2-快速开始)
  - [2.1 环境要求](#21-环境要求)
  - [2.2 安装依赖](#22-安装依赖)
  - [2.3 运行测试](#23-运行测试)
- [3 工具开发进度](#3-工具开发进度)
- [4 本周目标Week 1](#4-本周目标week-1)
- [5 贡献指南](#5-贡献指南)
  - [5.1 添加新工具](#51-添加新工具)
  - [5.2 代码规范](#52-代码规范)
- [6 文件结构](#6-文件结构)
- [7 相关文档](#7-相关文档)
- [8 更新日志](#8-更新日志)
  - [8.1 -10-25](#81--10-25)

---

## 1 工具列表

### 1.1 已实现

#### 1.1.1 链接检查器Link Validator

**功能**: 自动检查所有markdown文件的链接有效性

**使用方法**:

```bash
# 基本用法（检查Concept/目录）
python tools/link_validator.py

# 指定目录
python tools/link_validator.py --dir docs/

# 保存详细报告
python tools/link_validator.py --report link_report.md
```

**检查内容**:

- ✅ 内部文件链接
- ✅ 锚点链接（#section）
- ✅ 相对路径链接
- ⏭️  外部链接（跳过）

**输出示例**:

```text
═══════════════════════════════════════
        链接验证报告           
═══════════════════════════════════════

📁 扫描文件: 52
🔗 总链接数: 347
✅ 有效链接: 342
❌ 失效链接: 5
📊 成功率: 98.6%
```

---

### 1.2 计划开发

#### 2. 目录生成器（TOC Generator）

**功能**: 自动为长文档生成目录

**计划用法**:

```bash
# 为单个文件生成目录
python tools/toc_generator.py Concept/CONCEPT_CROSS_INDEX.md

# 批量处理
python tools/toc_generator.py Concept/*.md

# 指定最大层级
python tools/toc_generator.py --max-level 3 Concept/*.md
```

**状态**: ⏳ 待开发（预计3小时）

---

#### 2.2.1 格式验证器Format Checker

**功能**: 检查文档格式规范性

**计划检查项**:

- 标题层级（不能跳级）
- 代码块闭合
- 多余空格/符号
- 标题唯一性

**状态**: ⏳ 待开发（预计3小时）

---

#### 2.2.2 概念关系图谱生成器Graph Builder

**功能**: 生成交互式概念关系图

**技术栈**: Python + NetworkX + Pyvis/D3.js

**状态**: ⏳ 待开发（预计20小时）

---

#### 2.2.3 主权矩阵分析器Sovereignty Analyzer

**功能**: 分析虚拟化技术的九维主权值

**状态**: ⏳ 待开发（预计15小时）

---

## 2 快速开始

### 2.1 环境要求

```bash
Python 3.8+
```

### 2.2 安装依赖

```bash
# 基础依赖（可选，增强显示效果）
pip install rich

# 完整依赖（开发所有工具）
pip install -r tools/requirements.txt
```

### 2.3 运行测试

```bash
# 测试链接检查器
cd E:/_src/FormalScience
python tools/link_validator.py

# 如果一切正常，应该看到验证报告
```

---

## 3 工具开发进度

```text
Phase 6 进度: 16.7% (1/6 工具完成)

✅ Link Validator     [████████████████████] 100%
⏳ TOC Generator      [                    ]   0%
⏳ Format Checker     [                    ]   0%
⏳ Graph Builder      [                    ]   0%
⏳ Sovereignty Analyzer[                    ]   0%
⏳ Decision Support   [                    ]   0%
```

---

## 4 本周目标Week 1

- [x] 创建tools目录
- [x] 实现链接检查器
- [ ] 测试链接检查器
- [ ] 实现目录生成器
- [ ] 实现格式验证器

---

## 5 贡献指南

### 5.1 添加新工具

1. 在 `tools/` 目录创建脚本
2. 遵循命名规范: `tool_name.py`
3. 添加文档注释和使用说明
4. 在本README中更新工具列表

### 5.2 代码规范

- Python 3.8+ 类型注解
- Docstring（Google风格）
- 命令行参数支持（argparse）
- 错误处理和友好提示

---

## 6 文件结构

```text
tools/
├── README.md                    # 本文件
├── requirements.txt             # Python依赖
│
├── link_validator.py            # ✅ 链接检查器
├── toc_generator.py             # ⏳ 目录生成器
├── format_checker.py            # ⏳ 格式验证器
├── graph_builder.py             # ⏳ 图谱生成器
├── sovereignty_analyzer.py      # ⏳ 主权矩阵分析器
└── decision_support.py          # ⏳ 决策支持系统
```

---

## 7 相关文档

- [下一阶段路线图](../Concept/NEXT_PHASE_ROADMAP_2025-10.md)
- [立即行动计划](../Concept/IMMEDIATE_ACTION_PLAN.md)
- [项目完成报告](../Concept/PROJECT_FINAL_SUMMARY.md)

---

## 8 更新日志

### 8.1 -10-25

- ✅ 创建tools目录
- ✅ 实现链接检查器v1.0
- ✅ 编写工具文档

---

**维护者**: FormalScience团队  
**最后更新**: 2025-10-25  
**版本**: v0.1.0
