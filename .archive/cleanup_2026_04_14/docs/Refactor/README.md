# FormalScience 文档质量标准体系

> **版本**: 1.0.0
> **创建日期**: 2026-04-12
> **状态**: 已完成

---

## 体系概览

本文档质量标准体系为 FormalScience 项目提供统一的文档规范、检查工具和规范化流程。

### 核心组件

| 组件 | 位置 | 功能 |
|------|------|------|
| **文档模板** | `.templates/` | 标准化文档结构模板 |
| **检查脚本** | `../tools/document_linter.py` | 自动化质量检查 |
| **规范化脚本** | `../tools/batch_normalize_documents.py` | 批量规范化 |
| **风格指南** | `.guides/document_style_guide.md` | 详细规范说明 |

---

## 文档模板

### 可用模板

| 模板 | 用途 | 文件 |
|------|------|------|
| 标准头部 | 文档元数据 | `document_header_template.md` |
| 理论体系 | 定义-定理-证明结构 | `theory_section_template.md` |
| 思维表征 | 图表-矩阵-流程图 | `thinking_representation_template.md` |
| 关联网络 | 引用-链接关系 | `network_section_template.md` |

### 快速使用

```markdown
---
topic: "文档主题"
dependencies: []
status: "draft|review|complete"
author: "作者"
date: "2026-04-12"
version: "1.0.0"
tags: ["标签1", "标签2"]
category: "theory|practice|reference|guide"
priority: "high|medium|low"
---

# 文档标题

> **文档定位**: 一句话描述本文档的核心内容和目的

## 1. 概述 {#概述}
...

## 2. 理论体系 {#理论体系}
...

## 3. 实践应用 {#实践应用}
...

## 4. 关联网络 {#关联网络}
...
```

---

## 质量检查工具

### document_linter.py

自动化文档质量检查，支持以下检查项：

- ✅ **占位符检查**: 检测 `- |- |- |-` 等占位符模式
- ✅ **章节完整性**: 检查是否包含概述、理论体系、实践应用、关联网络
- ✅ **元数据头**: 验证 YAML frontmatter 格式
- ✅ **内部链接**: 检查链接有效性
- ✅ **LaTeX公式**: 检查公式格式和括号匹配
- ✅ **格式规范**: 检查空格、缩进、标题格式

### 使用方法

```bash
# 检查当前目录
python tools/document_linter.py

# 检查指定目录
python tools/document_linter.py ./Concept

# 生成报告
python tools/document_linter.py . --report report.txt --json report.json

# 严格模式
python tools/document_linter.py . --strict

# 排除目录
python tools/document_linter.py . --exclude temp,old,draft
```

---

## 批量规范化工具

### batch_normalize_documents.py

自动为文档添加元数据、规范化章节编号、修复格式问题。

### 使用方法

```bash
# 预览变更（不实际修改）
python tools/batch_normalize_documents.py ./Concept --dry-run

# 实际执行规范化
python tools/batch_normalize_documents.py ./Concept

# 限制处理数量
python tools/batch_normalize_documents.py ./Concept --limit 50

# 生成报告
python tools/batch_normalize_documents.py ./Concept --report report.txt
```

### 规范化内容

1. **添加元数据头**: 自动推断主题、状态、类别等
2. **章节编号**: 统一为 `## 1. 标题 {#锚点}` 格式
3. **格式修复**: 修复空格、列表、代码块格式
4. **添加底部**: 添加标准关联网络部分

---

## 风格指南

详见 `.guides/document_style_guide.md`，主要规范：

### 命名规范

| 类型 | 规范 | 示例 |
|------|------|------|
| 文件名 | 小写+连字符 | `recursion-theory.md` |
| 章节编号 | `## N.` | `## 2. 理论体系` |
| 锚点 | 小写+连字符 | `{#theory-system}` |

### 格式规范

- Markdown 标准语法
- LaTeX 公式格式
- Mermaid 图表规范

### 内容规范

- 形式化定义格式
- 定理-证明格式
- 引用和链接规范

---

## 批量规范化进展

### 处理统计

| 模块 | 总文件数 | 已处理 | 添加元数据 | 规范化编号 |
|------|----------|--------|------------|------------|
| Concept | 454 | 159 | 145 | 1512 |
| FormalRE | 172 | 148 | 100 | 1489 |
| Composed | 366 | 76 | 76 | 538 |
| **合计** | **992** | **383** | **321** | **3539** |

### 检查结果

```
总文件数: 3298
问题文件数: 3251
总问题数: 22968
  - 错误: 946 (占位符、断链、公式错误)
  - 警告: 19940 (元数据、结构、格式)
  - 信息: 2082
```

### 问题分布

| 类别 | 数量 | 说明 |
|------|------|------|
| placeholder | 15769 | 主要是表格分隔符 `-|-` 模式 |
| metadata | 3059 | 缺少元数据头 |
| format | 2080 | 格式问题 |
| structure | 1114 | 章节结构不完整 |
| link | 916 | 断链问题 |
| latex | 30 | LaTeX公式问题 |

---

## 使用建议

### 新文档创建流程

1. 复制 `.templates/document_header_template.md`
2. 填充元数据
3. 按照模板结构编写内容
4. 运行检查: `python tools/document_linter.py 文件.md`
5. 修复问题后提交

### 现有文档改进流程

1. 运行批量规范化: `python tools/batch_normalize_documents.py 路径`
2. 人工审核重要文档
3. 运行质量检查: `python tools/document_linter.py 路径`
4. 根据报告逐步修复问题
5. 定期重新检查

---

## 文件清单

```
docs/Refactor/
├── README.md                          # 本文件
├── .templates/
│   ├── document_header_template.md    # 文档头部模板
│   ├── theory_section_template.md     # 理论体系模板
│   ├── thinking_representation_template.md  # 思维表征模板
│   └── network_section_template.md    # 关联网络模板
└── .guides/
    └── document_style_guide.md        # 详细风格指南

tools/
├── document_linter.py                 # 质量检查脚本
└── batch_normalize_documents.py       # 批量规范化脚本
```

---

## 持续改进

### 计划任务

- [ ] 修复占位符误判问题（表格分隔符）
- [ ] 优化元数据自动推断算法
- [ ] 添加更多LaTeX公式检查规则
- [ ] 实现链接自动修复功能
- [ ] 创建文档质量评分系统

### 反馈渠道

如有问题或建议，请在项目讨论区提出。

---

**文档结束**

_最后更新: 2026-04-12_
