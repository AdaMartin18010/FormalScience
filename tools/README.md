# FormalScience 工具集

本目录包含 FormalScience 项目的自动化工具集。

---

## 📋 可用工具

### 1. 文档质量检查器 (document_quality_checker.py)

文档质量自动化检查工具，用于确保所有文档符合项目标准。

#### 功能

- ✅ 检测占位符（`- |- |- |-`、`待补充`、`TODO` 等）
- ✅ 检查元数据头完整性
- ✅ 验证章节结构
- ✅ 检查交叉引用链接有效性
- ✅ 验证思维表征图表
- ✅ 生成详细质量报告

#### 快速开始

```bash
# 检查单个文件
python tools/document_quality_checker.py Concept/README.md

# 检查整个目录
python tools/document_quality_checker.py -r Concept/

# 生成 Markdown 报告
python tools/document_quality_checker.py -f markdown -o report.md -r Concept/

# 标准化元数据头
python tools/document_quality_checker.py --normalize -r Concept/
```

#### 详细文档

- [使用指南](../docs/Refactor/.templates/QUALITY_CHECKER_USAGE.md)

---

## 🛠️ 开发计划

计划中的工具：

| 工具名称 | 功能描述 | 状态 |
|---------|----------|------|
| link_validator.py | 跨文档链接批量验证 | 计划中 |
| toc_generator.py | 自动生成和更新目录 | 计划中 |
| metadata_sync.py | 批量同步元数据字段 | 计划中 |
| chart_validator.py | Mermaid 图表语法检查 | 计划中 |

---

## 📖 使用说明

所有工具使用 Python 3 编写，无需额外依赖：

```bash
# 查看工具帮助
python tools/<tool_name>.py --help

# 大多数工具支持以下通用选项
-r, --recursive     # 递归处理子目录
-v, --verbose       # 详细输出
-o, --output        # 指定输出文件
```

---

## 🔧 贡献指南

添加新工具时，请遵循以下规范：

1. 使用 Python 3.7+ 编写
2. 仅使用标准库，避免外部依赖
3. 提供 `--help` 帮助信息
4. 添加详细的文档说明
5. 支持标准输入输出约定

---

**最后更新**: 2026-04-12
