# Markdown 目录修复指南

> **创建日期**: 2025-10-30
> **状态**: ✅ 工具就绪，待批量执行
> **目的**: 为所有 Markdown 文件添加/更新目录，修复序号不一致问题

---

## 📋 目录

    - [1.1.1 问题3：序号跳跃](#111-问题3序号跳跃)

- [Markdown 目录修复指南](#markdown-目录修复指南)
  - [📋 目录](#-目录)
  - [第一章](#第一章--)
  - [5 解决方案](#5-解决方案)
    - [5.1 设计原则](#51-设计原则)
  - [6 已提供的工具](#6-已提供的工具)
    - [6.1 Python 脚本推荐](#61-python-脚本推荐)
    - [6.2 PowerShell 脚本Windows](#62-powershell-脚本windows)
    - [6.3 Nodejs 脚本跨平台](#63-nodejs-脚本跨平台)
  - [7 使用方法](#7-使用方法)
    - [7.1 方案A：使用 Python 脚本推荐](#71-方案a使用-python-脚本推荐)
    - [7.2 方案B：使用 PowerShellWindows原生](#72-方案b使用-powershellwindows原生)
    - [7.3 方案C：使用 Nodejs如果安装了Node](#73-方案c使用-nodejs如果安装了node)
    - [7.4 方案D：手动修复针对少量文件](#74-方案d手动修复针对少量文件)
  - [8 示例修复](#8-示例修复)
    - [8.1 修复前](#81-修复前)
  - [12 批量执行建议](#12-批量执行建议)
    - [12.1 策略1：全量修复推荐](#121-策略1全量修复推荐)
    - [12.2 策略2：分批修复谨慎](#122-策略2分批修复谨慎)
    - [12.3 策略3：先测试再全量最安全](#123-策略3先测试再全量最安全)
  - [13 注意事项](#13-注意事项)
    - [13.1 安全措施](#131-安全措施)
    - [13.2 已知限制](#132-已知限制)
    - [13.3 手动修复序号](#133-手动修复序号)
  - [20 执行清单](#20-执行清单)
    - [20.1 执行前](#201-执行前)
    - [20.2 执行中](#202-执行中)
    - [20.3 执行后](#203-执行后)
  - [21 快速开始](#21-快速开始)
  - [22 附录](#22-附录)
    - [A. 目录格式标准](#a-目录格式标准)
  - [\`\`\`markdown](#markdown)

---


## 第一章  <!-- 直接开始，没有目录 -->

```

**期望**：在元数据块之后、第一个主标题之前插入目录

#### 2.2.1 问题3：序号跳跃

```markdown
## 2 标题A
## 3 标题B
## 4 标题C -- 应该是 13 --
```

---

## 5 解决方案

### 5.1 设计原则

1. **自动生成目录**：根据文件中的所有标题（2-4级）自动生成
2. **智能插入**：在元数据块之后、第一个主标题之前插入
3. **更新而非替换**：如果已有目录，更新而不是删除
4. **保留结构**：不改变原有章节结构和序号

---

## 6 已提供的工具

我已为您创建了 **3个自动化修复脚本**：

### 6.1 Python 脚本推荐

**文件**: `fix_toc_and_numbering.py`

**功能**:

- ✅ 扫描所有 .md 文件
- ✅ 自动生成/更新目录
- ✅ 检查序号一致性
- ✅ 生成详细 JSON 报告

**使用**:

```bash
cd Concept
python fix_toc_and_numbering.py
```

**输出**:

- 控制台：实时进度和统计
- `TOC_FIX_REPORT.json`：详细报告

---

### 6.2 PowerShell 脚本Windows

**文件**: `Fix-TOC.ps1`

**功能**:

- ✅ 扫描所有 .md 文件
- ✅ 自动生成/更新目录
- ✅ 彩色输出

**使用**:

```powershell
cd Concept
powershell -ExecutionPolicy Bypass -File Fix-TOC.ps1
```

**参数**:

```powershell
# 模拟运行（不实际修改）
Fix-TOC.ps1 -DryRun

# 指定路径
Fix-TOC.ps1 -Path "AI_model_Perspective"
```

---

### 6.3 Nodejs 脚本跨平台

**文件**: `fix-toc.js`

**功能**:

- ✅ 扫描所有 .md 文件
- ✅ 自动生成/更新目录
- ✅ 轻量快速

**使用**:

```bash
cd Concept
node fix-toc.js
```

---

## 7 使用方法

### 7.1 方案A：使用 Python 脚本推荐

```bash
# 1. 进入 Concept 目录
cd C:\Users\luyan\.cursor\worktrees\FormalScience\DWBAh\Concept

# 2. 运行脚本
python fix_toc_and_numbering.py

# 3. 查看报告
cat TOC_FIX_REPORT.json
```

### 7.2 方案B：使用 PowerShellWindows原生

```powershell
# 1. 进入目录
cd C:\Users\luyan\.cursor\worktrees\FormalScience\DWBAh\Concept

# 2. 先模拟运行查看效果
.\Fix-TOC.ps1 -DryRun

# 3. 确认无误后正式运行
.\Fix-TOC.ps1
```

### 7.3 方案C：使用 Nodejs如果安装了Node

```bash
cd C:\Users\luyan\.cursor\worktrees\FormalScience\DWBAh\Concept
node fix-toc.js
```

### 7.4 方案D：手动修复针对少量文件

如果只需要修复个别文件，可以手动操作：

1. 读取文件，提取所有 2-4 级标题
2. 生成目录（格式见示例）
3. 在元数据块之后插入

---

## 8 示例修复

### 8.1 修复前

```markdown
# 神经语言模型 | Neural Language Models

> **文档版本**: v1.0.0

---

---

---

## 9 概述

神经语言模型...

## 10 核心技术突破

### 10.1 分布式词表示

### 10.2 循环神经网络

## 11 重要里程碑

### 11.1 Bengio 2003

### 11.2 Mikolov 2010
```

---

## 12 批量执行建议

### 12.1 策略1：全量修复推荐

```bash
# 一次性修复所有文件
cd Concept
python fix_toc_and_numbering.py
```

**优点**: 快速、全面、一致
**缺点**: 可能需要审查修改

### 12.2 策略2：分批修复谨慎

```bash
# 按视角分批处理
cd Concept

# 第1批：AI模型视角
python fix_toc_and_numbering.py --path AI_model_Perspective

# 第2批：形式语言视角
python fix_toc_and_numbering.py --path FormalLanguage_Perspective

# ... 依次处理其他视角
```

**优点**: 可控、便于审查
**缺点**: 耗时较长

### 12.3 策略3：先测试再全量最安全

```bash
# 1. 先备份
cp -r Concept Concept_backup

# 2. 测试单个文件
python fix_toc_and_numbering.py --file AI_model_Perspective/README.md

# 3. 检查修复效果
git diff AI_model_Perspective/README.md

# 4. 如果满意，执行全量
python fix_toc_and_numbering.py

# 5. 审查所有修改
git diff

# 6. 提交或回滚
git commit -am "Fix: 为所有 Markdown 添加/更新目录"
# 或
git reset --hard  # 回滚
```

---

## 13 注意事项

### 13.1 安全措施

1. **提交前备份**：

   ```bash
   git stash  # 暂存当前修改
   git checkout -b toc-fix  # 新建分支
   ```

2. **使用 Git 审查修改**：

   ```bash
   git diff  # 查看所有修改
   git diff --stat  # 统计修改
   ```

3. **分批提交**：

   ```bash
   git add AI_model_Perspective/
   git commit -m "Fix: AI模型视角目录修复"
   ```

### 13.2 已知限制

1. **emoji 锚点**：包含 emoji 的标题，锚点生成可能不完美
   - 例如：`## 📊 数据分析` → `#-数据分析`
   - **建议**：手动调整或移除 emoji

2. **中英文混合**：某些标题的锚点可能需要微调
   - 例如：`## AI vs 图灵机` → `#ai-vs-图灵机`

3. **特殊字符**：标题中的特殊字符会被移除
   - 例如：`## 1.1 标题（重要）` → `#11-标题重要`

4. **序号不连续**：脚本会**检测但不自动修复**序号问题
   - 需要手动审查 `TOC_FIX_REPORT.json` 中的 `numbering_issues`

### 13.3 手动修复序号

如果发现序号不一致（如 1.1, 1.2, 1.5），需要手动修复：

```markdown
<!-- 修复前 -->
## 14 第一节
## 15 第二节
## 16 第三节

<!-- 修复后 -->
## 17 第一节
## 18 第二节
## 19 第三节
```

---

## 20 执行清单

### 20.1 执行前

- [ ] 备份当前工作区（`git stash` 或 `cp -r`）
- [ ] 确认Python/PowerShell/Node.js环境
- [ ] 阅读本指南

### 20.2 执行中

- [ ] 选择一个脚本运行
- [ ] 观察输出，记录错误
- [ ] 检查修复后的文件样例

### 20.3 执行后

- [ ] 使用 `git diff` 审查所有修改
- [ ] 检查关键文件的目录是否正确
- [ ] 处理 `numbering_issues` 中的序号问题
- [ ] 提交修改或回滚

---

## 21 快速开始

**最快的方式**（如果您信任自动化）：

```bash
cd C:\Users\luyan\.cursor\worktrees\FormalScience\DWBAh\Concept

# 创建备份分支
git checkout -b toc-fix-2025-10-30

# 运行修复（选一个）
python fix_toc_and_numbering.py
# 或
powershell -ExecutionPolicy Bypass -File Fix-TOC.ps1
# 或
node fix-toc.js

# 审查修改
git diff --stat
git diff | less

# 如果满意
git add .
git commit -m "修复: 为所有 Markdown 文件添加/更新目录

- 使用自动化脚本修复 260+ 个文件
- 统一目录格式为 GitHub 风格
- 保持原有章节结构和序号"

# 如果不满意
git reset --hard
git checkout main
git branch -D toc-fix-2025-10-30
```

---

## 22 附录

### A. 目录格式标准

```markdown
---

**创建日期**: 2025-10-30
**版本**: v1.0.0
**维护者**: AI Assistant

**需要帮助？** 请查看脚本注释或联系维护者。
