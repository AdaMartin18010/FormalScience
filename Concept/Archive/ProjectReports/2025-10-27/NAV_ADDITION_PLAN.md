# 导航链接添加计划

> **日期**: 2025-10-27  
> **任务**: 为189个文件添加导航链接  
> **当前进度**: 36/225 (16%) → 目标 225/225 (100%)

---

## 📋 任务概述

### 已完成 ✅
- **Software_Perspective**: 36/36 (100%) - 完整的目录+导航

### 待完成 ⏳
- **AI_model_Perspective**: 0/60 (0%) - 有目录，缺导航
- **FormalLanguage_Perspective**: 0/63 (0%) - 有目录，缺导航  
- **Information_Theory_Perspective**: 0/66 (0%) - 有目录，缺导航

**总计**: 189个文件需添加导航链接

---

## 🎯 导航链接标准格式

每个文件末尾需要添加三部分导航：

### 1. 上一篇/下一篇

```markdown
---

## 导航 | Navigation

**上一篇**: [← 00.0 章节导航](../00_Chapter/README.md)  
**下一篇**: [01.2 下一主题 →](./01.2_Next_Topic.md)  
**返回目录**: [↑ AI模型视角总览](../README.md)
```

### 2. 相关主题

```markdown
---

## 相关主题 | Related Topics

### 同层级主题
- [01.2 主题2](./01.2_Topic2.md)
- [01.3 主题3](./01.3_Topic3.md)

### 关联章节
- [02.1 相关章节](../02_Chapter/02.1_Topic.md)
- [03.1 相关理论](../03_Chapter/03.1_Theory.md)

### 其他视角
- [Software_Perspective: 相关主题](../../Software_Perspective/topic.md)
- [FormalLanguage_Perspective: 相关理论](../../FormalLanguage_Perspective/theory.md)
```

### 3. 参考文献（如已有）

保留原有的参考文献部分

---

## 🚀 执行策略

### 方案A: Python自动化（推荐）

**工具**: 使用`tools/add_navigation.py`  
**优点**: 
- 快速（20分钟完成全部）
- 一致性好
- 自动生成链接

**步骤**:
1. 配置Python环境
2. 运行脚本: `python tools/add_navigation.py --perspective all --apply`
3. 验证结果

**预计时间**: 20分钟

### 方案B: 批量手动处理

**工具**: 文本编辑器批量替换  
**优点**:
- 无需Python环境
- 可控性强

**步骤**:
1. 为每个Perspective准备导航模板
2. 使用VS Code多光标功能
3. 批量插入导航链接

**预计时间**: 8-12小时

### 方案C: 逐个手动添加

**最不推荐**  
**预计时间**: 16小时+

---

## 📝 导航模板

### AI_model_Perspective 模板

```markdown
---

## 导航 | Navigation

**上一篇**: [← {PREV_TITLE}]({PREV_PATH})  
**下一篇**: [{NEXT_TITLE} →]({NEXT_PATH})  
**返回目录**: [↑ AI模型视角总览](../README.md)

---

## 相关主题 | Related Topics

### 本章节
{CHAPTER_TOPICS}

### 相关章节
{RELATED_CHAPTERS}

### 跨视角链接
- [Software_Perspective](../../Software_Perspective/README.md)
- [FormalLanguage_Perspective](../../FormalLanguage_Perspective/README.md)
- [Information_Theory_Perspective](../../Information_Theory_Perspective/README.md)
```

---

## 📊 执行计划

### 阶段1: AI_model_Perspective (60个文件)

**目录结构**:
- 01_Foundational_Theory (5个)
- 02_Neural_Network_Theory (5个)
- 03_Language_Models (6个)
- 04_Semantic_Models (6个)
- 05_Learning_Theory (6个)
- 06_Computational_Paradigms (5个)
- 07_AI_Philosophy (6个)
- 08_Comparison_Analysis (5个)
- 09_AI_Factory_Model (5个)
- 10_Future_Directions (5个)
- 索引文件 (6个)

**执行顺序**: 按目录顺序，每批处理5-10个

### 阶段2: FormalLanguage_Perspective (63个文件)

类似处理

### 阶段3: Information_Theory_Perspective (66个文件)

类似处理

---

## ✅ 验证清单

每个文件检查项:
- [ ] 有导航部分（上一篇/下一篇/返回目录）
- [ ] 有相关主题部分
- [ ] 所有链接正确无误
- [ ] Markdown格式正确
- [ ] 跨视角链接完整

---

## 🎯 预期成果

完成后，每个文件将：
1. ✅ 有完整的目录（Table of Contents）
2. ✅ 有导航链接（前后文+返回）
3. ✅ 有相关主题（横向+纵向+跨视角）
4. ✅ 结构完全统一
5. ✅ 用户体验极佳

**总进度**: 36/225 → 225/225 (100%)

---

**创建时间**: 2025-10-27  
**执行状态**: 待开始  
**优先级**: 高

