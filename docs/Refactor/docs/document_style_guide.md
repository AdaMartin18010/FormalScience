# 文档风格指南

> 本文档定义了项目文档的写作规范、格式要求和命名约定。

---

## 目录

- [写作规范](#写作规范)
- [格式要求](#格式要求)
- [命名约定](#命名约定)
- [示例说明](#示例说明)

---

## 写作规范

### 1. 语言风格

#### 1.1 简洁明确

- ✅ **推荐**: 点击"保存"按钮提交表单
- ❌ **避免**: 请您在填写完所有必要信息后，找到并点击页面上的"保存"按钮以提交您的表单数据

#### 1.2 使用主动语态

- ✅ **推荐**: 系统验证用户输入
- ❌ **避免**: 用户输入被系统验证

#### 1.3 第二人称

- ✅ **推荐**: 你可以使用以下命令...
- ❌ **避免**: 用户可以使用以下命令...

### 2. 技术写作原则

#### 2.1 一个概念一段落

每个段落应聚焦于一个主要概念或主题。

#### 2.2 使用列表提高可读性

复杂步骤应使用有序列表，相关项目使用无序列表。

#### 2.3 提供上下文

在介绍新概念时，先解释"为什么"再解释"怎么做"。

### 3. 中英文混排规范

| 场景 | 规范 | 示例 |
|------|------|------|
| 中文与英文 | 加空格 | 这是一个 Python 项目 |
| 中文与数字 | 加空格 | 版本 2.0 已发布 |
| 英文标点 | 后加空格 | Hello, world |
| 专有名词 | 保持原样 | GitHub, Python, Docker |

### 4. 标点符号使用

- 中文文档使用中文标点（，。！？）
- 英文文档使用英文标点（, . ! ?）
- 代码中使用英文标点
- 引号嵌套：外双内单 "'example'"

---

## 格式要求

### 1. Markdown 规范

#### 1.1 标题层级

```markdown
# 一级标题 - 文档主标题（仅一个）

## 二级标题 - 主要章节

### 三级标题 - 子章节

#### 四级标题 - 细分内容（尽量少用）
```

#### 1.2 代码块

- 所有代码块必须指定语言
- 使用围栏代码块（```）而非缩进

````markdown
```python
def example():
    pass
```
````

#### 1.3 表格

- 表头使用标题格式
- 对齐方式明确

```markdown
| 左对齐 | 居中对齐 | 右对齐 |
|:-------|:--------:|-------:|
| 内容   |  内容    |   内容 |
```

### 2. 文档结构

#### 2.1 标准文档结构

```
1. 标题和描述
2. 目录（可选，文档较长时使用）
3. 概述/简介
4. 主体内容（分层组织）
5. 示例/用法
6. 参考链接
7. 附录（可选）
```

#### 2.2 YAML Frontmatter（可选）

```yaml
---
title: "文档标题"
date: YYYY-MM-DD
author: "作者名"
version: "1.0.0"
tags: ["标签1", "标签2"]
---
```

### 3. 图片和媒体

#### 3.1 图片引用

```markdown
![图片描述](./images/example.png)
```

#### 3.2 图片存储

- 图片存放于文档同级 `images/` 目录
- 使用相对路径引用
- 图片命名：`文档名_序号_描述.png`

---

## 命名约定

### 1. 文件命名

#### 1.1 文档文件

| 类型 | 命名规范 | 示例 |
|------|----------|------|
| 指南类 | `guide_主题.md` | `guide_installation.md` |
| 教程类 | `tutorial_主题.md` | `tutorial_quickstart.md` |
| 参考类 | `ref_主题.md` | `ref_api.md` |
| 概念类 | `concept_主题.md` | `concept_architecture.md` |

#### 1.2 README 文件

- 项目根目录：`README.md`
- 子项目目录：`README.md`
- 中文版本：`README_zh.md`

#### 1.3 命名风格

- 使用小写字母
- 单词间用下划线 `_` 连接
- 避免空格和特殊字符
- 保持描述性：`install_guide.md` 而非 `guide.md`

### 2. 目录结构

```
docs/
├── README.md                 # 文档首页
├── guide/                    # 用户指南
│   ├── guide_installation.md
│   └── guide_configuration.md
├── tutorial/                 # 教程
│   ├── tutorial_quickstart.md
│   └── tutorial_advanced.md
├── reference/                # 参考文档
│   ├── ref_api.md
│   └── ref_cli.md
├── concept/                  # 概念说明
│   └── concept_architecture.md
├── examples/                 # 示例代码
│   └── example_basic_usage.md
└── images/                   # 图片资源
    └── architecture_diagram.png
```

### 3. 内部链接

#### 3.1 链接格式

```markdown
<!-- 同一目录 -->
[链接文本](./file.md)

<!-- 上级目录 -->
[链接文本](../guide/file.md)

<!-- 锚点链接 -->
[链接文本](./file.md#章节标题)
```

#### 3.2 链接文本规范

- 使用描述性文本
- 避免使用"点击这里"

```markdown
✅ [查看安装指南](./guide_installation.md)
❌ [点击这里](./guide_installation.md)
```

---

## 示例说明

### 1. 完整文档示例

#### 1.1 文件头示例

```markdown
---
title: "快速开始指南"
date: 2024-01-15
author: "张三"
version: "1.0.0"
tags: ["入门", "教程"]
---

# 快速开始指南

> 本文档帮助新用户在 5 分钟内完成项目的安装和基础配置。
```

#### 1.2 章节示例

```markdown
## 安装

### 环境要求

在开始之前，请确保你的系统满足以下要求：

- Python 3.10 或更高版本
- pip 包管理器
- 至少 2GB 可用内存

### 安装步骤

1. 创建虚拟环境：
   ```bash
   python -m venv venv
   ```

2. 激活虚拟环境：
   ```bash
   # Linux/macOS
   source venv/bin/activate
   
   # Windows
   venv\Scripts\activate
   ```

3. 安装依赖：
   ```bash
   pip install -r requirements.txt
   ```
```

### 2. 代码示例规范

#### 2.1 代码块注释

```python
# ✅ 好的注释：解释"为什么"
# 使用二分查找因为列表已排序
result = binary_search(sorted_list, target)

# ❌ 差的注释：重复代码内容
# 对列表进行二分查找
result = binary_search(sorted_list, target)
```

#### 2.2 代码输出示例

````markdown
运行上述代码将输出：

```
Hello, World!
计算结果: 42
```
````

### 3. 表格示例

#### 3.1 配置参数表

```markdown
| 参数名 | 类型 | 必填 | 默认值 | 说明 |
|--------|------|------|--------|------|
| host | string | 是 | - | 服务器地址 |
| port | integer | 否 | 8080 | 端口号 |
| timeout | integer | 否 | 30 | 超时时间（秒） |
| retries | integer | 否 | 3 | 重试次数 |
```

#### 3.2 版本兼容表

```markdown
| 项目版本 | Python 版本 | 支持状态 |
|----------|-------------|----------|
| 1.x | 3.8+ | 维护中 |
| 2.x | 3.10+ | 活跃开发 |
| 3.x | 3.12+ | 计划中 |
```

### 4. 提示框示例

```markdown
> 💡 **提示**
> 这是一个有用的提示信息。

> ⚠️ **警告**
> 注意这可能导致数据丢失。

> 🚫 **重要**
> 这是必须遵守的要求。

> 📌 **注意**
> 这是需要额外关注的信息。
```

### 5. 完整示例文档

参考模板文件：

- [标准文档模板](../.templates/document_template.md)
- [代码示例模板](../.templates/code_example_template.md)
- [README 模板](../.templates/README_template.md)

---

## 检查清单

发布文档前，请确认：

- [ ] 文档标题清晰明确
- [ ] 所有链接可正常访问
- [ ] 代码示例经过测试
- [ ] 图片正确显示
- [ ] 无拼写和语法错误
- [ ] 格式符合本指南要求
- [ ] 更新日志已记录（如适用）

---

## 参考资源

- [Microsoft Writing Style Guide](https://docs.microsoft.com/en-us/style-guide/)
- [Google Developer Documentation Style Guide](https://developers.google.com/style)
- [中文技术文档写作规范](https://github.com/ruanyf/document-style-guide)
