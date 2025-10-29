# VSCode/Cursor 配置说明

## 自动 Markdown 格式化配置

本目录包含 VSCode/Cursor 的配置文件，用于在保存 Markdown 文件时自动格式化。

## 📦 需要安装的扩展

打开 Cursor/VSCode 后，会自动提示安装推荐的扩展，或者手动安装：

1. **Markdownlint** (必需)
   - ID: `DavidAnson.vscode-markdownlint`
   - 功能：Markdown 格式检查和自动修复

2. **Markdown All in One** (推荐)
   - ID: `yzhang.markdown-all-in-one`
   - 功能：TOC 生成、快捷键、列表自动续写等

## ⚙️ 配置文件说明

### `settings.json`

主要配置：

- ✅ 保存时自动格式化 Markdown
- ✅ 自动删除行尾空格
- ✅ 文件末尾自动添加新行
- ✅ 允许使用 HTML 标签（`<details>`, `<summary>` 等）
- ✅ 允许同级标题重复

### `.markdownlint.json`

Markdownlint 规则配置（项目根目录）：

- MD033: false - 允许内联 HTML
- MD024: siblings_only - 允许非同级标题重复
- MD013: false - 不限制行长度
- MD012: false - 允许多个空行

## 🚀 使用方法

### 自动格式化

1. 打开任意 Markdown 文件
2. 修改内容
3. 按 `Ctrl+S` (Windows) 或 `Cmd+S` (Mac) 保存
4. 文件会自动格式化

### 手动格式化

- **格式化整个文档**: `Shift+Alt+F` (Windows) / `Shift+Option+F` (Mac)
- **格式化选中内容**: 选中文本后右键 → "Format Selection"

### 查看和修复 Linter 错误

1. 打开 Markdown 文件
2. 查看编辑器中的波浪线提示
3. 点击灯泡图标 💡 查看快速修复选项
4. 或在命令面板中运行: `Markdownlint: Fix all supported markdownlint violations in document`

## 🎯 快捷键

| 功能 | Windows/Linux | Mac |
|------|--------------|-----|
| 保存并格式化 | `Ctrl+S` | `Cmd+S` |
| 格式化文档 | `Shift+Alt+F` | `Shift+Option+F` |
| 修复所有错误 | `Ctrl+Shift+P` → "Fix all" | `Cmd+Shift+P` → "Fix all" |

## 📝 规则说明

### 允许的格式

```markdown
<!-- ✅ 允许使用 HTML -->
<details>
<summary>点击展开</summary>
内容
</details>

<!-- ✅ 允许重复标题（不同章节） -->
## 概述
### 示例
## 实现
### 示例  <!-- 允许，因为不是同级 -->

<!-- ✅ 允许长行（代码块、链接等） -->
这是一个很长很长很长的行...
```

### 自动修复的问题

- ❌ 行尾空格 → ✅ 自动删除
- ❌ 缺少文件末尾新行 → ✅ 自动添加
- ❌ 不一致的列表缩进 → ✅ 自动修正
- ❌ 代码块缺少语言标识 → ✅ 自动添加空标识

## 🔧 自定义配置

如果需要修改规则，编辑以下文件：

- **VSCode 设置**: `.vscode/settings.json`
- **Markdownlint 规则**: `.markdownlint.json`（项目根目录）

## 🐛 故障排除

### 格式化不生效

1. 确认已安装 Markdownlint 扩展
2. 重新加载窗口: `Ctrl+Shift+P` → "Reload Window"
3. 检查输出面板: `Ctrl+Shift+U` → 选择 "Markdownlint"

### 某些规则想要禁用

在 `.markdownlint.json` 中设置为 `false`:

```json
{
  "MD规则编号": false
}
```

### 某个文件想要跳过检查

在文件开头添加注释：

```markdown
<!-- markdownlint-disable -->
文件内容
<!-- markdownlint-enable -->
```

或禁用特定规则：

```markdown
<!-- markdownlint-disable MD033 -->
<details>内容</details>
<!-- markdownlint-enable MD033 -->
```

## 📚 参考文档

- [Markdownlint 规则列表](https://github.com/DavidAnson/markdownlint/blob/main/doc/Rules.md)
- [VSCode Markdown 支持](https://code.visualstudio.com/docs/languages/markdown)
