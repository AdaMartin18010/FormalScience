# Cursor/VSCode Markdown 自动格式化配置指南

## ✅ 配置已完成

已为项目配置好以下文件：

```text
FormalScience/
├── .vscode/
│   ├── settings.json         # VSCode/Cursor 设置
│   ├── extensions.json       # 推荐扩展列表
│   └── README.md            # 详细配置说明
├── .markdownlint.json       # Markdownlint 规则配置
└── .gitignore               # Git 忽略文件
```

## 🚀 快速开始

### 步骤 1: 安装必需扩展

1. 打开 Cursor/VSCode
2. 会自动弹出提示：**"是否安装推荐的扩展？"**
3. 点击 **"Install All"** 或手动安装：
   - 打开扩展面板 (`Ctrl+Shift+X` / `Cmd+Shift+X`)
   - 搜索并安装 `Markdownlint`（必需）

### 步骤 2: 重新加载窗口

安装扩展后：

- 按 `F1` 或 `Ctrl+Shift+P` (Mac: `Cmd+Shift+P`)
- 输入 `Reload Window`
- 按回车

### 步骤 3: 测试自动格式化

1. 打开任意 `.md` 文件（如这个文件）
2. 故意添加一些格式问题：

   ```markdown
   #错误的标题格式

   - 列表项1
   - 列表项2



   多余的空行
   ```

3. 按 `Ctrl+S` (Mac: `Cmd+S`) 保存
4. 观察文件是否自动修复为：

   ```markdown
   # 错误的标题格式

   - 列表项1
   - 列表项2

   多余的空行
   ```

## ⚙️ 配置详情

### 自动修复的问题

保存时会自动修复：

| 问题 | 修复方式 |
|------|---------|
| ❌ 行尾空格 | ✅ 自动删除 |
| ❌ 文件末尾缺少新行 | ✅ 自动添加 |
| ❌ 不一致的列表缩进 | ✅ 统一为 2 空格 |
| ❌ 标题后缺少空行 | ✅ 自动添加 |
| ❌ 代码块未指定语言 | ✅ 添加提示 |

### 允许的格式（不会报错）

以下格式是项目中常用的，已配置为允许：

```markdown
<!-- ✅ 允许 HTML 标签 -->
<details>
<summary><b>点击展开</b></summary>
内容
</details>

<!-- ✅ 允许同级标题重复（用于文档结构） -->
## 章节 1
### 示例
## 章节 2
### 示例  <!-- 不会报错 -->

<!-- ✅ 允许长行 -->
这是一个很长的行，包含链接 [链接文本](https://example.com/very/long/url/path)

<!-- ✅ 允许多个连续空行 -->


<!-- 用于分隔章节 -->
```

## 🎯 常用快捷键

| 功能 | Windows/Linux | Mac |
|------|--------------|-----|
| 保存并自动格式化 | `Ctrl+S` | `Cmd+S` |
| 手动格式化当前文档 | `Shift+Alt+F` | `Shift+Option+F` |
| 查看所有问题 | `Ctrl+Shift+M` | `Cmd+Shift+M` |
| 修复所有可修复的问题 | `F1` → "Fix all" | `Cmd+Shift+P` → "Fix all" |

## 💡 使用技巧

### 1. 查看 Linter 错误

编辑器中会显示：

- 🔴 红色波浪线：错误
- 🟡 黄色波浪线：警告

鼠标悬停查看详细信息，点击灯泡 💡 查看快速修复。

### 2. 禁用某个文件的检查

在文件开头添加：

```markdown
<!-- markdownlint-disable -->
整个文件内容
```

### 3. 禁用某行的检查

```markdown
<!-- markdownlint-disable-next-line MD033 -->
<div>允许使用 HTML</div>
```

### 4. 批量格式化多个文件

使用 VSCode 的命令面板：

1. `Ctrl+Shift+P` / `Cmd+Shift+P`
2. 输入 `Format Document`
3. 或者使用 `tools/batch_fix_markdown.py` 脚本

## 🔧 自定义配置

### 修改 Markdownlint 规则

编辑根目录的 `.markdownlint.json` 文件：

```json
{
  "MD规则编号": true,  // 启用规则
  "MD规则编号": false, // 禁用规则
  "MD规则编号": {      // 配置规则选项
    "选项": "值"
  }
}
```

### 修改 VSCode 设置

编辑 `.vscode/settings.json` 文件。

## 📚 规则参考

### 常用 Markdownlint 规则

| 规则 | 名称 | 说明 | 本项目配置 |
|------|------|------|-----------|
| MD001 | heading-increment | 标题层级递增 | ✅ 启用 |
| MD003 | heading-style | 标题样式（ATX/Setext） | ATX (#) |
| MD004 | ul-style | 无序列表样式 | dash (-) |
| MD007 | ul-indent | 列表缩进 | 2 空格 |
| MD012 | no-multiple-blanks | 禁止多个空行 | ❌ 禁用 |
| MD013 | line-length | 行长度限制 | ❌ 禁用 |
| MD024 | no-duplicate-heading | 禁止重复标题 | 仅同级 |
| MD033 | no-inline-html | 禁止内联 HTML | ❌ 禁用 |
| MD051 | link-fragments | 链接锚点验证 | ✅ 启用 |

完整规则列表：https://github.com/DavidAnson/markdownlint/blob/main/doc/Rules.md

## 🐛 故障排除

### 问题 1: 保存时没有自动格式化

**解决方法**：

1. 确认已安装 Markdownlint 扩展
2. 检查文件是否为 `.md` 扩展名
3. 查看状态栏是否显示 "Markdown"
4. 重新加载窗口: `F1` → "Reload Window"

### 问题 2: 某些规则不生效

**解决方法**：

1. 检查 `.markdownlint.json` 文件格式是否正确
2. 查看输出面板: `Ctrl+Shift+U` → 选择 "Markdownlint"
3. 确认规则名称拼写正确

### 问题 3: 格式化后文件变乱

**解决方法**：

1. 撤销更改: `Ctrl+Z` / `Cmd+Z`
2. 检查 `.markdownlint.json` 配置
3. 查看是否有多个格式化工具冲突

### 问题 4: 中文字符显示问题

**解决方法**：

确认 VSCode 设置：
```json
{
  "files.encoding": "utf8"
}
```

## 📖 更多资源

- 📁 [详细配置说明](.vscode/README.md)
- 🔗 [Markdownlint 官方文档](https://github.com/DavidAnson/markdownlint)
- 🔗 [VSCode Markdown 支持](https://code.visualstudio.com/docs/languages/markdown)
- 📚 [本项目 Markdown 规范](Concept/DOCUMENT_STRUCTURE_STANDARD.md)

## ✨ 下一步

1. ✅ 安装推荐扩展
2. ✅ 测试自动格式化
3. ✅ 阅读 [详细配置说明](.vscode/README.md)
4. ✅ 开始编写文档，享受自动格式化！

---

**配置完成日期**: 2025-10-29
**维护者**: AI Assistant
**问题反馈**: 在项目 Issues 中提出
