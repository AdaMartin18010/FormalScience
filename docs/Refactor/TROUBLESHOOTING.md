# 故障排除指南 (Troubleshooting Guide)

> 本指南帮助您诊断和解决使用FormalScience项目时遇到的常见问题。

---

## 📋 目录

- [故障排除指南 (Troubleshooting Guide)](#故障排除指南-troubleshooting-guide)
  - [📋 目录](#-目录)
  - [快速诊断](#快速诊断)
    - [故障排除流程](#故障排除流程)
    - [收集系统信息](#收集系统信息)
  - [Lean安装问题](#lean安装问题)
    - [问题1: Elan安装失败](#问题1-elan安装失败)
    - [问题2: 工具链下载失败](#问题2-工具链下载失败)
    - [问题3: VS Code无法识别Lean](#问题3-vs-code无法识别lean)
    - [问题4: 权限不足（Unix系统）](#问题4-权限不足unix系统)
  - [代码编译错误](#代码编译错误)
    - [问题5: 导入错误 (Unknown Module)](#问题5-导入错误-unknown-module)
    - [问题6: 类型不匹配 (Type Mismatch)](#问题6-类型不匹配-type-mismatch)
    - [问题7: 无法合成实例 (Failed to Synthesize)](#问题7-无法合成实例-failed-to-synthesize)
    - [问题8: 递归函数终止性错误](#问题8-递归函数终止性错误)
    - [问题9: 证明卡壳 (Stuck in Proof)](#问题9-证明卡壳-stuck-in-proof)
    - [问题10: 内存不足 (Out of Memory)](#问题10-内存不足-out-of-memory)
  - [环境配置问题](#环境配置问题)
    - [问题11: Lakefile语法错误](#问题11-lakefile语法错误)
    - [问题12: Git子模块问题](#问题12-git子模块问题)
    - [问题13: 文件路径过长（Windows）](#问题13-文件路径过长windows)
    - [问题14: VS Code InfoView空白](#问题14-vs-code-infoview空白)
    - [问题15: 编码问题](#问题15-编码问题)
  - [常见错误及解决方案](#常见错误及解决方案)
    - [错误对照表](#错误对照表)
    - [问题16: 构建缓存失效](#问题16-构建缓存失效)
    - [问题17: Mathlib版本不兼容](#问题17-mathlib版本不兼容)
    - [问题18: 循环依赖](#问题18-循环依赖)
    - [问题19: 名称冲突](#问题19-名称冲突)
    - [问题20: 证明性能问题](#问题20-证明性能问题)
  - [获取帮助](#获取帮助)
    - [自助资源](#自助资源)
    - [提问模板](#提问模板)

---

## 快速诊断

### 故障排除流程

```
遇到问题
    ↓
[检查错误信息]
    ↓
能看懂错误？→ 是 → [查找对应解决方案]
    ↓ 否
[收集系统信息]
    ↓
[搜索已知问题]
    ↓
找到解决方案？→ 是 → [应用解决方案]
    ↓ 否
[创建Issue求助]
```

### 收集系统信息

运行以下命令收集诊断信息：

```bash
# Lean版本
lean --version

# Lake版本
lake --version

# Elan版本
elan --version

# 操作系统
uname -a  # Linux/Mac
ver       # Windows

# 项目状态
git status
git log --oneline -5
```

---

## Lean安装问题

### 问题1: Elan安装失败

**症状**:

```
curl: (35) error:0A000086:SSL routines::certificate verify failed
```

**原因**: SSL证书问题或网络连接问题

**解决方案**:

```bash
# Linux/Mac - 使用备用安装方式
curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# 或者下载预编译二进制
wget https://github.com/leanprover/elan/releases/latest/download/elan-x86_64-unknown-linux-gnu.tar.gz
tar xf elan-x86_64-unknown-linux-gnu.tar.gz
./elan-init -y

# Windows - 使用PowerShell
# 如果脚本执行失败，手动下载:
# 1. 访问 https://github.com/leanprover/elan/releases
# 2. 下载 elan-x86_64-pc-windows-msvc.zip
# 3. 解压并将路径添加到环境变量
```

---

### 问题2: 工具链下载失败

**症状**:

```
error: could not download file from ...
error: caused by: [28] Timeout
```

**原因**: 网络超时或防火墙限制

**解决方案**:

```bash
# 设置镜像源（中国用户）
elan toolchain install stable --default-toolchain none

# 使用代理
export https_proxy=http://proxy.example.com:8080
elan self update

# 手动下载工具链
# 1. 从 https://github.com/leanprover/lean4/releases 下载
# 2. 使用 elan toolchain link 命令关联
```

---

### 问题3: VS Code无法识别Lean

**症状**:

- 打开.lean文件无语法高亮
- InfoView显示"Waiting for Lean server..."

**原因**: 扩展未正确安装或路径配置问题

**解决方案**:

```bash
# 1. 确认Lean安装位置
which lean
# 或
where lean

# 2. 在VS Code设置中配置路径
# Ctrl+Shift+P -> Preferences: Open Settings (JSON)
{
  "lean4.toolchainPath": "/path/to/elan/bin"
}

# 3. 重启Lean服务器
# Ctrl+Shift+P -> Lean 4: Restart Server
```

---

### 问题4: 权限不足（Unix系统）

**症状**:

```
error: permission denied: ~/.elan/bin/lean
```

**解决方案**:

```bash
# 修复权限
chmod +x ~/.elan/bin/*
chmod +x ~/.elan/toolchains/*/bin/*

# 或者重新安装到用户目录
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
```

---

## 代码编译错误

### 问题5: 导入错误 (Unknown Module)

**症状**:

```
unknown module 'Mathlib.Data.Nat.Basic'
```

**原因**: 依赖未下载或lakefile配置错误

**解决方案**:

```bash
# 1. 更新依赖
lake update

# 2. 下载Mathlib缓存
lake exe cache get

# 3. 检查lakefile.lean
# 确保包含: require mathlib from git "..."

# 4. 重新构建
lake clean
lake build
```

---

### 问题6: 类型不匹配 (Type Mismatch)

**症状**:

```
type mismatch
  x
has type
  Nat : Type
but is expected to have type
  Int : Type
```

**解决方案**:

```lean
-- 显式类型转换
def f (n : Int) := n + 1
#eval f (3 : Nat).toInt  -- ✅

-- 或使用coercion
instance : Coe Nat Int := ⟨Int.ofNat⟩
#eval f 3  -- ✅ 自动转换

-- 检查函数签名
#check your_function
```

---

### 问题7: 无法合成实例 (Failed to Synthesize)

**症状**:

```
failed to synthesize instance
  Add α
```

**原因**: 缺少必要的Type Class实例

**解决方案**:

```lean
-- 1. 检查是否需要添加约束
variable [Add α]  -- 添加类型类约束

-- 2. 确认实例已定义
instance : Add MyType where
  add := ...

-- 3. 导入正确的模块
import Mathlib.Algebra.Group.Defs
```

---

### 问题8: 递归函数终止性错误

**症状**:

```
fail to show termination for
  f
with errors
  structural recursion cannot be used
```

**解决方案**:

```lean
-- 方法1: 使用结构递归
def f : Nat → Nat
  | 0 => ...
  | n + 1 => ...  -- 参数必须"变小"

-- 方法2: 显式指定终止度量
def g (m n : Nat) : Nat :=
  if m = 0 then n
  else g (m - 1) n
termination_by m n => m  -- 指定终止度量

-- 方法3: 使用 WellFounded
def h : Nat → Nat := ...
partial def h' : Nat → Nat := h  -- 如果确定会终止
```

---

### 问题9: 证明卡壳 (Stuck in Proof)

**症状**: 无法推进证明，目标状态不明确

**解决方案**:

```lean
theorem stuck : P := by
  -- 使用这些tactics查看状态
  trace_state        -- 打印当前目标
  trace "message"    -- 输出调试信息

  -- 尝试简化目标
  simp only []
  dsimp

  -- 如果完全卡住
  sorry  -- 教学示例：暂时跳过，用于演示故障排除技巧

  -- 或寻求帮助
  /-
  当前状态:
  P : Prop
  ⊢ Q
  尝试过: intro, apply, exact
  -/
```

---

### 问题10: 内存不足 (Out of Memory)

**症状**:

- 编译时系统卡顿
- 进程被系统kill
- "Killed" 错误信息

**解决方案**:

```bash
# 1. 限制并行任务数
lake build -j2  # 使用2个并行任务

# 2. 增加交换空间
sudo fallocate -l 8G /swapfile
sudo chmod 600 /swapfile
sudo mkswap /swapfile
sudo swapon /swapfile

# 3. 分批构建
lake build FormalScience.Concept  # 先构建特定模块

# 4. 清理缓存
lake clean
lake exe cache get  # 重新下载缓存
```

---

## 环境配置问题

### 问题11: Lakefile语法错误

**症状**:

```
error: lakefile.lean:5:2: error: unexpected token
```

**常见错误和修复**:

```lean
-- ❌ 错误: 使用旧版语法
package MyPackage

-- ✅ 正确: 使用新版DSL语法
package «my-package» where
  -- 配置

-- ❌ 错误: require位置不对
require mathlib from ...
package «my-package»

-- ✅ 正确: package在前
package «my-package»
require mathlib from ...

-- ❌ 错误: 缺少git
require mathlib from "https://..."

-- ✅ 正确: 使用git关键字
require mathlib from git "https://..."
```

---

### 问题12: Git子模块问题

**症状**:

```
fatal: not a git repository: ../../.git/modules/...
```

**解决方案**:

```bash
# 1. 清理并重新初始化
git submodule deinit -f .
git submodule update --init --recursive

# 2. 或者重新克隆
git clone --recursive <repo-url>

# 3. 如果不需要子模块，修改.gitmodules
```

---

### 问题13: 文件路径过长（Windows）

**症状**:

```
error: unable to create file ...: Filename too long
```

**解决方案**:

```powershell
# 以管理员身份运行PowerShell
# 启用长路径支持
New-ItemProperty -Path "HKLM:\SYSTEM\CurrentControlSet\Control\FileSystem" `
  -Name "LongPathsEnabled" -Value 1 -PropertyType DWORD -Force

# 或者将项目移动到更短的路径
cd C:\project  # 而不是 C:\Users\VeryLongUsername\Documents\...
```

---

### 问题14: VS Code InfoView空白

**症状**: InfoView面板打开但不显示内容

**解决方案**:

```bash
# 1. 检查Lean服务器状态
# 看右下角状态栏

# 2. 重启服务器
# Ctrl+Shift+P -> Lean 4: Restart Server

# 3. 检查输出面板
# Ctrl+Shift+P -> Output: Focus on Output View
# 选择 "Lean: Editor" 查看日志

# 4. 删除工作区存储
# 删除 .vscode/ 目录下的临时文件
rm -rf .vscode/.lean4-*
```

---

### 问题15: 编码问题

**症状**: 中文字符显示乱码或编译错误

**解决方案**:

```bash
# 确保文件为UTF-8编码
# VS Code右下角显示编码，点击可转换

# 添加文件头注释
/- -*- coding: utf-8 -*- -/

# 检查locale设置（Linux/Mac）
export LANG=en_US.UTF-8
export LC_ALL=en_US.UTF-8
```

---

## 常见错误及解决方案

### 错误对照表

| 错误信息 | 可能原因 | 解决方案 |
|---------|---------|---------|
| `unknown identifier` | 变量未定义或未导入 | 检查拼写，添加import |
| `application type mismatch` | 参数类型错误 | 使用`#check`检查签名 |
| `syntactic tautology` | 冗余代码 | 删除不必要的tactic |
| `maximum recursion depth` | 无限递归 | 检查递归基准情况 |
| `declaration uses sorry` | 未完成的证明 | 完成证明或移除sorry |
| `no goals to be solved` | 多余的tactic | 删除多余步骤 |
| `tactic failed` | 策略不适用 | 换用其他tactic |
| `metavariable` | 存在未赋值变量 | 使用`exact`或`apply`完成 |

---

### 问题16: 构建缓存失效

**症状**: 每次构建都重新编译所有文件

**解决方案**:

```bash
# 1. 确保使用cache
lake exe cache get

# 2. 检查磁盘空间
df -h  # Linux/Mac

# 3. 清理并重新下载
lake clean
rm -rf .lake
lake exe cache get

# 4. 如果cache服务不可用，本地构建
lake build  # 这可能需要较长时间
```

---

### 问题17: Mathlib版本不兼容

**症状**:

```
error: import Mathlib.X.Y failed, version mismatch
```

**解决方案**:

```bash
# 1. 更新到兼容版本
lake update mathlib

# 2. 回退到已知工作版本
# 编辑 lake-manifest.json
# 或重新克隆项目

# 3. 使用特定commit
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "abc123"
```

---

### 问题18: 循环依赖

**症状**:

```
import cycle detected
```

**解决方案**:

```lean
-- 重新组织文件结构
-- 将公共定义提取到单独文件

-- 之前:
-- A.lean imports B
-- B.lean imports A

-- 之后:
-- Common.lean  -- 定义共享内容
-- A.lean imports Common
-- B.lean imports Common
```

---

### 问题19: 名称冲突

**症状**:

```
ambiguous, possible interpretations: ...
```

**解决方案**:

```lean
-- 使用全限定名
open Classical
-- 或
open scoped Classical

-- 或显式指定命名空间
theorem T : ... := by
  exact Classical.em P

-- 重命名导入
import Mathlib.Data.Nat.Basic as NatDefs
```

---

### 问题20: 证明性能问题

**症状**: 证明执行缓慢，VS Code卡顿

**解决方案**:

```lean
-- 1. 限制simp范围
simp only [needed_lemmas]  -- 而不是 simp

-- 2. 使用更具体的tactic
rw [lemma]  -- 而不是 simp

-- 3. 分解长证明
theorem part1 : ... := ...
theorem part2 : ... := ...
theorem main : ... := by
  apply part1
  apply part2

-- 4. 设置超时
set_option maxHeartbeats 100000  -- 增加限制
```

---

## 获取帮助

### 自助资源

1. **官方文档**
   - [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
   - [Lean 4 Manual](https://lean-lang.org/lean4/doc/)

2. **API搜索**
   - [Loogle](https://loogle.lean-lang.org/) - 按类型签名搜索
   - [Mathlib4 Docs](https://leanprover-community.github.io/mathlib4_docs/)

3. **社区资源**
   - [Zulip Chat](https://leanprover.zulipchat.com/) - 实时讨论
   - [GitHub Issues](https://github.com/leanprover/lean4/issues)

### 提问模板

```markdown
## 问题描述
简要描述遇到的问题

## 环境信息
- OS: [Windows/macOS/Linux]
- Lean版本: [输出 of `lean --version`]
- 项目版本: [git commit hash]

## 复现步骤
1. 步骤一
2. 步骤二
3. ...

## 错误信息
```

粘贴完整错误信息

```

## 已尝试的解决方案
- 尝试A - 结果
- 尝试B - 结果
```

---

> 📌 **提示**: 保持软件更新是解决大多数问题的最佳方法。定期运行 `elan self update` 和 `lake update`。
