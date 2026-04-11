# 代码示例总索引

> 形式化科学项目代码示例库 - 涵盖 Lean 4、Rust 和 Haskell 三种语言

---

## 目录结构

```
examples/
├── lean/          # Lean 4 形式化数学示例
├── rust/          # Rust 系统编程示例
└── haskell/       # Haskell 函数式编程示例
```

---

## 示例导航

### 🧮 Lean 4 示例（形式化数学）

| 文件 | 内容 | 对应理论 | 难度 |
|------|------|----------|------|
| `basic.lean` | 基础数学定义（自然数、整数、实数、代数结构） | 数论、代数基础 | ⭐⭐ |
| `type_theory.lean` | 类型论构造（依赖类型、归纳类型、命题逻辑） | 类型论基础 | ⭐⭐⭐ |
| `category.lean` | 范畴论基本概念（范畴、函子、自然变换） | 范畴论 | ⭐⭐⭐⭐ |
| `scheduler.lean` | 调度算法的形式化证明 | 调度理论 | ⭐⭐⭐⭐⭐ |

### ⚙️ Rust 示例（系统编程）

| 文件 | 内容 | 对应理论 | 难度 |
|------|------|----------|------|
| `ownership.rs` | 所有权系统、借用检查、生命周期 | 线性类型论、资源管理 | ⭐⭐ |
| `type_system.rs` | 高级类型系统特性（泛型、Trait、关联类型） | 类型论、子类型 | ⭐⭐⭐ |
| `async.rs` | 异步编程和 Future 机制 | 计算理论、并发模型 | ⭐⭐⭐⭐ |
| `concurrent_patterns.rs` | 并发模式和线程安全 | 进程演算、并发理论 | ⭐⭐⭐⭐ |

### λ Haskell 示例（函数式编程）

| 文件 | 内容 | 对应理论 | 难度 |
|------|------|----------|------|
| `functor_monad.hs` | 函子、应用函子、单子 | 范畴论、单子论 | ⭐⭐⭐ |
| `type_class.hs` | 类型类和多态 | 类型论、特设多态 | ⭐⭐ |

---

## 运行环境要求

### Lean 4 环境

| 组件 | 最低版本 | 推荐版本 |
|------|----------|----------|
| Lean | 4.5.0 | 4.7.0+ |
| Lake | 内置 | 内置 |
| elan | 最新 | 最新 |

**安装命令：**

```bash
# 安装 Lean 4 (使用 elan)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# 验证安装
lean --version
```

### Rust 环境

| 组件 | 最低版本 | 推荐版本 |
|------|----------|----------|
| rustc | 1.75.0 | 1.78.0+ |
| Cargo | 内置 | 内置 |

**安装命令：**

```bash
# 安装 Rust (使用 rustup)
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# 验证安装
rustc --version
cargo --version
```

### Haskell 环境

| 组件 | 最低版本 | 推荐版本 |
|------|----------|----------|
| GHC | 9.0 | 9.6+ |
| Cabal | 3.6 | 3.10+ |
| Stack | 2.9 | 2.13+ |

**安装命令：**

```bash
# 安装 GHC (使用 ghcup)
curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh

# 验证安装
ghc --version
cabal --version
```

---

## 学习路径建议

### 初学者路径（无函数式编程基础）

```
1. Rust ownership.rs → 2. Haskell type_class.hs → 3. Lean basic.lean
```

**理由：** Rust 的所有权系统相对直观，Haskell 类型类引入多态概念，Lean 则综合应用这些概念。

### 数学背景路径（有数学基础）

```
1. Lean basic.lean → 2. Lean type_theory.lean → 3. Lean category.lean
     ↓                      ↓                        ↓
4. Haskell functor_monad.hs ← 5. Rust type_system.rs ← 6. Lean scheduler.lean
```

**理由：** 从数学形式化开始，理解类型论基础，再到范畴论，最后映射到编程语言实现。

### 系统编程路径（关注工程应用）

```
1. Rust ownership.rs → 2. Rust type_system.rs → 3. Rust async.rs
                                                            ↓
4. Rust concurrent_patterns.rs ← 5. Haskell functor_monad.hs
```

**理由：** 掌握 Rust 核心特性后，扩展到并发编程，再用 Haskell 理解单子在并发中的抽象。

### 形式化验证路径（专注定理证明）

```
1. Lean basic.lean → 2. Lean type_theory.lean → 3. Lean category.lean
                                                          ↓
4. Lean scheduler.lean → [项目案例] → 5. 自定义证明项目
```

**理由：** 循序渐进掌握 Lean 4 的证明技巧，最终能独立完成形式化验证项目。

---

## 快速运行

### Lean 4

```bash
cd lean

# 验证单个文件
lean --run basic.lean

# 创建项目并运行
lake new my_project math
cd my_project
# 复制示例文件到项目目录
lake build
```

### Rust

```bash
cd rust

# 编译单个文件
rustc --edition 2021 ownership.rs -o ownership
./ownership

# 使用 Cargo
cargo new my_project
cd my_project
# 将示例复制到 src/bin/ 目录
cargo run --bin ownership
```

### Haskell

```bash
cd haskell

# 直接运行
runhaskell functor_monad.hs

# 编译后运行
ghc --make functor_monad.hs -o functor_monad
./functor_monad
```

---

## 相关文档

- [概念索引](../08_附录/03_索引/03.1_概念索引.md) - 查找示例中涉及的核心概念
- [定理索引](../08_附录/03_索引/03.2_定理索引.md) - 查看形式化证明相关的定理
- [学习路线图](../07_交叉视角/03_学习路线图.md) - 完整的学习路径规划

---

## 外部资源

### Lean 4

- [Lean 4 官方文档](https://leanprover.github.io/lean4/doc/)
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)

### Rust

- [The Rust Programming Language](https://doc.rust-lang.org/book/)
- [Rust by Example](https://doc.rust-lang.org/rust-by-example/)
- [Rustonomicon](https://doc.rust-lang.org/nomicon/)（高级主题）

### Haskell

- [Learn You a Haskell](http://learnyouahaskell.com/)
- [Real World Haskell](http://book.realworldhaskell.org/)
- [Haskell Wiki](https://wiki.haskell.org/)
