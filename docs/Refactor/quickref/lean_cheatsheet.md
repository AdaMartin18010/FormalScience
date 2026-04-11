# Lean 4 速查卡

> 单页速查 | 常用Tactics | 类型定义 | 证明模式

---

## 常用Tactics（一页纸）

| 类别 | Tactic | 功能 | 示例 |
|------|--------|------|------|
| **基础** | `intro` | 引入假设/变量 | `intro h` |
| | `intros` | 引入多个 | `intros a b h` |
| | `exact` | 精确匹配目标 | `exact h` |
| | `apply` | 应用蕴含 | `apply h` |
| | `refine` | 部分应用 | `refine h ?_` |
| **重写** | `rw` | 重写等式 | `rw [h]` |
| | `rwa` | 重写+尝试精确 | `rwa [h]` |
| | `simp` | 简化表达式 | `simp [h1, h2]` |
| | `simp_all` | 简化所有假设和目标 | `simp_all` |
| **归纳** | `induction` | 归纳证明 | `induction n with` |
| | `cases` | 情况分析 | `cases h with` |
| | `destruct` | 解构存在量词 | `destruct h` |
| **目标操作** | `have` | 引入中间结论 | `have h : P := ...` |
| | `show` | 显式声明目标 | `show P` |
| | `suffices` | 证明充分条件 | `suffices h : P` |
| | `by_contra` | 反证法 | `by_contra h` |
| **自动化** | `tauto` | 命题逻辑自动 | `tauto` |
| | `linarith` | 线性算术自动 | `linarith` |
| | `aesop` | 通用自动证明 | `aesop` |
| | `omega` | 整数算术自动 | `omega` |

---

## 类型定义速查

| 定义类型 | 语法 | 示例 |
|----------|------|------|
| **函数类型** | `A → B` | `Nat → Bool` |
| **依赖函数** | `(x : A) → B x` | `(n : Nat) → Vector Nat n` |
| **积类型** | `A × B` | `Nat × Bool` |
| **和类型** | `A ⊕ B` | `String ⊕ Nat` |
| **单位类型** | `Unit` | `()` |
| **空类型** | `Empty` | - |
| **命题** | `Prop` | `1 + 1 = 2` |
| **全称量词** | `∀ x : A, P x` | `∀ n : Nat, n ≥ 0` |
| **存在量词** | `∃ x : A, P x` | `∃ n : Nat, n > 5` |

### 自定义类型

```lean
-- 枚举类型
inductive Color : Type
  | red | green | blue

-- 递归类型
inductive NatList : Type
  | nil
  | cons (head : Nat) (tail : NatList)

-- 归纳族
inductive Vec (A : Type) : Nat → Type
  | nil : Vec A 0
  | cons : A → Vec A n → Vec A (n+1)

-- 结构体
structure Point where
  x : Float
  y : Float
```

---

## 证明模式速查

| 证明目标 | 模式 | 代码示例 |
|----------|------|----------|
| **蕴含** $P → Q$ | 假设P证Q | `intro hp; ...; exact hq` |
| **合取** $P ∧ Q$ | 分别证明 | `constructor; · exact hp; · exact hq` |
| **析取** $P ∨ Q$ | 选一边 | `left; exact hp` / `right; exact hq` |
| **否定** $¬P$ | 反证 | `intro hp; ...; contradiction` |
| **等价** $P ↔ Q$ | 双向证明 | `constructor; · exact h1; · exact h2` |
| **存在** $∃x, P(x)$ | 构造见证 | `use witness; exact h` |
| **等式** | 重写/自反 | `rw [h]` / `rfl` |
| **全称** $∀x, P(x)$ | 任意引入 | `intro x; ...` |
| **唯一存在** $∃!x, P(x)$ | 存在+唯一 | `exists_unique` |

---

## 常用库速查

| 导入 | 内容 |
|------|------|
| `import Mathlib` | 数学库全集 |
| `import Mathlib.Data.Nat.Basic` | 自然数基础 |
| `import Mathlib.Algebra.Group.Basic` | 群论基础 |
| `import Mathlib.Topology.Basic` | 拓扑基础 |
| `import Mathlib.Logic.Basic` | 逻辑基础 |

---

## 命令速查

| 命令 | 功能 |
|------|------|
| `theorem` / `lemma` | 声明定理 |
| `def` | 定义函数 |
| `example` | 匿名证明 |
| `variable` | 声明变量 |
| `open` | 打开命名空间 |
| `namespace` | 定义命名空间 |
| `section` / `end` | 代码块分隔 |

---

*打印版：A4横向，适合快速查阅*
