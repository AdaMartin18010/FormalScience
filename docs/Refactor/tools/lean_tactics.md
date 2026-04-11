# Lean策略手册 🔍

> Lean定理证明器常用tactics速查，包含示例和效果说明

---

## 📑 目录

- [Lean策略手册 🔍](#lean策略手册-)
  - [📑 目录](#-目录)
  - [基础策略](#基础策略)
    - [目标管理](#目标管理)
    - [假设管理](#假设管理)
  - [逻辑连接词](#逻辑连接词)
    - [合取 (∧)](#合取-)
    - [析取 (∨)](#析取-)
    - [否定 (¬)](#否定-)
    - [真值与假值](#真值与假值)
  - [等式与重写](#等式与重写)
    - [重写策略](#重写策略)
    - [等式证明](#等式证明)
  - [量化词](#量化词)
    - [全称量词 (∀)](#全称量词-)
    - [存在量词 (∃)](#存在量词-)
  - [归纳法](#归纳法)
    - [自然数归纳](#自然数归纳)
    - [归纳变体](#归纳变体)
  - [自动化](#自动化)
    - [自动证明](#自动证明)
    - [搜索与提示](#搜索与提示)
  - [高级策略](#高级策略)
    - [目标转换](#目标转换)
    - [宏与组合](#宏与组合)
    - [块结构](#块结构)
  - [快速参考卡片](#快速参考卡片)
    - [常见证明模式](#常见证明模式)
    - [Mathlib常用](#mathlib常用)
  - [🔗 相关资源](#-相关资源)

---

## 基础策略

### 目标管理

| Tactic | 效果 | 示例 |
|--------|------|------|
| `intro` | 引入假设（消去→） | `intro h` 将 `P → Q` 转为在假设`h: P`下证`Q` |
| `intros` | 批量引入 | `intros x y h` 引入多个变量/假设 |
| `exact` | 精确匹配目标 | `exact h` 用假设`h`直接证明目标 |
| `apply` | 应用蕴含 | `apply h` 将 `Q` 转为证 `P`（若`h: P → Q`） |
| `refine` | 部分应用 | `refine h ?_` 应用`h`并生成剩余子目标 |

**示例：intro与exact**

```lean
example (P Q : Prop) (hp : P) (h : P → Q) : Q := by
  apply h      -- 目标变为 P
  exact hp     -- 用 hp 精确匹配
```

### 假设管理

| Tactic | 效果 | 示例 |
|--------|------|------|
| `have` | 建立中间结论 | `have h' : P := ...` |
| `let` | 定义局部变量 | `let n := 5` |
| `clear` | 清除假设 | `clear h` 移除假设h |
| `rename` | 重命名假设 | `rename _ h => h'` |
| `revert` | 反向intro | `revert h` 将假设转为目标前件 |

---

## 逻辑连接词

### 合取 (∧)

| Tactic | 效果 | 场景 |
|--------|------|------|
| `constructor` | 拆分合取目标 | `P ∧ Q` → 分别证`P`和`Q` |
| `left` | 选择左边 | 证 `P` 部分 |
| `right` | 选择右边 | 证 `Q` 部分 |
| `cases` | 分解合取假设 | `cases h with hp hq` 得`hp: P`, `hq: Q` |

**示例：合取**

```lean
-- 构造
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

-- 分解
example (P Q : Prop) (h : P ∧ Q) : P := by
  cases h with
  | intro hp _ => exact hp
```

### 析取 (∨)

| Tactic | 效果 | 场景 |
|--------|------|------|
| `left` | 选择左边证明 | 目标 `P ∨ Q`，选择证`P` |
| `right` | 选择右边证明 | 目标 `P ∨ Q`，选择证`Q` |
| `cases` | 分类讨论 | `cases h` 分`P`或`Q`两种情况 |

**示例：析取**

```lean
-- 构造
example (P Q : Prop) (hp : P) : P ∨ Q := by
  left
  exact hp

-- 分类讨论
example (P Q R : Prop) (h : P ∨ Q) (hp : P → R) (hq : Q → R) : R := by
  cases h with
  | inl hp' => apply hp hp'
  | inr hq' => apply hq hq'
```

### 否定 (¬)

| Tactic | 效果 | 场景 |
|--------|------|------|
| `intro` | 引入假设 | `¬P` 即 `P → False` |
| `contradiction` | 发现矛盾 | 当假设中有`P`和`¬P` |
| `exfalso` | 转为证False | 用于反证 |

**示例：否定**

```lean
example (P : Prop) : ¬(P ∧ ¬P) := by
  intro h
  cases h with
  | intro hp hnp => contradiction
```

### 真值与假值

| Tactic | 效果 | 场景 |
|--------|------|------|
| `trivial` | 证明True | 目标为`True` |
| `exfalso` | 转为证False | 使用矛盾前提 |
| `contradiction` | 自动找矛盾 | 上下文有矛盾时 |

---

## 等式与重写

### 重写策略

| Tactic | 效果 | 示例 |
|--------|------|------|
| `rw` | 重写等式 | `rw [h]` 用`h: a = b`替换 |
| `rwa` | rw + assumption | `rwa [h]` 重写后尝试assumption |
| `simp` | 简化表达式 | `simp [h1, h2]` 用引理简化 |
| `simp_all` | 简化所有 | 简化目标和所有假设 |
| `dsimp` | 定义简化 | 只展开定义 |

**方向修饰符**

```lean
rw [h]     -- 左到右: a → b
rw [←h]    -- 右到左: b → a
rw [h] at hp -- 在假设hp中重写
```

**示例：重写**

```lean
example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1]    -- 目标变为 b = c
  rw [h2]    -- 目标变为 c = c
  rfl        -- 自反性

-- 或使用传递性
example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1, h2]  -- 链式重写
```

### 等式证明

| Tactic | 效果 | 场景 |
|--------|------|------|
| `rfl` | 自反性 | 证明 `a = a` |
| `symm` | 对称性 | `h: a = b` 得 `b = a` |
| `trans` | 传递性 | 连接两个等式 |
| `subst` | 代入 | 用等式替换变量 |

---

## 量化词

### 全称量词 (∀)

| Tactic | 效果 | 示例 |
|--------|------|------|
| `intro` | 引入变量 | `∀ x, P x` → 证 `P x` |
| `intros` | 批量引入 | `intros x y h` |
| `specialize` | 特化全称 | `specialize h a` 得 `h : P a` |

**示例：全称**

```lean
-- 证明
example : ∀ (n : Nat), n + 0 = n := by
  intro n
  rw [Nat.add_zero]

-- 使用
example (h : ∀ n, n + 0 = n) : 5 + 0 = 5 := by
  specialize h 5
  exact h
```

### 存在量词 (∃)

| Tactic | 效果 | 示例 |
|--------|------|------|
| `use` | 提供见证 | `use 5` 证 `∃x, P x` |
| `exists` | 同use | `exists 5` |
| `cases` | 分解存在 | `cases h with x hx` |
| `obtain` | 解构存在 | `obtain ⟨x, hx⟩ := h` |

**示例：存在**

```lean
-- 构造
example : ∃ (n : Nat), n > 5 := by
  use 6
  norm_num

-- 使用
example (h : ∃ n, n > 5) : ∃ m, m > 4 := by
  cases h with
  | intro n hn =>
    use n
    linarith
```

---

## 归纳法

### 自然数归纳

| Tactic | 效果 | 示例 |
|--------|------|------|
| `induction` | 归纳原理 | `induction n with` |
| `induction'` | Mathlib版 | 更友好的语法 |
| `cases` | 情况分析 | 无归纳假设的分析 |

**示例：归纳**

```lean
-- 标准归纳
theorem sum_formula (n : Nat) : ∑ i in range n, i = n * (n - 1) / 2 := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    ring

-- 结构归纳 (列表)
theorem list_length_append {α} (l1 l2 : List α) :
  (l1 ++ l2).length = l1.length + l2.length := by
  induction l1 with
  | nil => simp
  | cons x xs ih =>
    simp [ih]
    rw [Nat.add_succ]
```

### 归纳变体

```lean
-- 强归纳
induction n using Nat.strongRecOn

-- 二进制归纳
induction n using Nat.binaryRec

-- 双向归纳 (用于整数)
induction n using Int.inductionOn
```

---

## 自动化

### 自动证明

| Tactic | 能力 | 适用 |
|--------|------|------|
| `trivial` | 证明True/平凡等式 | 简单目标 |
| `simp` | 简化+重写 | 代数表达式 |
| `simp_all` | 全面简化 | 复杂上下文 |
| `aesop` | 自动搜索 | 一般性命题 |
| `omega` | Presburger算术 | 线性整数不等式 |
| `linarith` | 线性算术 | 线性等式/不等式 |
| `nlinarith` | 非线性算术 | 含乘积的不等式 |
| `ring` | 环论自动 | 多项式等式 |
| `field_simp` | 域简化 | 分式表达式 |
| `norm_num` | 数值计算 | 具体数字计算 |

**示例：自动化**

```lean
example (x y : Int) (h1 : x + y > 5) (h2 : 2*x < 6) : y > 2 := by
  linarith  -- 自动推导线性不等式

example (n : Nat) : n * (n + 1) = n^2 + n := by
  ring  -- 自动证明多项式等式

example (h : 5 > 3) : 5 + 2 > 3 + 2 := by
  norm_num at h ⊢  -- 规范化数字表达式
  exact h
```

### 搜索与提示

| Tactic | 效果 | 示例 |
|--------|------|------|
| `library_search` | 库搜索 | 找已有引理 |
| `exact?` | 精确搜索 | 找精确匹配 |
| `apply?` | 应用搜索 | 找可应用的引理 |
| `hint` | 获取提示 | 建议可能的tactics |

---

## 高级策略

### 目标转换

| Tactic | 效果 | 示例 |
|--------|------|------|
| `suffices` | 证明充分条件 | `suffices h : P` |
| `show` | 显式声明目标 | `show P` 确认当前目标 |
| `change` | 等价转换 | `change P` 用等价式替换目标 |
| `convert` | 转换证明 | `convert h` 生成差异子目标 |
| `congr` | 同余 | 证明函数应用的相等 |

### 宏与组合

| Tactic | 效果 | 示例 |
|--------|------|------|
| `<;>` | 顺序应用 | `tac1 <;> tac2` 对所有子目标应用tac2 |
| `all_goals` | 所有目标 | `all_goals tac` |
| `any_goals` | 任意目标 | `any_goals tac` |
| `first` | 第一个成功 | `first \| tac1 \| tac2 \| tac3` |
| `repeat` | 重复 | `repeat tac` |
| `try` | 容错 | `try tac` 失败不停止 |

**示例：组合**

```lean
-- 对所有子目标应用simp
all_goals simp

-- 尝试多个tactics
first | exact h1 | exact h2 | simp

-- 顺序处理
constructor <;> simp <;> try linarith
```

### 块结构

```lean
-- 使用点号聚焦
constructor
· -- 第一个子目标
  exact hp
· -- 第二个子目标
  exact hq

-- 使用focus
focus
  tac1
  tac2
end

-- 使用case命名
cases h with
| inl hp => ...
| inr hq => ...
```

---

## 快速参考卡片

### 常见证明模式

| 要证 | 起始策略 |
|------|---------|
| `P → Q` | `intro h` |
| `P ∧ Q` | `constructor` |
| `P ∨ Q` | `left` 或 `right` |
| `¬P` | `intro h` |
| `∀ x, P x` | `intro x` |
| `∃ x, P x` | `use witness` |
| `a = b` | `rw [h]` 或 `ring` |
| 任意命题 | `apply?` 找引理 |

### Mathlib常用

```lean
-- 定义展开
unfold def_name

-- 函数扩展
funext x

-- 命题扩展
propext h

-- 选择原理
cases' Classical.em P with hp hnp

-- 反证法
by_contra h
push_neg at h
```

---

## 🔗 相关资源

- [公式速查表](./formula_sheet.md) - 数学公式
- [Rust设计模式](./rust_patterns.md) - 编程技巧
- [术语查询工具](./glossary_tool.md) - 类型理论术语

---

_Lean版本: 4.x | 最后更新: 2026-04-11_
