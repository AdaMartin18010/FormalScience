# 快速参考手册

> 形式化科学核心知识速查表 - 定理、公式、代码片段与符号

---

## 1. 常用定理速查

### 1.1 数理逻辑

| 定理 | 表述 | 应用 |
|------|------|------|
| **哥德尔完备性定理** | Γ ⊢ φ ⟺ Γ ⊨ φ | 证明系统可靠性 |
| **哥德尔不完备定理** | 足够强系统存在不可判定命题 | 形式系统局限性 |
| **紧致性定理** | 有限可满足 ⟹ 整体可满足 | 模型构造 |
| **柯里-霍华德对应** | 证明 ⟺ 程序 | 类型系统与逻辑对应 |

### 1.2 λ演算

| 定理 | 表述 | 应用 |
|------|------|------|
| **邱奇-罗瑟定理** | 若 M → N 且 M → P，则 ∃Q: N → Q 且 P → Q | 合流性保证 |
| **标准型定理** | 左最外规约可达标准型 | 求值策略 |
| **正规化定理** | 良类型项强正规化 | 程序终止性 |

### 1.3 类型系统

| 定理 | 表述 | 应用 |
|------|------|------|
| **类型安全性** | 进展性 + 保持性 | 运行时安全保证 |
| **进展性** | 良类型非值项可规约 | 程序不会卡住 |
| **保持性** | Γ ⊢ M : τ 且 M → N ⟹ Γ ⊢ N : τ | 类型在规约下保持 |

### 1.4 范畴论

| 定理 | 表述 | 应用 |
|------|------|------|
| **米田引理** | Hom(A, -) ≅ Hom(B, -) ⟹ A ≅ B | 可表函子、泛性质 |
| **伴随泛性质** | L ⊣ R ⟺ Hom(LA, B) ≅ Hom(A, RB) | 自由构造、单子 |

### 1.5 调度理论

| 定理 | 表述 | 应用 |
|------|------|------|
| **RMS最优性** | 利用率测试: U ≤ n(2^(1/n) - 1) | 实时任务可调度性 |
| **EDF最优性** | U ≤ 1 时EDF最优 | 动态优先级调度 |
| **Liu-Layland界** | U ≤ ln(2) ≈ 0.693 | RMS利用率上界 |

---

## 2. 常用公式速查

### 2.1 λ演算

**β规约：**

```
(λx.M) N →β M[N/x]
```

**η规约：**

```
λx.(M x) →η M   (若 x ∉ FV(M))
```

**替换（定义）：**

```
x[N/x] = N
y[N/x] = y       (y ≠ x)
(λy.M)[N/x] = λy.(M[N/x])  (y ∉ FV(N))
(M P)[N/x] = (M[N/x])(P[N/x])
```

### 2.2 类型系统

**简单类型：**

```
τ ::= ι | τ → τ | τ × τ | τ + τ
```

**System F（多态类型）：**

```
τ ::= α | τ → τ | ∀α.τ
```

**依赖类型：**

```
τ ::= x | Type | (x:τ) → τ | (x:τ) × τ | λx:τ.τ | τ τ
```

**类型推导规则（应用）：**

```
Γ ⊢ M : σ → τ    Γ ⊢ N : σ
─────────────────────────── (→E)
      Γ ⊢ M N : τ

   Γ, x:σ ⊢ M : τ
──────────────────── (→I)
Γ ⊢ λx:σ.M : σ → τ
```

### 2.3 范畴论

**泛性质（积）：**

```
∀Z, ∀f: Z→A, ∀g: Z→B, ∃!h: Z→A×B:
  π₁ ∘ h = f ∧ π₂ ∘ h = g
```

**伴随（Hom集同构）：**

```
Hom_C(LA, B) ≅ Hom_D(A, RB)
```

**单子定律：**

```
μ ∘ Tμ = μ ∘ μT      (结合律)
μ ∘ ηT = id = μ ∘ Tη  (单位律)
```

### 2.4 时序逻辑

**LTL公式：**

```
φ ::= p | ¬φ | φ ∧ ψ | ◯φ | ◇φ | □φ | φ U ψ

◯φ : 下一时刻φ成立
◇φ : 最终φ成立
□φ : 总是φ成立
φ U ψ : φ一直成立直到ψ成立
```

**CTL公式：**

```
φ ::= p | ¬φ | φ ∧ ψ | AX φ | EX φ
    | AF φ | EF φ | AG φ | EG φ
    | A[φ U ψ] | E[φ U ψ]

A: 所有路径
E: 存在路径
X: 下一状态
F: 最终
G: 总是
U: 直到
```

### 2.5 调度理论

**利用率：**

```
U = Σ(Ci/Ti)

Ci: 最坏执行时间
Ti: 周期
```

**响应时间分析：**

```
Ri = Ci + Σ⌈Ri/Tj⌉·Cj   (j ∈ hp(i))

hp(i): 优先级高于i的任务集合
```

**速率单调优先级：**

```
Pi > Pj ⟺ Ti < Tj
```

---

## 3. 常用代码片段

### 3.1 Lean 4

**基础证明结构：**

```lean
theorem example_theorem (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]
```

**定义归纳类型：**

```lean
inductive Tree (α : Type)
  | leaf : Tree α
  | node : α → Tree α → Tree α → Tree α
```

**类型类实例：**

```lean
instance : Functor Option where
  map f x := match x with
    | some a => some (f a)
    | none => none
```

### 3.2 Rust

**所有权与借用：**

```rust
// 所有权转移
fn take_ownership(s: String) {
    println!("{}", s);
} // s 在这里被drop

// 不可变借用
fn borrow(s: &String) {
    println!("{}", s);
} // s 继续有效

// 可变借用
fn mutate(s: &mut String) {
    s.push_str("!");
}
```

**泛型与Trait：**

```rust
pub trait Scheduler<T> {
    fn schedule(&mut self, tasks: Vec<T>) -> Vec<T>;
}

pub struct RoundRobin<T> {
    queue: VecDeque<T>,
}

impl<T> Scheduler<T> for RoundRobin<T> {
    fn schedule(&mut self, tasks: Vec<T>) -> Vec<T> {
        // 实现...
        tasks
    }
}
```

**异步模式：**

```rust
async fn fetch_data(url: &str) -> Result<String, Error> {
    let response = reqwest::get(url).await?;
    let text = response.text().await?;
    Ok(text)
}

// 并发执行
let (result1, result2) = tokio::join!(
    fetch_data("url1"),
    fetch_data("url2")
);
```

### 3.3 Haskell

**单子定义：**

```haskell
class Functor f where
  fmap :: (a -> b) -> f a -> f b

class Functor f => Applicative f where
  pure :: a -> f a
  (<*>) :: f (a -> b) -> f a -> f b

class Applicative m => Monad m where
  (>>=) :: m a -> (a -> m b) -> m b
  return :: a -> m a
  return = pure
```

**单子实例（Maybe）：**

```haskell
instance Monad Maybe where
  Nothing >>= _ = Nothing
  Just x >>= f = f x

  return = Just
```

**do语法：**

```haskell
calc :: Maybe Int
calc = do
  x <- Just 5
  y <- Just 10
  return (x + y)
-- 结果: Just 15
```

### 3.4 伪代码（算法描述）

**工作窃取调度器：**

```
function WORK-STEALING-SCHEDULER:
  each worker has DEQUE of tasks

  PUSH(task):
    worker.local_deque.push_bottom(task)

  POP():
    return worker.local_deque.pop_bottom()

  STEAL(victim):
    return victim.deque.pop_top()
```

**响应时间分析：**

```
function RESPONSE-TIME-ANALYSIS(task i):
  R = Ci
  repeat:
    R' = R
    R = Ci + Σ⌈R'/Tj⌉·Cj for all j in hp(i)
  until R = R' or R > Di

  if R ≤ Di then schedulable else unschedulable
```

---

## 4. 符号速查

### 4.1 逻辑符号

| 符号 | 名称 | 含义 |
|------|------|------|
| ¬ | 非 | 否定 |
| ∧ | 且 | 合取 |
| ∨ | 或 | 析取 |
| → | 蕴含 | 如果...那么... |
| ↔ | 等价 | 当且仅当 |
| ∀ | 全称量词 | 对所有 |
| ∃ | 存在量词 | 存在 |
| ⊢ | 推出 | 语法可证 |
| ⊨ | 满足 | 语义蕴涵 |
| ⊤ | 真 | 恒真 |
| ⊥ | 假 | 恒假/底部 |

### 4.2 集合论符号

| 符号 | 名称 | 含义 |
|------|------|------|
| ∈ | 属于 | 元素属于集合 |
| ⊆ | 包含于 | 子集 |
| ∪ | 并 | 并集 |
| ∩ | 交 | 交集 |
| ∅ | 空集 | 不含元素的集合 |
| ℘(A) | 幂集 | A的所有子集 |
| × | 笛卡尔积 | 有序对集合 |
| \ | 差集 | 相对补集 |
| \|A\| | 基数 | 集合元素个数 |
| ℕ | 自然数集 | {0, 1, 2, ...} |
| ℤ | 整数集 | {..., -1, 0, 1, ...} |
| ℚ | 有理数集 | 分数集合 |
| ℝ | 实数集 | 实数集合 |

### 4.3 类型论语义

| 符号 | 名称 | 含义 |
|------|------|------|
| → | 函数类型 | A → B: A到B的函数 |
| × | 积类型 | A × B: 有序对 |
| + | 和类型 | A + B: 互斥或 |
| ∀ | 全称类型 | ∀α.τ: 多态类型 |
| ∃ | 存在类型 | ∃α.τ: 存在量化类型 |
| Π | 依赖积 | Π(x:A).B(x): 依赖函数 |
| Σ | 依赖和 | Σ(x:A).B(x): 依赖对 |
| ≡ | 定义相等 | 定义等价 |
| ≝ | 定义为 | 定义为 |
| ≈ | 近似/等价 | 近似相等 |

### 4.4 范畴论符号

| 符号 | 名称 | 含义 |
|------|------|------|
| Ob(C) | 对象类 | 范畴C的对象 |
| Hom(A,B) | 态射集 | A到B的态射 |
| ∘ | 复合 | 态射复合 |
| id_A | 恒等态射 | A上的恒等 |
| C^op | 反范畴 | 对偶范畴 |
| C × D | 积范畴 | 范畴的积 |
| Set | 集合范畴 | 集合和函数 |
| Cat | 范畴范畴 | 小范畴和函子 |

### 4.5 时序逻辑符号

| 符号 | 名称 | 含义 |
|------|------|------|
| ◯ | 下一时刻 | X (Next) |
| ◇ | 最终 | F (Future) |
| □ | 总是 | G (Globally) |
| U | 直到 | U (Until) |
| R | 释放 | R (Release) |
| A | 所有路径 | 全称路径量词 |
| E | 存在路径 | 存在路径量词 |

### 4.6 调度系统符号

| 符号 | 名称 | 含义 |
|------|------|------|
| τ | 任务 | Task |
| T | 周期 | Period |
| C | 执行时间 | Execution Time |
| D | 截止时间 | Deadline |
| P | 优先级 | Priority |
| U | 利用率 | Utilization |
| R | 响应时间 | Response Time |
| J | 抖动 | Jitter |
| B | 阻塞时间 | Blocking Time |
| sched | 可调度 | Schedulable |

---

## 5. 快捷键与命令

### 5.1 Lean 4

| 命令 | 功能 |
|------|------|
| `Ctrl+Shift+Enter` | 执行当前行 |
| `Ctrl+Space` | 自动补全 |
| `lake build` | 构建项目 |
| `lake env lean --server` | 启动语言服务器 |
| `#check expr` | 检查表达式类型 |
| `#eval expr` | 求值表达式 |
| `simp` | 简化 |
| `rfl` | 自反性证明 |
| `induction x` | 归纳证明 |

### 5.2 Rust

| 命令 | 功能 |
|------|------|
| `cargo build` | 构建项目 |
| `cargo run` | 运行项目 |
| `cargo test` | 运行测试 |
| `cargo check` | 快速类型检查 |
| `cargo clippy` | 代码检查 |
| `cargo doc` | 生成文档 |
| `rustfmt` | 格式化代码 |

### 5.3 Haskell

| 命令 | 功能 |
|------|------|
| `ghc --make file.hs` | 编译 |
| `runhaskell file.hs` | 直接运行 |
| `cabal build` | 构建项目 |
| `cabal repl` | 交互式环境 |
| `:t expr` | 查看类型 |
| `:i name` | 查看信息 |
| `:q` | 退出 GHCi |

---

## 6. 常用缩写对照

| 缩写 | 全称 | 中文 |
|------|------|------|
| PLT | Programming Language Theory | 编程语言理论 |
| FP | Functional Programming | 函数式编程 |
| OOP | Object-Oriented Programming | 面向对象编程 |
| ADT | Algebraic Data Type | 代数数据类型 |
| GADT | Generalized ADT | 广义代数数据类型 |
| HOAS | Higher-Order Abstract Syntax | 高阶抽象语法 |
| CPS | Continuation-Passing Style | 续传递风格 |
| IR | Intermediate Representation | 中间表示 |
| CFG | Control Flow Graph | 控制流图 |
| SSA | Static Single Assignment | 静态单赋值 |
| LTL | Linear Temporal Logic | 线性时序逻辑 |
| CTL | Computation Tree Logic | 计算树逻辑 |
| TLA | Temporal Logic of Actions | 动作时序逻辑 |
| CMDP | Constrained MDP | 约束马尔可夫决策过程 |
| RL | Reinforcement Learning | 强化学习 |
| RMS | Rate Monotonic Scheduling | 速率单调调度 |
| EDF | Earliest Deadline First | 最早截止时间优先 |

---

## 参考链接

- [概念索引](08_附录/03_索引/03.1_概念索引.md)
- [定理索引](08_附录/03_索引/03.2_定理索引.md)
- [代码示例索引](08_附录/03_索引/03.3_代码示例索引.md)
- [符号表](08_附录/02_符号表/)
