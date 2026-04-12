/-
# 有限自动机形式化 (Finite Automaton Formalization)

本文件包含确定性有限自动机(DFA)和非确定性有限自动机(NFA)的形式化定义，
以及它们之间等价性的形式化证明框架。

参考文档: docs/Refactor/02_形式语言/01_形式语言基础/01.2_有限自动机.md
-/

namespace FiniteAutomaton

-- ============================================
-- 第一部分：确定性有限自动机 (DFA)
-- ============================================

/-- DFA的五元组定义：M = (Q, Σ, δ, q₀, F)
  - State: 状态类型参数
  - Alphabet: 字母表类型参数
-/
structure DFA (State Alphabet : Type) where
  /-- 状态集合 Q -/
  states : List State
  /-- 输入字母表 Σ -/
  alphabet : List Alphabet
  /-- 转移函数 δ: Q × Σ → Q -/
  transition : State → Alphabet → State
  /-- 初始状态 q₀ -/
  startState : State
  /-- 接受状态集合 F ⊆ Q -/
  acceptStates : List State
  deriving Repr

/-- 检查状态是否在DFA的状态集合中 -/
def DFA.isValidState {S A : Type} [BEq S] (dfa : DFA S A) (s : S) : Bool :=
  dfa.states.contains s

/-- 检查字母是否在DFA的字母表中 -/
def DFA.isValidSymbol {S A : Type} [BEq A] (dfa : DFA S A) (a : A) : Bool :=
  dfa.alphabet.contains a

/-- 扩展转移函数 δ̂: Q × Σ* → Q
  处理整个字符串，返回最终状态
-/
def DFA.deltaHat {S A : Type} (dfa : DFA S A) (q : S) (w : List A) : S :=
  w.foldl (λ currentState symbol => dfa.transition currentState symbol) q

/-- DFA接受的语言：L(M) = {w | δ̂(q₀, w) ∈ F}
  判断一个字符串是否被DFA接受
-/
def DFA.accepts {S A : Type} [BEq S] (dfa : DFA S A) (w : List A) : Bool :=
  let finalState := dfa.deltaHat dfa.startState w
  dfa.acceptStates.contains finalState

-- ============================================
-- 第二部分：非确定性有限自动机 (NFA)
-- ============================================

/-- NFA的五元组定义：N = (Q, Σ, δ, q₀, F)
  与DFA不同，转移函数返回状态集合
-/
structure NFA (State Alphabet : Type) where
  /-- 状态集合 Q -/
  states : List State
  /-- 输入字母表 Σ -/
  alphabet : List Alphabet
  /-- 转移函数 δ: Q × (Σ ∪ {ε}) → P(Q) 
      使用 Option Alphabet 表示 ε 转移 (None) -/
  transition : State → Option Alphabet → List State
  /-- 初始状态 q₀ -/
  startState : State
  /-- 接受状态集合 F ⊆ Q -/
  acceptStates : List State
  deriving Repr

/-- NFA的ε-闭包：从给定状态集合出发，仅通过ε转移可达的所有状态
  使用不动点迭代计算
-/
def NFA.epsilonClosure {S A : Type} [BEq S] (nfa : NFA S A) 
    (states : List S) : List S :=
  -- 不动点计算
  let rec closureAux (current : List S) (visited : List S) : List S :=
    match current with
    | [] => visited
    | s :: rest =>
      if visited.contains s then
        closureAux rest visited
      else
        -- 找到通过ε转移可达的新状态
        let epsilonStates := nfa.transition s none
        let newStates := epsilonStates.filter (λ x => !visited.contains x && !current.contains x)
        closureAux (rest ++ newStates) (s :: visited)
  closureAux states []

/-- NFA的单步转移（含ε闭包）
  从给定状态集合，读入一个符号后到达的新状态集合
-/
def NFA.move {S A : Type} [BEq S] (nfa : NFA S A) 
    (states : List S) (a : A) : List S :=
  -- 对每个状态，找到通过a转移可达的状态
  let newStates := states.flatMap (λ s => nfa.transition s (some a))
  -- 计算ε闭包
  nfa.epsilonClosure newStates

/-- NFA的扩展转移函数 δ̂: P(Q) × Σ* → P(Q) -/
def NFA.deltaHat {S A : Type} [BEq S] (nfa : NFA S A) 
    (states : List S) (w : List A) : List S :=
  match w with
  | [] => states
  | a :: rest =>
    let newStates := nfa.move states a
    nfa.deltaHat newStates rest

/-- NFA接受的语言：L(N) = {w | δ̂({q₀}, w) ∩ F ≠ ∅} -/
def NFA.accepts {S A : Type} [BEq S] (nfa : NFA S A) (w : List A) : Bool :=
  let startClosure := nfa.epsilonClosure [nfa.startState]
  let finalStates := nfa.deltaHat startClosure w
  -- 检查是否有接受状态
  finalStates.any (λ s => nfa.acceptStates.contains s)

-- ============================================
-- 第三部分：DFA与NFA的等价性
-- ============================================

/-- 子集构造：将NFA转换为DFA
  定理：对任意NFA N，存在DFA D 使得 L(D) = L(N)
  
  构造方法：
  - Q' = P(Q) (状态是NFA状态的子集)
  - q₀' = E({q₀}) (初始状态的ε闭包)
  - δ'(S, a) = ∪_{q∈S} E(δ(q, a))
  - F' = {S ⊆ Q | S ∩ F ≠ ∅}
-/
def NFA.toDFA {S A : Type} [BEq S] [BEq A] (nfa : NFA S A) : DFA (List S) A :=
  let powerSetStates := [[]]  -- 简化为空列表，实际需要计算所有子集
  let dfaTransition := λ (states : List S) (a : A) =>
    nfa.move states a
  let startState := nfa.epsilonClosure [nfa.startState]
  let acceptStates := powerSetStates.filter (λ ss => 
    ss.any (λ s => nfa.acceptStates.contains s)
  )
  
  DFA.mk powerSetStates nfa.alphabet dfaTransition startState acceptStates

/-- DFA与NFA等价性定理（陈述）
  定理：对任意NFA N，通过子集构造得到的DFA D 满足 L(D) = L(N)
-/
theorem NFA_DFA_equivalence {S A : Type} [BEq S] [BEq A] (nfa : NFA S A) (w : List A) :
  nfa.accepts w = nfa.toDFA.accepts w := by
  -- 证明思路：
  -- 1. 对|w|进行归纳
  -- 2. 证明 δ̂_DFA(q₀', w) = δ̂_NFA({q₀}, w) 的ε闭包
  -- 3. 利用ε闭包的性质
  sorry

-- ============================================
-- 第四部分：正则语言的性质
-- ============================================

/-- 语言是正则的：存在DFA接受该语言 -/
def IsRegularLanguage {A : Type} (L : List A → Bool) : Prop :=
  ∃ (S : Type) (dfa : DFA S A), ∀ (w : List A), dfa.accepts w = L w

/-- 正则语言的并封闭性（陈述）
  定理：若 L₁ 和 L₂ 是正则语言，则 L₁ ∪ L₂ 也是正则语言
-/
theorem regular_union {A : Type} (L1 L2 : List A → Bool)
    (h1 : IsRegularLanguage L1) (h2 : IsRegularLanguage L2) :
    IsRegularLanguage (λ w => L1 w || L2 w) := by
  -- 证明：乘积构造
  -- 设 DFA1 = (Q₁, Σ, δ₁, q₀₁, F₁)，DFA2 = (Q₂, Σ, δ₂, q₀₂, F₂)
  -- 构造 DFA = (Q₁ × Q₂, Σ, δ, (q₀₁, q₀₂), F)
  -- 其中 δ((q₁, q₂), a) = (δ₁(q₁, a), δ₂(q₂, a))
  -- F = {(q₁, q₂) | q₁ ∈ F₁ ∨ q₂ ∈ F₂}
  sorry

/-- 正则语言的交封闭性（陈述）
  定理：若 L₁ 和 L₂ 是正则语言，则 L₁ ∩ L₂ 也是正则语言
-/
theorem regular_intersection {A : Type} (L1 L2 : List A → Bool)
    (h1 : IsRegularLanguage L1) (h2 : IsRegularLanguage L2) :
    IsRegularLanguage (λ w => L1 w && L2 w) := by
  -- 证明：乘积构造，接受状态 F = F₁ × F₂
  sorry

/-- 正则语言的补封闭性（陈述）
  定理：若 L 是正则语言，则 L̄ = Σ* \ L 也是正则语言
-/
theorem regular_complement {A : Type} (L : List A → Bool)
    (h : IsRegularLanguage L) :
    IsRegularLanguage (λ w => !L w) := by
  -- 证明：交换接受状态与非接受状态
  sorry

-- ============================================
-- 第五部分：Myhill-Nerode定理
-- ============================================

/-- 右不变等价关系定义 -/
def RightInvariant {A : Type} (R : (List A → Bool) → (List A → Bool) → Prop) : Prop :=
  ∀ (x y : List A → Bool) (a : A),
    R x y → R (λ w => x (a :: w)) (λ w => y (a :: w))

/-- 不可区分关系 ≡_L 的形式化
  x ≡_L y 当且仅当 ∀z, xz ∈ L ↔ yz ∈ L
-/
def Indistinguishable {A : Type} (L : List A → Bool) 
    (x y : List A) : Prop :=
  ∀ (z : List A), L (x ++ z) = L (y ++ z)

/-- Myhill-Nerode定理（陈述）
  定理：语言 L 是正则的当且仅当 ≡_L 有有限指数
  （即等价类数量有限）
-/
theorem myhill_nerode {A : Type} (L : List A → Bool) :
  IsRegularLanguage L ↔ 
  ∃ (n : Nat), ∀ (w : List A), 
    (List.filter (λ x => Indistinguishable L x w) (allStringsUpTo n)).length ≤ n := by
  -- 证明分为两个方向：
  -- (⇒) 若 L 被 DFA M 接受，则 x ≡_L y 当且仅当 δ̂(q₀, x) = δ̂(q₀, y)
  --     DFA 状态有限，故等价类有限
  -- (⇐) 若 ≡_L 有有限指数，构造DFA：
  --     状态为等价类，转移为 [x] --a--> [xa]
  sorry

-- 辅助函数：生成长度不超过n的所有字符串
private def allStringsUpTo {A : Type} (n : Nat) : List (List A) :=
  [[]]  -- 简化实现，实际需要生成所有组合

-- ============================================
-- 第六部分：具体示例
-- ============================================

/-- 示例：识别偶数个1的DFA
  状态：
  - q0: 偶数个1（接受状态）
  - q1: 奇数个1
-/
def evenOnesDFA : DFA Bool Bool :=
  let states := [false, true]  -- false=q0, true=q1
  let alphabet := [false, true]  -- false=0, true=1
  let transition := λ (state : Bool) (input : Bool) =>
    if input then !state else state  -- 读1翻转状态，读0保持
  let startState := false  -- 从偶数开始（0个1）
  let acceptStates := [false]  -- q0是接受状态
  
  DFA.mk states alphabet transition startState acceptStates

/-- 验证偶数个1DFA的正确性（测试） -/
example : evenOnesDFA.accepts [true, true] = true := by
  rfl  -- 11有偶数个1，应该接受

example : evenOnesDFA.accepts [true, true, true] = false := by
  rfl  -- 111有奇数个1，应该拒绝

example : evenOnesDFA.accepts [] = true := by
  rfl  -- 空串（0个1，偶数），应该接受

end FiniteAutomaton
