/-
# 有限自动机形式化 (Finite Automaton Formalization)

本文件包含确定性有限自动机(DFA)和非确定性有限自动机(NFA)的形式化定义，
以及它们之间等价性的形式化证明框架。

更新日志 (2026-04-14):
- 修复了 toDFA 和 epsilonClosure 的定义（使用 fuel 参数保证终止性）
- 添加了 DFA/NFA 的良构性(well-formedness)定义
- 完成了正则语言并、交、补封闭性的完整证明
- 为 NFA-DFA 等价性和 Myhill-Nerode 定理提供了结构化证明框架

参考文档: docs/Refactor/02_形式语言/01_形式语言基础/01.2_有限自动机.md
-/

namespace FiniteAutomaton

-- ============================================
-- 第一部分：确定性有限自动机 (DFA)
-- ============================================

/-- DFA的五元组定义：M = (Q, Σ, δ, q₀, F) -/
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

/-- 检查状态是否在DFA的状态集合中 -/
def DFA.isValidState {S A : Type} [BEq S] (dfa : DFA S A) (s : S) : Bool :=
  dfa.states.contains s

/-- 检查字母是否在DFA的字母表中 -/
def DFA.isValidSymbol {S A : Type} [BEq A] (dfa : DFA S A) (a : A) : Bool :=
  dfa.alphabet.contains a

/-- DFA良构性：初始状态在状态集合中，且转移不离开状态集合 -/
def DFA.WellFormed {S A : Type} [BEq S] (dfa : DFA S A) : Prop :=
  dfa.states.contains dfa.startState ∧
  ∀ (s : S), dfa.states.contains s → ∀ (a : A),
    dfa.states.contains (dfa.transition s a)

/-- 扩展转移函数 δ̂: Q × Σ* → Q -/
def DFA.deltaHat {S A : Type} (dfa : DFA S A) (q : S) (w : List A) : S :=
  w.foldl (λ currentState symbol => dfa.transition currentState symbol) q

/-- DFA接受的语言：L(M) = {w | δ̂(q₀, w) ∈ F} -/
def DFA.accepts {S A : Type} [BEq S] (dfa : DFA S A) (w : List A) : Bool :=
  let finalState := dfa.deltaHat dfa.startState w
  dfa.acceptStates.contains finalState

-- 辅助引理：deltaHat保持状态集合成员关系
theorem DFA.deltaHat_preserves_states {S A : Type} [BEq S] (dfa : DFA S A)
    (hw : dfa.WellFormed) (q : S) (hq : dfa.states.contains q) (w : List A) :
    dfa.states.contains (dfa.deltaHat q w) := by
  induction w generalizing q with
  | nil => simp [DFA.deltaHat]; exact hq
  | cons a w ih =>
    simp [DFA.deltaHat]
    exact ih (dfa.transition q a) (hw.right q hq a)

-- ============================================
-- 第二部分：非确定性有限自动机 (NFA)
-- ============================================

/-- NFA的五元组定义：N = (Q, Σ, δ, q₀, F) -/
structure NFA (State Alphabet : Type) where
  /-- 状态集合 Q -/
  states : List State
  /-- 输入字母表 Σ -/
  alphabet : List Alphabet
  /-- 转移函数 δ: Q × (Σ ∪ {ε}) → P(Q) -/
  transition : State → Option Alphabet → List State
  /-- 初始状态 q₀ -/
  startState : State
  /-- 接受状态集合 F ⊆ Q -/
  acceptStates : List State

/-- NFA良构性：初始状态在状态集合中，且转移不离开状态集合 -/
def NFA.WellFormed {S A : Type} [BEq S] (nfa : NFA S A) : Prop :=
  nfa.states.contains nfa.startState ∧
  ∀ (s : S), nfa.states.contains s → ∀ (a : Option A),
    (nfa.transition s a).all (λ s' => nfa.states.contains s')

/-- NFA的ε-闭包：使用 fuel 参数保证终止性 -/
def NFA.epsilonClosure {S A : Type} [BEq S] (nfa : NFA S A) (states : List S) : List S :=
  let rec closureAux (fuel : Nat) (current : List S) (visited : List S) : List S :=
    match fuel with
    | 0 => visited
    | fuel + 1 =>
      match current with
      | [] => visited
      | s :: rest =>
        if visited.contains s then
          closureAux fuel rest visited
        else
          let epsilonStates := nfa.transition s none
          let newStates := epsilonStates.filter (λ x => !visited.contains x && !current.contains x)
          closureAux fuel (rest ++ newStates) (s :: visited)
  closureAux (nfa.states.length + states.length + 1) states []

/-- NFA的单步转移（含ε闭包） -/
def NFA.move {S A : Type} [BEq S] (nfa : NFA S A) (states : List S) (a : A) : List S :=
  let newStates := states.flatMap (λ s => nfa.transition s (some a))
  nfa.epsilonClosure newStates

/-- NFA的扩展转移函数 δ̂ -/
def NFA.deltaHat {S A : Type} [BEq S] (nfa : NFA S A) (states : List S) (w : List A) : List S :=
  match w with
  | [] => states
  | a :: rest =>
    let newStates := nfa.move states a
    nfa.deltaHat newStates rest

/-- NFA接受的语言 -/
def NFA.accepts {S A : Type} [BEq S] (nfa : NFA S A) (w : List A) : Bool :=
  let startClosure := nfa.epsilonClosure [nfa.startState]
  let finalStates := nfa.deltaHat startClosure w
  finalStates.any (λ s => nfa.acceptStates.contains s)

-- ============================================
-- 第三部分：DFA与NFA的等价性
-- ============================================

/-- 计算列表的幂集 -/
def powerSet {α : Type} (l : List α) : List (List α) :=
  l.foldr (fun x acc => acc ++ acc.map (fun xs => x :: xs)) [[]]

/-- 子集构造：将NFA转换为DFA -/
def NFA.toDFA {S A : Type} [BEq S] [BEq A] (nfa : NFA S A) : DFA (List S) A :=
  let powerSetStates := powerSet nfa.states
  let dfaTransition := λ (states : List S) (a : A) => nfa.move states a
  let startState := nfa.epsilonClosure [nfa.startState]
  let acceptStates := powerSetStates.filter (λ ss => ss.any (λ s => nfa.acceptStates.contains s))
  DFA.mk powerSetStates nfa.alphabet dfaTransition startState acceptStates

-- 辅助引理：filter后的contains性质
theorem filter_contains {α : Type} [BEq α] [LawfulBEq α] (l : List α) (p : α → Bool) (x : α)
    (hx : l.contains x = true) :
    (l.filter p).contains x = p x := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    by_cases hxy : y == x
    · have hy : y = x := LawfulBEq.eq_of_beq hxy
      rw [hy]
      by_cases hp : p x
      · simp [hp]
      · simp [hp]
        have h1 : (ys.filter p).contains x = false := by
          induction ys with
          | nil => simp
          | cons z zs ih2 =>
            simp
            by_cases hz : z == x
            · simp [LawfulBEq.eq_of_beq hz, hp]
            · simp [hz, ih2]
        simp [h1]
    · have hx' : ys.contains x = true := by
        rw [show (y :: ys).contains x = (y == x) || ys.contains x by rfl] at hx
        simp [hxy] at hx
        exact hx
      rw [show (y :: ys).filter p = if p y then y :: ys.filter p else ys.filter p by rfl]
      simp [hxy]
      exact ih hx'

-- 幂集包含性引理（核心引理，证明较复杂，使用 sorry）
theorem powerSet_contains {α : Type} [BEq α] [LawfulBEq α] (l : List α) (sub : List α)
    (h : sub.all (λ x => l.contains x) = true) :
    (powerSet l).contains sub = true := by
  sorry

/-- DFA与NFA等价性定理（结构化证明框架） -/
theorem NFA_DFA_equivalence {S A : Type} [BEq S] [BEq A] [LawfulBEq S] (nfa : NFA S A)
    (hw : nfa.WellFormed) (w : List A) :
    nfa.accepts w = nfa.toDFA.accepts w := by
  have h_delta : ∀ (states : List S) (w : List A),
      (nfa.toDFA).deltaHat states w = nfa.deltaHat states w := by
    intro states w
    induction w generalizing states with
    | nil => simp [DFA.deltaHat, NFA.deltaHat]
    | cons a w ih =>
      simp [DFA.deltaHat, NFA.deltaHat]
      exact ih (nfa.move states a)
  have h_mem : (powerSet nfa.states).contains (nfa.deltaHat (nfa.epsilonClosure [nfa.startState]) w) = true := by
    apply powerSet_contains
    -- 良构NFA保证所有可达状态都是 nfa.states 的子集
    sorry
  have h1 : nfa.accepts w = (nfa.deltaHat (nfa.epsilonClosure [nfa.startState]) w).any (λ s => nfa.acceptStates.contains s) := rfl
  have h2 : nfa.toDFA.accepts w = nfa.toDFA.acceptStates.contains (nfa.toDFA.deltaHat nfa.toDFA.startState w) := rfl
  have h3 : nfa.toDFA.deltaHat nfa.toDFA.startState w = nfa.deltaHat (nfa.epsilonClosure [nfa.startState]) w := by
    apply h_delta
  rw [h1, h2, h3]
  have h4 : nfa.toDFA.acceptStates.contains (nfa.deltaHat (nfa.epsilonClosure [nfa.startState]) w)
      = (nfa.deltaHat (nfa.epsilonClosure [nfa.startState]) w).any (λ s => nfa.acceptStates.contains s) := by
    unfold NFA.toDFA
    rw [filter_contains (powerSet nfa.states) (λ ss => ss.any (λ s => nfa.acceptStates.contains s))
          (nfa.deltaHat (nfa.epsilonClosure [nfa.startState]) w) h_mem]
    simp
  exact h4

-- ============================================
-- 第四部分：正则语言的性质
-- ============================================

/-- 语言是正则的：存在良构DFA接受该语言 -/
def IsRegularLanguage {A : Type} (L : List A → Bool) : Prop :=
  ∃ (S : Type) (inst : LawfulBEq S) (dfa : DFA S A), dfa.WellFormed ∧ ∀ (w : List A), dfa.accepts w = L w

-- 辅助引理：flatMap-map的contains
theorem flatMap_map_contains_pair {α β : Type} [BEq α] [BEq β] [LawfulBEq α] [LawfulBEq β]
    (l1 : List α) (l2 : List β) (x : α) (y : β)
    (hx : l1.contains x = true) (hy : l2.contains y = true) :
    (l1.flatMap (fun a => l2.map (fun b => (a, b)))).contains (x, y) = true := by
  induction l1 with
  | nil => simp at hx
  | cons a as ih =>
    by_cases ha : a == x
    · simp [LawfulBEq.eq_of_beq ha]
      induction l2 with
      | nil => simp at hy
      | cons b bs ih2 =>
        by_cases hb : b == y
        · simp [LawfulBEq.eq_of_beq hb]
        · have hy' : bs.contains y = true := by
            rw [show (b :: bs).contains y = (b == y) || bs.contains y by rfl] at hy
            simp [hb] at hy
            exact hy
          rw [show (b :: bs).contains y = (b == y) || bs.contains y by rfl]
          simp [hb]
          exact ih2 hy'
    · have hx' : as.contains x = true := by
        rw [show (a :: as).contains x = (a == x) || as.contains x by rfl] at hx
        simp [ha] at hx
        exact hx
      rw [show (a :: as).flatMap (fun a => l2.map (fun b => (a, b))) = l2.map (fun b => (a, b)) ++ as.flatMap (fun a => l2.map (fun b => (a, b))) by rfl]
      simp [ha]
      exact ih hx'

-- foldl在乘积类型上的分解引理
theorem foldl_pair {α β γ : Type} (f1 : α → γ → α) (f2 : β → γ → β) (q1 : α) (q2 : β) (w : List γ) :
    List.foldl (λ (p : α × β) c => (f1 p.fst c, f2 p.snd c)) (q1, q2) w
    = (List.foldl f1 q1 w, List.foldl f2 q2 w) := by
  induction w generalizing q1 q2 with
  | nil => simp
  | cons a w ih =>
    simp
    exact ih (f1 q1 a) (f2 q2 a)

-- 乘积DFA的deltaHat等于各DFA deltaHat的乘积
theorem product_deltaHat {S1 S2 A : Type} [BEq S1] [BEq S2]
    (dfa1 : DFA S1 A) (dfa2 : DFA S2 A)
    (q1 : S1) (q2 : S2) (w : List A) :
    let prodDFA : DFA (S1 × S2) A := {
      states := dfa1.states.flatMap (fun s1 => dfa2.states.map (fun s2 => (s1, s2))),
      alphabet := dfa1.alphabet,
      transition := λ (s1, s2) a => (dfa1.transition s1 a, dfa2.transition s2 a),
      startState := (q1, q2),
      acceptStates := []
    }
    prodDFA.deltaHat (q1, q2) w = (dfa1.deltaHat q1 w, dfa2.deltaHat q2 w) := by
  simp [DFA.deltaHat]
  exact foldl_pair dfa1.transition dfa2.transition q1 q2 w

/-- 正则语言的并封闭性（完整证明） -/
theorem regular_union {A : Type} (L1 L2 : List A → Bool)
    (h1 : IsRegularLanguage L1) (h2 : IsRegularLanguage L2) :
    IsRegularLanguage (λ w => L1 w || L2 w) := by
  rcases h1 with ⟨S1, _, dfa1, hw1, hd1⟩
  rcases h2 with ⟨S2, _, dfa2, hw2, hd2⟩
  let prodStates := dfa1.states.flatMap (fun s1 => dfa2.states.map (fun s2 => (s1, s2)))
  let prodDFA : DFA (S1 × S2) A := {
    states := prodStates,
    alphabet := dfa1.alphabet,
    transition := λ (s1, s2) a => (dfa1.transition s1 a, dfa2.transition s2 a),
    startState := (dfa1.startState, dfa2.startState),
    acceptStates := prodStates.filter (λ (s1, s2) => dfa1.acceptStates.contains s1 || dfa2.acceptStates.contains s2)
  }
  use S1 × S2, inferInstance, prodDFA
  constructor
  · constructor
    · exact flatMap_map_contains_pair dfa1.states dfa2.states dfa1.startState dfa2.startState hw1.left hw2.left
    · intro s hs a
      exact flatMap_map_contains_pair dfa1.states dfa2.states s.fst s.snd
        (hw1.right s.fst (by simpa using hs) a) (hw2.right s.snd (by simpa using hs) a)
  · intro w
    have h1 := hd1 w
    have h2 := hd2 w
    have h3 : prodDFA.deltaHat prodDFA.startState w = (dfa1.deltaHat dfa1.startState w, dfa2.deltaHat dfa2.startState w) := by
      apply product_deltaHat
    simp [DFA.accepts, h3, h1, h2]
    have hq1 : dfa1.states.contains (dfa1.deltaHat dfa1.startState w) :=
      DFA.deltaHat_preserves_states dfa1 hw1 dfa1.startState hw1.left w
    have hq2 : dfa2.states.contains (dfa2.deltaHat dfa2.startState w) :=
      DFA.deltaHat_preserves_states dfa2 hw2 dfa2.startState hw2.left w
    have hmem : prodStates.contains (dfa1.deltaHat dfa1.startState w, dfa2.deltaHat dfa2.startState w) = true :=
      flatMap_map_contains_pair dfa1.states dfa2.states _ _ hq1 hq2
    rw [filter_contains prodStates (λ (s1, s2) => dfa1.acceptStates.contains s1 || dfa2.acceptStates.contains s2)
          (dfa1.deltaHat dfa1.startState w, dfa2.deltaHat dfa2.startState w) hmem]
    simp

/-- 正则语言的交封闭性（完整证明） -/
theorem regular_intersection {A : Type} (L1 L2 : List A → Bool)
    (h1 : IsRegularLanguage L1) (h2 : IsRegularLanguage L2) :
    IsRegularLanguage (λ w => L1 w && L2 w) := by
  rcases h1 with ⟨S1, _, dfa1, hw1, hd1⟩
  rcases h2 with ⟨S2, _, dfa2, hw2, hd2⟩
  let prodStates := dfa1.states.flatMap (fun s1 => dfa2.states.map (fun s2 => (s1, s2)))
  let prodDFA : DFA (S1 × S2) A := {
    states := prodStates,
    alphabet := dfa1.alphabet,
    transition := λ (s1, s2) a => (dfa1.transition s1 a, dfa2.transition s2 a),
    startState := (dfa1.startState, dfa2.startState),
    acceptStates := prodStates.filter (λ (s1, s2) => dfa1.acceptStates.contains s1 && dfa2.acceptStates.contains s2)
  }
  use S1 × S2, inferInstance, prodDFA
  constructor
  · constructor
    · exact flatMap_map_contains_pair dfa1.states dfa2.states dfa1.startState dfa2.startState hw1.left hw2.left
    · intro s hs a
      exact flatMap_map_contains_pair dfa1.states dfa2.states s.fst s.snd
        (hw1.right s.fst (by simpa using hs) a) (hw2.right s.snd (by simpa using hs) a)
  · intro w
    have h1 := hd1 w
    have h2 := hd2 w
    have h3 : prodDFA.deltaHat prodDFA.startState w = (dfa1.deltaHat dfa1.startState w, dfa2.deltaHat dfa2.startState w) := by
      apply product_deltaHat
    simp [DFA.accepts, h3, h1, h2]
    have hq1 : dfa1.states.contains (dfa1.deltaHat dfa1.startState w) :=
      DFA.deltaHat_preserves_states dfa1 hw1 dfa1.startState hw1.left w
    have hq2 : dfa2.states.contains (dfa2.deltaHat dfa2.startState w) :=
      DFA.deltaHat_preserves_states dfa2 hw2 dfa2.startState hw2.left w
    have hmem : prodStates.contains (dfa1.deltaHat dfa1.startState w, dfa2.deltaHat dfa2.startState w) = true :=
      flatMap_map_contains_pair dfa1.states dfa2.states _ _ hq1 hq2
    rw [filter_contains prodStates (λ (s1, s2) => dfa1.acceptStates.contains s1 && dfa2.acceptStates.contains s2)
          (dfa1.deltaHat dfa1.startState w, dfa2.deltaHat dfa2.startState w) hmem]
    simp

/-- 正则语言的补封闭性（完整证明） -/
theorem regular_complement {A : Type} (L : List A → Bool)
    (h : IsRegularLanguage L) :
    IsRegularLanguage (λ w => !L w) := by
  rcases h with ⟨S, _, dfa, hw, hd⟩
  let compDFA : DFA S A := {
    states := dfa.states,
    alphabet := dfa.alphabet,
    transition := dfa.transition,
    startState := dfa.startState,
    acceptStates := dfa.states.filter (λ s => !dfa.acceptStates.contains s)
  }
  use S, inferInstance, compDFA
  constructor
  · exact hw
  · intro w
    have h1 := hd w
    simp [DFA.accepts, h1]
    have hq : dfa.states.contains (dfa.deltaHat dfa.startState w) :=
      DFA.deltaHat_preserves_states dfa hw dfa.startState hw.left w
    rw [filter_contains dfa.states (λ s => !dfa.acceptStates.contains s) (dfa.deltaHat dfa.startState w) hq]
    simp

-- ============================================
-- 第五部分：Myhill-Nerode定理
-- ============================================

/-- 右不变等价关系定义 -/
def RightInvariant {A : Type} (R : (List A → Bool) → (List A → Bool) → Prop) : Prop :=
  ∀ (x y : List A → Bool) (a : A),
    R x y → R (λ w => x (a :: w)) (λ w => y (a :: w))

/-- 不可区分关系 ≡_L -/
def Indistinguishable {A : Type} (L : List A → Bool) (x y : List A) : Prop :=
  ∀ (z : List A), L (x ++ z) = L (y ++ z)

/-- Myhill-Nerode定理（正确陈述） -/
theorem myhill_nerode {A : Type} (L : List A → Bool) :
  IsRegularLanguage L ↔ 
  (∃ (n : Nat) (rep : Fin n → List A),
    ∀ (w : List A), ∃ (i : Fin n), Indistinguishable L w (rep i)) := by
  -- 证明框架：
  -- (⇒) 若 L 被 DFA M 接受，x ≡_L y ⇔ δ̂(q₀, x) = δ̂(q₀, y)。Q 有限故等价类有限。
  -- (⇐) 若 ≡_L 有有限指数，构造最小DFA：状态为等价类，转移 [x] --a--> [xa]。
  sorry

-- ============================================
-- 第六部分：具体示例
-- ============================================

/-- 识别偶数个1的DFA -/
def evenOnesDFA : DFA Bool Bool :=
  let states := [false, true]
  let alphabet := [false, true]
  let transition := λ (state : Bool) (input : Bool) => if input then !state else state
  let startState := false
  let acceptStates := [false]
  DFA.mk states alphabet transition startState acceptStates

example : evenOnesDFA.accepts [true, true] = true := by
  native_decide

example : evenOnesDFA.accepts [true, true, true] = false := by
  native_decide

example : evenOnesDFA.accepts [] = true := by
  native_decide

end FiniteAutomaton
