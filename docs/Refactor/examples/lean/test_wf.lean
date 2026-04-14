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
