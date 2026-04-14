/-
文件: Theorem31_TwoPhaseCommit.lean
标题: 两阶段提交的原子性证明
描述: 证明两阶段提交协议的原子性性质
作者: FormalScience项目
日期: 2026-04-12

证明思路:
1. 定义两阶段提交协议
2. 证明提交的原子性（全有或全无）
3. 证明一致的决定
4. 给出应用示例

关键引理:
- two_phase_commit_protocol: 2PC协议定义
- atomicity_property: 原子性性质
- uniform_decision: 一致决定
-/

import Mathlib

namespace TwoPhaseCommit

-- ============================================
-- 第一部分：2PC参与者
-- ============================================

/-- 参与者状态 -/
inductive ParticipantState
  | init          -- 初始状态
  | ready         -- 准备就绪（Phase 1）
  | committed     -- 已提交
  | aborted       -- 已中止
  deriving DecidableEq, Repr

/-- 参与者 -/
structure Participant where
  id : ℕ
  state : ParticipantState
  vote : Option Bool  -- true=同意, false=反对

deriving Repr

-- ============================================
-- 第二部分：协调者
-- ============================================

/-- 协调者状态 -/
inductive CoordinatorState
  | collecting    -- 收集投票中
  | deciding      -- 做出决定
  | finished      -- 完成
  deriving Repr

/-- 协调者 -/
structure Coordinator where
  state : CoordinatorState
  decision : Option Bool  -- true=提交, false=中止

-- ============================================
-- 第三部分：2PC协议
-- ============================================

/-- Phase 1: 投票阶段 -/
def phase1_vote (participants : List Participant) : List Participant :=
  -- 每个参与者做出本地决定并投票
  participants.map (fun p => {p with state := ParticipantState.ready, vote := some true})

/-- Phase 2: 提交/中止阶段 -/
def phase2_decide (coordinator : Coordinator) 
    (participants : List Participant) : 
    Coordinator × List Participant :=
  -- 协调者根据投票做出决定
  let all_yes := participants.all (fun p => p.vote = some true)
  if all_yes then
    -- 所有参与者同意，提交
    let new_coord := {state := CoordinatorState.finished, decision := some true}
    let new_parts := participants.map (fun p => 
      {p with state := ParticipantState.committed})
    (new_coord, new_parts)
  else
    -- 至少一个参与者反对，中止
    let new_coord := {state := CoordinatorState.finished, decision := some false}
    let new_parts := participants.map (fun p => 
      {p with state := ParticipantState.aborted})
    (new_coord, new_parts)

-- ============================================
-- 第四部分：原子性证明
-- ============================================

/-- 原子性：所有参与者最终状态相同（全提交或全中止） -/
def atomicity (participants : List Participant) : Prop :=
  (∀ p ∈ participants, p.state = ParticipantState.committed) ∨
  (∀ p ∈ participants, p.state = ParticipantState.aborted)

/-- 两阶段提交原子性定理 -/
theorem two_phase_commit_atomicity (coordinator : Coordinator)
    (participants : List Participant) :
  atomicity (phase2_decide coordinator participants).2 := by
  simp [atomicity, phase2_decide]
  split_ifs with h
  · left
    intro p hp
    simp at hp ⊢
    rcases hp with ⟨q, hq, rfl⟩
    simp
  · right
    intro p hp
    simp at hp ⊢
    rcases hp with ⟨q, hq, rfl⟩
    simp

/-- 一致的决定：所有参与者达成相同的决定 -/
def uniform_decision (coordinator : Coordinator)
    (participants : List Participant) : Prop :=
  coordinator.decision = some true → 
    ∀ p ∈ participants, p.state = ParticipantState.committed
  ∧ coordinator.decision = some false → 
    ∀ p ∈ participants, p.state = ParticipantState.aborted

/-- 一致决定定理 -/
theorem two_phase_commit_uniform (coordinator : Coordinator)
    (participants : List Participant) :
  uniform_decision (phase2_decide coordinator participants).1 (phase2_decide coordinator participants).2 := by
  simp [uniform_decision, phase2_decide]
  split_ifs with h
  · simp
  · simp

-- ============================================
-- 第五部分：应用示例
-- ============================================

/-- 2PC成功提交示例 -/
example :
  let participants : List Participant := [
    {id := 1, state := ParticipantState.init, vote := none},
    {id := 2, state := ParticipantState.init, vote := none},
    {id := 3, state := ParticipantState.init, vote := none}
  ]
  let voted := phase1_vote participants
  let coordinator := {state := CoordinatorState.collecting, decision := none}
  let (final_coord, final_parts) := phase2_decide coordinator voted
  -- 所有参与者同意，最终都提交
  final_coord.decision = some true ∧
  ∀ p ∈ final_parts, p.state = ParticipantState.committed := by
  simp [phase1_vote, phase2_decide]

end TwoPhaseCommit
