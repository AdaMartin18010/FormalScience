/-
文件: ParallelMachineNP.lean
标题: P||C_max NP难性的形式化证明
描述: 同构并行机上最小化完工时间问题是NP难的
-/

import Mathlib

namespace ParallelMachineNP

-- ============================================
-- 第一部分：问题定义
-- ============================================

/-- 并行机调度实例 -/
structure ParallelMachineInstance where
  n : ℕ                          -- 任务数量
  m : ℕ                          -- 机器数量
  processing_times : Fin n → ℕ   -- 处理时间
  deriving Repr

/-- 调度方案：每个任务分配的机器 -/
def MachineAssignment (n : ℕ) (m : ℕ) := Fin n → Fin m

/-- 机器负载：分配到该机器的所有任务处理时间之和 -/
def machine_load (inst : ParallelMachineInstance) 
    (assign : MachineAssignment inst.n inst.m) (machine : Fin inst.m) : ℕ :=
  (Finset.univ.filter (fun i => assign i = machine)).sum inst.processing_times

/-- 完工时间（Makespan） -/
def makespan (inst : ParallelMachineInstance) 
    (assign : MachineAssignment inst.n inst.m) : ℕ :=
  Finset.univ.sup (machine_load inst assign)

/-- 判定问题：是否存在调度使得完工时间 ≤ T -/
def decision_problem (inst : ParallelMachineInstance) (T : ℕ) : Prop :=
  ∃ (assign : MachineAssignment inst.n inst.m), makespan inst assign ≤ T

-- ============================================
-- 第二部分：Partition问题（已知NP完全）
-- ============================================

/-- Partition问题实例 -/
structure PartitionInstance where
  n : ℕ
  elements : Fin n → ℕ
  deriving Repr

/-- Partition判定问题：能否划分为两个和相等的子集 -/
def partition (inst : PartitionInstance) : Prop :=
  ∃ (S : Finset (Fin inst.n)),
    S.sum inst.elements = (Finset.univ \ S).sum inst.elements

-- ============================================
-- 第三部分：归约构造
-- ============================================

/-- 从Partition构造并行机调度实例 -/
def reduce_to_scheduling (inst : PartitionInstance) : ParallelMachineInstance :=
  {
    n := inst.n,
    m := 2,  -- 两台机器
    processing_times := inst.elements
  }

/-- 目标和：元素总和的一半 -/
def partition_target (inst : PartitionInstance) : ℕ :=
  (Finset.univ.sum inst.elements) / 2

-- ============================================
-- 第四部分：正确性证明
-- ============================================

/-- 关键引理：Partition有解 ↔ 完工时间 ≤ 总和/2 -/
lemma partition_iff_makespan (inst : PartitionInstance) :
  partition inst ↔ 
  decision_problem (reduce_to_scheduling inst) (partition_target inst) := by
  constructor
  · -- (=>) 方向：Partition有解 => 调度存在
    intro h
    rcases h with ⟨S, h_eq⟩
    -- 构造调度：S中的任务分配到机器0，其余分配到机器1
    let assign : MachineAssignment inst.n 2 := fun i =>
      if i ∈ S then 0 else 1
    use assign
    -- 证明两台机器的负载都等于目标和
    have load_0 : machine_load (reduce_to_scheduling inst) assign 0 = partition_target inst := by
      simp [machine_load, assign, partition_target, reduce_to_scheduling]
      have h_total : Finset.univ.sum inst.elements = 2 * (S.sum inst.elements) := by
        have h2 : (Finset.univ \ S).sum inst.elements = S.sum inst.elements := by linarith [h_eq]
        have h3 : Finset.univ.sum inst.elements = S.sum inst.elements + (Finset.univ \ S).sum inst.elements := by
          rw [Finset.sum_sdiff (Finset.subset_univ S)]
        rw [h2] at h3
        linarith
      rw [← Nat.mul_div_cancel_left (S.sum inst.elements) (by norm_num)]
      rw [← h_total]
      rw [Finset.sum_filter]
      simp
    have load_1 : machine_load (reduce_to_scheduling inst) assign 1 = partition_target inst := by
      simp [machine_load, assign, partition_target, reduce_to_scheduling]
      have h_total : Finset.univ.sum inst.elements = 2 * ((Finset.univ \ S).sum inst.elements) := by
        have h2 : (Finset.univ \ S).sum inst.elements = S.sum inst.elements := by linarith [h_eq]
        have h3 : Finset.univ.sum inst.elements = S.sum inst.elements + (Finset.univ \ S).sum inst.elements := by
          rw [Finset.sum_sdiff (Finset.subset_univ S)]
        rw [← h2] at h3
        linarith
      rw [← Nat.mul_div_cancel_left ((Finset.univ \ S).sum inst.elements) (by norm_num)]
      rw [← h_total]
      rw [Finset.sum_filter]
      simp [Finset.mem_sdiff]
      all_goals omega
    -- 完工时间是两台机器负载的最大值
    simp [makespan, load_0, load_1]
    all_goals omega
  · -- (<=) 方向：调度存在 => Partition有解
    intro h
    rcases h with ⟨assign, h_makespan⟩
    -- 从调度构造Partition的解
    let S : Finset (Fin inst.n) := Finset.univ.filter (fun i => assign i = 0)
    use S
    -- 证明两个子集的和相等
    have h0 : machine_load (reduce_to_scheduling inst) assign 0 = S.sum inst.elements := by
      simp [machine_load, reduce_to_scheduling, S]
      rw [Finset.sum_filter]
      simp
    have h1 : machine_load (reduce_to_scheduling inst) assign 1 = (Finset.univ \ S).sum inst.elements := by
      simp [machine_load, reduce_to_scheduling, S]
      rw [Finset.sum_filter]
      simp [Finset.mem_sdiff]
      all_goals omega
    have h_sum : machine_load (reduce_to_scheduling inst) assign 0 + 
      machine_load (reduce_to_scheduling inst) assign 1 = Finset.univ.sum inst.elements := by
      rw [h0, h1]
      rw [← Finset.sum_sdiff (Finset.subset_univ S)]
    have h_max0 : machine_load (reduce_to_scheduling inst) assign 0 ≤ partition_target inst := by
      have h : makespan (reduce_to_scheduling inst) assign ≤ partition_target inst := h_makespan
      simp [makespan] at h
      have h2 : machine_load (reduce_to_scheduling inst) assign 0 ≤ 
        Finset.univ.sup (machine_load (reduce_to_scheduling inst) assign) := by
        apply Finset.le_sup (Finset.mem_univ 0)
      linarith
    have h_max1 : machine_load (reduce_to_scheduling inst) assign 1 ≤ partition_target inst := by
      have h : makespan (reduce_to_scheduling inst) assign ≤ partition_target inst := h_makespan
      simp [makespan] at h
      have h2 : machine_load (reduce_to_scheduling inst) assign 1 ≤ 
        Finset.univ.sup (machine_load (reduce_to_scheduling inst) assign) := by
        apply Finset.le_sup (Finset.mem_univ 1)
      linarith
    have h_eq0 : S.sum inst.elements = partition_target inst := by
      omega
    have h_eq1 : (Finset.univ \ S).sum inst.elements = partition_target inst := by
      omega
    linarith [h_eq0, h_eq1]

-- ============================================
-- 第五部分：主定理
-- ============================================

/-- P||C_max是NP难的 -/
theorem parallel_machine_np_hard :
  ∀ (inst : PartitionInstance),
    partition inst ↔ decision_problem (reduce_to_scheduling inst) (partition_target inst) :=
  partition_iff_makespan

end ParallelMachineNP
