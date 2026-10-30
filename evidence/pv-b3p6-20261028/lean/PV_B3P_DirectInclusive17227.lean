import PV_B3P_DirectRange17227
namespace PV_B3P_Direct17227
open Aeneas Aeneas.Std Result
set_option autoImplicit false

theorem inclusive_next_extraction17 (r : core.ops.range.RangeInclusive Usize) :
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      core.iter.range.StepUsize r =
    if r.exhausted ∨ r.«end».val < r.start.val then .ok (none,r)
    else if r.start.val < r.«end».val then
      .ok (some r.start,{ start := Usize.wrapping_add r.start 1#usize,
        «end» := r.«end», exhausted := false })
    else .ok (some r.start,{ start := r.start, «end» := r.«end», exhausted := true }) := by
  obtain ⟨⟨item, rest⟩, execution, shape⟩ := WP.spec_imp_exists
    (core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next_Usize_spec r)
  by_cases empty : r.exhausted ∨ r.«end».val < r.start.val
  · simp only [empty,if_true] at shape ⊢
    rw [execution,shape.1,shape.2]
  · simp only [empty,if_false] at shape ⊢
    by_cases advance : r.start.val < r.«end».val
    · simp only [advance,if_true] at shape ⊢
      have inside : r.start < r.«end» := by scalar_tac
      have inc := PV_B3P_Offset226V3.add_value r.start 1#usize
        (PV_B3P_Binding13227.range_increment_safe13 r.start r.«end» inside)
      have same_start : rest.start = Usize.wrapping_add r.start 1#usize := by scalar_tac
      have same : rest = { start := Usize.wrapping_add r.start 1#usize,
          «end» := r.«end», exhausted := false } := by
        cases rest
        simp_all
      rw [execution,shape.1,same]
    · simp only [advance,if_false] at shape ⊢
      have same : rest = { start := r.start, «end» := r.«end», exhausted := true } := by
        cases rest
        simp_all
      rw [execution,shape.1,same]
#print axioms inclusive_next_extraction17
end PV_B3P_Direct17227
