import R1Z.BuilderBankExtracted
import R0Z.WriterRefineMerge

/-! Symbolic refinement of the extracted row and block dispatch predicates.
No enumeration of concrete bank cells or Poseidon rounds. -/
set_option autoImplicit false
namespace R1Z.BuilderBankShape
open Aeneas Aeneas.Std Result

theorem range_usize (r : core.ops.range.Range Std.Usize) (x : Std.Usize) :
    BuilderStdModels.rangeContains core.cmp.PartialOrdUsize
      core.cmp.PartialOrdUsize core.cmp.PartialOrdUsize r x =
      ok (decide (r.start.val ≤ x.val ∧ x.val < r.end.val)) := by
  change (do
    let b ← ok (decide (r.start.val ≤ x.val))
    if b then ok (decide (x.val < r.end.val)) else ok false) = _
  by_cases h : r.start.val ≤ x.val <;> simp [h]

theorem inclusive_usize (r : core.ops.range.RangeInclusive Std.Usize)
    (x : Std.Usize) (he : r.exhausted = false) :
    BuilderStdModels.rangeInclusiveContains core.cmp.PartialOrdUsize
      core.cmp.PartialOrdUsize core.cmp.PartialOrdUsize r x =
      ok (decide (r.start.val ≤ x.val ∧ x.val ≤ r.end.val)) := by
  unfold BuilderStdModels.rangeInclusiveContains
  rw [he]
  change (do
    let b ← ok (decide (r.start.val ≤ x.val))
    if b then ok (decide (x.val ≤ r.end.val)) else ok false) = _
  by_cases h : r.start.val ≤ x.val <;> simp [h]

theorem late_row (k : Std.Usize) :
    AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.late_row k = ok (decide (R0Z.WriterRefine.LateRow k.val)) := by
  obtain ⟨r, hr, hv⟩ := R0Z.WriterRefine.rem1024 k
  rw [AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.late_row, hr]
  simp only [bind_tc_ok]
  simp only [AspisBuilderGlueSource.core.ops.range.Range.contains]
  rw [range_usize]
  simp [hv, R0Z.WriterRefine.LateRow]

theorem node_kind (h : Std.Usize) :
    AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.node_kind h = ok (decide ((4 ≤ h.val ∧ h.val ≤ 24) ∨
      (33 ≤ h.val ∧ h.val ≤ 56))) := by
  rw [AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.node_kind]
  simp only [core.ops.range.RangeInclusive.new, bind_tc_ok]
  simp only [AspisBuilderGlueSource.core.ops.range.RangeInclusive.contains]
  rw [inclusive_usize _ _ rfl]
  simp only [bind_tc_ok]
  split
  · rename_i ht
    simp_all
  · rw [inclusive_usize _ _ rfl]
    simp_all

theorem zero_kind (p : AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.RP) (h : Std.Usize) :
    AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.zero_kind p h = ok (decide (p.transfer = false ∧ 27 ≤ h.val ∧ h.val ≤ 29)) := by
  rw [AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.zero_kind]
  cases he : p.transfer <;> simp only [he, Bool.false_eq_true, if_false, if_true]
  · simp only [core.ops.range.RangeInclusive.new, bind_tc_ok]
    simp only [AspisBuilderGlueSource.core.ops.range.RangeInclusive.contains]
    rw [inclusive_usize _ _ rfl]
    simp
  · simp

#print axioms range_usize
#print axioms inclusive_usize
#print axioms late_row
#print axioms node_kind
#print axioms zero_kind
end R1Z.BuilderBankShape
