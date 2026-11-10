import NPH_R22Loops
import NHI_RangeProgress
import AspisR1Qm31SamplerIndex.Funs
import AspisR1Post25Sampler.Funs
import AspisR1SemanticCallExtraction.Funs
import S8OwnedP6.Funs
import FinishCandidateExplicitOps
import S1ValuesOwnedModelV1
import CurrentClaimDotModel
import S1ClaimBorrowedAbiNativeV1
import S1ClaimOwnedNestedModelV1

/-! NPH_ (R22 item 4, third batch): guarded-step lemmas for the remaining single-increment
bodies. Each body's only overflow-checked operation (body read, normalised hash in
NPH_R22_CONE.json) is one `x + 1#usize` under the body's own guard. For the three
range-iterator bodies the guard is the `some point` result of `IteratorRange.next`, and
`NHI_RangeProgress.some_next` (in the replayed closure) gives `point < iter.end`.
Standard axioms; no merged module is changed. -/
set_option autoImplicit false
namespace AspisR1.NPH_R22Loops3
open Aeneas Aeneas.Std Result AspisR1.NPH_R22Loops

abbrev Step (x : Usize) : Prop := ∃ z, (x + 1#usize : Result Usize) = ok z ∧ z.val = x.val + 1

theorem qm31_digits_loop1_body_step (i : Usize) (h : i < 4#usize) : Step i := usize_succ_ok i _ h
theorem low_base_p_digits_loop1_body_step (i : Usize) (h : i < 8#usize) : Step i := usize_succ_ok i _ h
theorem semantic_boundary_loop_body_step (index : Usize) (h : index < 28#usize) : Step index :=
  usize_succ_ok index _ h
theorem finish_owned_loop_body_step (weights : alloc.vec.Vec S8OwnedP6.aspis_core.field.QM31)
    (index : Usize) (h : index < alloc.vec.Vec.len weights) : Step index := usize_succ_ok index _ h
theorem finish_query_dot_loop_body_step (weights : Slice AspisR1FinishRelationCurrent.aspis_core.field.QM31)
    (j : Usize) (h : j < Slice.len weights) : Step j := usize_succ_ok j _ h
theorem values_owned_reference_loop_body_step (count chunk : Usize) (h : chunk < count) : Step chunk :=
  usize_succ_ok chunk _ h

/-- Generic: the `some point` produced by `IteratorRange.next` on a usize range has a safe successor. -/
theorem range_next_point_step (iter iter1 : core.ops.range.Range Usize) (point : Usize)
    (run : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = ok (some point, iter1)) :
    Step point := by
  obtain ⟨hp, _, _, hlt⟩ := NHI_RangeProgress.some_next iter iter1 point run
  subst hp
  exact usize_succ_ok _ iter.end hlt

theorem prepared_claim_loop_body_step (iter iter1 : core.ops.range.Range Usize) (point : Usize)
    (run : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = ok (some point, iter1)) :
    Step point := range_next_point_step iter iter1 point run
theorem borrowed_abi_owned_claim_loops_loop0_body_step (iter iter1 : core.ops.range.Range Usize) (point : Usize)
    (run : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = ok (some point, iter1)) :
    Step point := range_next_point_step iter iter1 point run
theorem owned_claim_loops_loop0_body_step (iter iter1 : core.ops.range.Range Usize) (point : Usize)
    (run : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = ok (some point, iter1)) :
    Step point := range_next_point_step iter iter1 point run

#print axioms qm31_digits_loop1_body_step
#print axioms low_base_p_digits_loop1_body_step
#print axioms semantic_boundary_loop_body_step
#print axioms finish_owned_loop_body_step
#print axioms finish_query_dot_loop_body_step
#print axioms values_owned_reference_loop_body_step
#print axioms range_next_point_step
#print axioms prepared_claim_loop_body_step
#print axioms borrowed_abi_owned_claim_loops_loop0_body_step
#print axioms owned_claim_loops_loop0_body_step
end AspisR1.NPH_R22Loops3
