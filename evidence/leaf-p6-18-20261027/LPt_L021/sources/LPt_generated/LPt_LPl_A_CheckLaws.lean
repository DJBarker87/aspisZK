import LPt_LPl_A_Check
import LPt_LPl_A_StageLaws
open Aeneas Aeneas.Std Result
open LPt_LPl_Kit_Release
set_option autoImplicit false
namespace LPt_LPl_A.Check

theorem accepts_iff (bs : Slice U8) :
    LPt_External.compact.check_values bs = ok (.Ok ()) ↔
      ∀ i, i < bs.val.length/16 → predicate bs.val i = true := by
  rw [shipped_leaf_model]
  simp only [loop, LPt_LPl_A.stages_all, List.all_eq_true, List.mem_range]
  split <;> simp_all

theorem rejects_of_bad_stage (bs : Slice U8) (i : Nat)
    (bound : i < bs.val.length/16) (bad : predicate bs.val i = false) :
    LPt_External.compact.check_values bs = ok (.Err .NonCanonical) := by
  have failed : loop bs.val = false := by
    rw [loop, LPt_LPl_A.stages_all, List.all_eq_false]
    exact ⟨i,List.mem_range.mpr bound,by simp only [bad, Bool.false_eq_true, not_false_eq_true]⟩
  rw [shipped_leaf_model, failed]
  rfl

#print axioms accepts_iff
#print axioms rejects_of_bad_stage
end LPt_LPl_A.Check
