import NCJ_GuardExact
import NDD_GuardModel
set_option autoImplicit false
noncomputable section
namespace NDL_GuardAssociation
open Aeneas Aeneas.Std Result FIo_Native
attribute [local instance] Classical.propDecidable
/-- The SAME complete record supplies every native-contract comparison.
No comparison success, equality result, or independent row is a premise. -/
theorem cohort (w : weights.Weights) (folds : Usize) :
    NDD_Reference.guard_ref (decide (w.variant = .S2)) folds
      (decide (NCJ_GuardExact.row w 0 2 = NCJ_GuardExact.row w 2 2))
      (decide (NCJ_GuardExact.row w 0 3 = NCJ_GuardExact.row w 2 3)) =
      weights.shared_two_point_guard w folds := by
  rw [NCJ_GuardExact.source]
  simp only [NDD_Reference.guard_ref, NCJ_GuardExact.guard]
  split <;> split <;> simp_all
/-- The native Bool cut inputs are the cohort's actual equality outputs
for the exact two rows; the emitted equality is total on arbitrary words. -/
theorem first_comparison (w : weights.Weights) :
    core.array.equality.PartialEqArray.eq
      aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
      (NCJ_GuardExact.row w 0 2) (NCJ_GuardExact.row w 2 2) =
      ok (decide (NCJ_GuardExact.row w 0 2 = NCJ_GuardExact.row w 2 2)) :=
  NCJ_QEquality.arrays _ _
theorem second_comparison (w : weights.Weights) :
    core.array.equality.PartialEqArray.eq
      aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
      (NCJ_GuardExact.row w 0 3) (NCJ_GuardExact.row w 2 3) =
      ok (decide (NCJ_GuardExact.row w 0 3 = NCJ_GuardExact.row w 2 3)) :=
  NCJ_QEquality.arrays _ _
#print axioms cohort
#print axioms first_comparison
#print axioms second_comparison
end NDL_GuardAssociation
end
