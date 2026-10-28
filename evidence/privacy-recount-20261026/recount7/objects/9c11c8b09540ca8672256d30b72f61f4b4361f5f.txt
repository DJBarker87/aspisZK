import R1Z.PV_RunJoin_FixtureArguments
import R1Z.BuilderRecordsAdmission
import R1Z.PV_Src_NativeDirections

/-! Primitive admission of the concrete record arguments, independent of any
chosen compilation payload or installed Records implementation. -/
set_option autoImplicit false
namespace R1Z.PV_RunJoin_FixtureAdmission
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_RunJoin_FixtureArguments
abbrev input := PV_Src_NativeDirections.reference witness

theorem first : Canon8 input.pair.pair_leaf.first_commitment := by
  intro j hj
  interval_cases j <;> decide

theorem second : Canon8 input.pair.pair_leaf.second_commitment := by
  intro j hj
  interval_cases j <;> decide

theorem membership : ∀ l, l < 20 → Canon8 input.pair.membership.siblings.val[l]! := by
  intro l hl j hj
  interval_cases l <;> interval_cases j <;> decide

theorem superRoot : ∀ l, l < 3 → Canon8 input.super_root_siblings.val[l]! := by
  intro l hl j hj
  interval_cases l <;> interval_cases j <;> decide

theorem transfer_values : input.pair.value.val < 2^30 ∧
    (600#u32 : U32).val < 2^30 ∧ transferChange.value.val < 2^30 := by decide

theorem withdrawal_values : input.pair.value.val < 2^30 ∧
    (250#u32 : U32).val < 2^30 ∧ withdrawalChange.value.val < 2^30 := by decide

#print axioms first
#print axioms second
#print axioms membership
#print axioms superRoot
#print axioms transfer_values
#print axioms withdrawal_values
end R1Z.PV_RunJoin_FixtureAdmission
