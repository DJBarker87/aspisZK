import NNH_Tx2LiteralSlots
set_option autoImplicit false
namespace AspisR1.NNH_CommonOffsets
open Aeneas Aeneas.Std Result
/-- Small generated offset arithmetic only; no recurrence/buffer reduction. -/
theorem values :
 NHT_Constants.compact.OFF_ROUND1 = (.ok 7783#usize : Result Usize) ∧
 NHT_Constants.compact.OFF_FOLDED_ROOT = (.ok 7751#usize : Result Usize) ∧
 NHT_Constants.compact.OFF_OPENINGS = (.ok 10055#usize : Result Usize) ∧
 NHT_Constants.compact.OFF_FINAL = (.ok 8007#usize : Result Usize) ∧
 NHT_Constants.compact.OFF_ROUND0 = (.ok 7527#usize : Result Usize) ∧
 NHT_Constants.compact.OFF_INACTIVE = (.ok 7495#usize : Result Usize) := by
 refine ⟨?_,?_,?_,?_,?_,?_⟩
 all_goals with_unfolding_all rfl
#print axioms values
end AspisR1.NNH_CommonOffsets
