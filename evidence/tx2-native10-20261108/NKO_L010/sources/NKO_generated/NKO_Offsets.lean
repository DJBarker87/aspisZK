import NKE_CommonCalls
set_option autoImplicit false
namespace NKO_Offsets
open Aeneas Aeneas.Std Result
theorem inactive : NHT_Constants.compact.OFF_INACTIVE=ok 7495#usize := by rfl
theorem round0 : NHT_Constants.compact.OFF_ROUND0=ok 7527#usize := by rfl
theorem folded : NHT_Constants.compact.OFF_FOLDED_ROOT=ok 7751#usize := by rfl
theorem round1 : NHT_Constants.compact.OFF_ROUND1=ok 7783#usize := by rfl
theorem final_message : NHT_Constants.compact.OFF_FINAL=ok 8007#usize := by rfl
theorem openings : NHT_Constants.compact.OFF_OPENINGS=ok 10055#usize := by rfl
#print axioms inactive
#print axioms round0
#print axioms folded
#print axioms round1
#print axioms final_message
#print axioms openings
end NKO_Offsets
