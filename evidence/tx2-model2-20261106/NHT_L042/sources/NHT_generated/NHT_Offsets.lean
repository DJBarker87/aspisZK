import NHT_Constants
set_option autoImplicit false
namespace NHT_Offsets
open Aeneas Aeneas.Std Result
/-- These are small straight-line source expressions (no recurrence or enumeration). -/
theorem split : NHT_Constants.compact.SPLIT=10#usize := rfl
theorem semantic : NHT_Constants.verifier.SEMANTIC_BYTES=ok 13831#usize := by rfl
theorem compact_semantic : NHT_Constants.compact.COMPACT_SEMANTIC=ok 7015#usize := by rfl
theorem inactive : NHT_Constants.compact.OFF_INACTIVE=ok 7495#usize := by rfl
theorem round0 : NHT_Constants.compact.OFF_ROUND0=ok 7527#usize := by rfl
theorem folded : NHT_Constants.compact.OFF_FOLDED_ROOT=ok 7751#usize := by rfl
theorem round1 : NHT_Constants.compact.OFF_ROUND1=ok 7783#usize := by rfl
theorem final : NHT_Constants.compact.OFF_FINAL=ok 8007#usize := by rfl
theorem openings : NHT_Constants.compact.OFF_OPENINGS=ok 10055#usize := by rfl
#print axioms split
#print axioms semantic
#print axioms compact_semantic
#print axioms inactive
#print axioms round0
#print axioms folded
#print axioms round1
#print axioms final
#print axioms openings
end NHT_Offsets
