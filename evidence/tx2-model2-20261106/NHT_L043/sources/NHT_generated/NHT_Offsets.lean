import NHT_Constants
set_option autoImplicit false
namespace NHT_Offsets
open Aeneas Aeneas.Std Result
/-- These are small straight-line source expressions (no recurrence or enumeration). -/
theorem split : NHT_Constants.compact.SPLIT=10#usize := by rw [NHT_Constants.compact.SPLIT]
theorem semantic : NHT_Constants.verifier.SEMANTIC_BYTES=ok 13831#usize := by
 simp only [NHT_Constants.compact.OFF_OPENINGS, NHT_Constants.compact.OFF_FINAL, NHT_Constants.compact.OFF_ROUND1, NHT_Constants.compact.OFF_FOLDED_ROOT, NHT_Constants.compact.OFF_ROUND0, NHT_Constants.compact.OFF_INACTIVE, NHT_Constants.compact.OFF_Y1, NHT_Constants.compact.COMPACT_Y1, NHT_Constants.compact.OFF_SEMANTIC, NHT_Constants.compact.HEADER, NHT_Constants.compact.COMPACT_SEMANTIC, NHT_Constants.compact.SEMANTIC_COMPACT_VALUES, NHT_Constants.compact.LOGICAL_SEMANTIC, NHT_Constants.verifier.SEMANTIC_BYTES, NHT_Constants.compact.FINAL_LEN]
 rfl
theorem compact_semantic : NHT_Constants.compact.COMPACT_SEMANTIC=ok 7015#usize := by
 simp only [NHT_Constants.compact.OFF_OPENINGS, NHT_Constants.compact.OFF_FINAL, NHT_Constants.compact.OFF_ROUND1, NHT_Constants.compact.OFF_FOLDED_ROOT, NHT_Constants.compact.OFF_ROUND0, NHT_Constants.compact.OFF_INACTIVE, NHT_Constants.compact.OFF_Y1, NHT_Constants.compact.COMPACT_Y1, NHT_Constants.compact.OFF_SEMANTIC, NHT_Constants.compact.HEADER, NHT_Constants.compact.COMPACT_SEMANTIC, NHT_Constants.compact.SEMANTIC_COMPACT_VALUES, NHT_Constants.compact.LOGICAL_SEMANTIC, NHT_Constants.verifier.SEMANTIC_BYTES, NHT_Constants.compact.FINAL_LEN]
 rfl
theorem inactive : NHT_Constants.compact.OFF_INACTIVE=ok 7495#usize := by
 simp only [NHT_Constants.compact.OFF_OPENINGS, NHT_Constants.compact.OFF_FINAL, NHT_Constants.compact.OFF_ROUND1, NHT_Constants.compact.OFF_FOLDED_ROOT, NHT_Constants.compact.OFF_ROUND0, NHT_Constants.compact.OFF_INACTIVE, NHT_Constants.compact.OFF_Y1, NHT_Constants.compact.COMPACT_Y1, NHT_Constants.compact.OFF_SEMANTIC, NHT_Constants.compact.HEADER, NHT_Constants.compact.COMPACT_SEMANTIC, NHT_Constants.compact.SEMANTIC_COMPACT_VALUES, NHT_Constants.compact.LOGICAL_SEMANTIC, NHT_Constants.verifier.SEMANTIC_BYTES, NHT_Constants.compact.FINAL_LEN]
 rfl
theorem round0 : NHT_Constants.compact.OFF_ROUND0=ok 7527#usize := by
 simp only [NHT_Constants.compact.OFF_OPENINGS, NHT_Constants.compact.OFF_FINAL, NHT_Constants.compact.OFF_ROUND1, NHT_Constants.compact.OFF_FOLDED_ROOT, NHT_Constants.compact.OFF_ROUND0, NHT_Constants.compact.OFF_INACTIVE, NHT_Constants.compact.OFF_Y1, NHT_Constants.compact.COMPACT_Y1, NHT_Constants.compact.OFF_SEMANTIC, NHT_Constants.compact.HEADER, NHT_Constants.compact.COMPACT_SEMANTIC, NHT_Constants.compact.SEMANTIC_COMPACT_VALUES, NHT_Constants.compact.LOGICAL_SEMANTIC, NHT_Constants.verifier.SEMANTIC_BYTES, NHT_Constants.compact.FINAL_LEN]
 rfl
theorem folded : NHT_Constants.compact.OFF_FOLDED_ROOT=ok 7751#usize := by
 simp only [NHT_Constants.compact.OFF_OPENINGS, NHT_Constants.compact.OFF_FINAL, NHT_Constants.compact.OFF_ROUND1, NHT_Constants.compact.OFF_FOLDED_ROOT, NHT_Constants.compact.OFF_ROUND0, NHT_Constants.compact.OFF_INACTIVE, NHT_Constants.compact.OFF_Y1, NHT_Constants.compact.COMPACT_Y1, NHT_Constants.compact.OFF_SEMANTIC, NHT_Constants.compact.HEADER, NHT_Constants.compact.COMPACT_SEMANTIC, NHT_Constants.compact.SEMANTIC_COMPACT_VALUES, NHT_Constants.compact.LOGICAL_SEMANTIC, NHT_Constants.verifier.SEMANTIC_BYTES, NHT_Constants.compact.FINAL_LEN]
 rfl
theorem round1 : NHT_Constants.compact.OFF_ROUND1=ok 7783#usize := by
 simp only [NHT_Constants.compact.OFF_OPENINGS, NHT_Constants.compact.OFF_FINAL, NHT_Constants.compact.OFF_ROUND1, NHT_Constants.compact.OFF_FOLDED_ROOT, NHT_Constants.compact.OFF_ROUND0, NHT_Constants.compact.OFF_INACTIVE, NHT_Constants.compact.OFF_Y1, NHT_Constants.compact.COMPACT_Y1, NHT_Constants.compact.OFF_SEMANTIC, NHT_Constants.compact.HEADER, NHT_Constants.compact.COMPACT_SEMANTIC, NHT_Constants.compact.SEMANTIC_COMPACT_VALUES, NHT_Constants.compact.LOGICAL_SEMANTIC, NHT_Constants.verifier.SEMANTIC_BYTES, NHT_Constants.compact.FINAL_LEN]
 rfl
theorem final : NHT_Constants.compact.OFF_FINAL=ok 8007#usize := by
 simp only [NHT_Constants.compact.OFF_OPENINGS, NHT_Constants.compact.OFF_FINAL, NHT_Constants.compact.OFF_ROUND1, NHT_Constants.compact.OFF_FOLDED_ROOT, NHT_Constants.compact.OFF_ROUND0, NHT_Constants.compact.OFF_INACTIVE, NHT_Constants.compact.OFF_Y1, NHT_Constants.compact.COMPACT_Y1, NHT_Constants.compact.OFF_SEMANTIC, NHT_Constants.compact.HEADER, NHT_Constants.compact.COMPACT_SEMANTIC, NHT_Constants.compact.SEMANTIC_COMPACT_VALUES, NHT_Constants.compact.LOGICAL_SEMANTIC, NHT_Constants.verifier.SEMANTIC_BYTES, NHT_Constants.compact.FINAL_LEN]
 rfl
theorem openings : NHT_Constants.compact.OFF_OPENINGS=ok 10055#usize := by
 simp only [NHT_Constants.compact.OFF_OPENINGS, NHT_Constants.compact.OFF_FINAL, NHT_Constants.compact.OFF_ROUND1, NHT_Constants.compact.OFF_FOLDED_ROOT, NHT_Constants.compact.OFF_ROUND0, NHT_Constants.compact.OFF_INACTIVE, NHT_Constants.compact.OFF_Y1, NHT_Constants.compact.COMPACT_Y1, NHT_Constants.compact.OFF_SEMANTIC, NHT_Constants.compact.HEADER, NHT_Constants.compact.COMPACT_SEMANTIC, NHT_Constants.compact.SEMANTIC_COMPACT_VALUES, NHT_Constants.compact.LOGICAL_SEMANTIC, NHT_Constants.verifier.SEMANTIC_BYTES, NHT_Constants.compact.FINAL_LEN]
 rfl
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
