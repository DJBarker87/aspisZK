import NKE_CommonCalls
set_option autoImplicit false
namespace NKO_Offsets
open Aeneas Aeneas.Std Result
theorem inactive : NHT_Constants.compact.OFF_INACTIVE=ok 7495#usize := by
 simp only [NHT_Constants.compact.OFF_INACTIVE,NHT_Constants.compact.OFF_Y1,NHT_Constants.compact.COMPACT_Y1,NHT_Constants.compact.COMPACT_SEMANTIC,NHT_Constants.compact.OFF_SEMANTIC,NHT_Constants.compact.HEADER,NHT_Constants.compact.SEMANTIC_COMPACT_VALUES,NHT_Constants.compact.LOGICAL_SEMANTIC,NHT_Constants.verifier.SEMANTIC_BYTES,NHT_Constants.compact.OFF_ROUND0,NHT_Constants.compact.OFF_FOLDED_ROOT,NHT_Constants.compact.OFF_ROUND1,NHT_Constants.compact.OFF_FINAL,NHT_Constants.compact.OFF_OPENINGS,NHT_Constants.compact.FINAL_LEN]
 scalar_tac
theorem round0 : NHT_Constants.compact.OFF_ROUND0=ok 7527#usize := by
 simp only [NHT_Constants.compact.OFF_INACTIVE,NHT_Constants.compact.OFF_Y1,NHT_Constants.compact.COMPACT_Y1,NHT_Constants.compact.COMPACT_SEMANTIC,NHT_Constants.compact.OFF_SEMANTIC,NHT_Constants.compact.HEADER,NHT_Constants.compact.SEMANTIC_COMPACT_VALUES,NHT_Constants.compact.LOGICAL_SEMANTIC,NHT_Constants.verifier.SEMANTIC_BYTES,NHT_Constants.compact.OFF_ROUND0,NHT_Constants.compact.OFF_FOLDED_ROOT,NHT_Constants.compact.OFF_ROUND1,NHT_Constants.compact.OFF_FINAL,NHT_Constants.compact.OFF_OPENINGS,NHT_Constants.compact.FINAL_LEN]
 scalar_tac
theorem folded : NHT_Constants.compact.OFF_FOLDED_ROOT=ok 7751#usize := by
 simp only [NHT_Constants.compact.OFF_INACTIVE,NHT_Constants.compact.OFF_Y1,NHT_Constants.compact.COMPACT_Y1,NHT_Constants.compact.COMPACT_SEMANTIC,NHT_Constants.compact.OFF_SEMANTIC,NHT_Constants.compact.HEADER,NHT_Constants.compact.SEMANTIC_COMPACT_VALUES,NHT_Constants.compact.LOGICAL_SEMANTIC,NHT_Constants.verifier.SEMANTIC_BYTES,NHT_Constants.compact.OFF_ROUND0,NHT_Constants.compact.OFF_FOLDED_ROOT,NHT_Constants.compact.OFF_ROUND1,NHT_Constants.compact.OFF_FINAL,NHT_Constants.compact.OFF_OPENINGS,NHT_Constants.compact.FINAL_LEN]
 scalar_tac
theorem round1 : NHT_Constants.compact.OFF_ROUND1=ok 7783#usize := by
 simp only [NHT_Constants.compact.OFF_INACTIVE,NHT_Constants.compact.OFF_Y1,NHT_Constants.compact.COMPACT_Y1,NHT_Constants.compact.COMPACT_SEMANTIC,NHT_Constants.compact.OFF_SEMANTIC,NHT_Constants.compact.HEADER,NHT_Constants.compact.SEMANTIC_COMPACT_VALUES,NHT_Constants.compact.LOGICAL_SEMANTIC,NHT_Constants.verifier.SEMANTIC_BYTES,NHT_Constants.compact.OFF_ROUND0,NHT_Constants.compact.OFF_FOLDED_ROOT,NHT_Constants.compact.OFF_ROUND1,NHT_Constants.compact.OFF_FINAL,NHT_Constants.compact.OFF_OPENINGS,NHT_Constants.compact.FINAL_LEN]
 scalar_tac
theorem final_message : NHT_Constants.compact.OFF_FINAL=ok 8007#usize := by
 simp only [NHT_Constants.compact.OFF_INACTIVE,NHT_Constants.compact.OFF_Y1,NHT_Constants.compact.COMPACT_Y1,NHT_Constants.compact.COMPACT_SEMANTIC,NHT_Constants.compact.OFF_SEMANTIC,NHT_Constants.compact.HEADER,NHT_Constants.compact.SEMANTIC_COMPACT_VALUES,NHT_Constants.compact.LOGICAL_SEMANTIC,NHT_Constants.verifier.SEMANTIC_BYTES,NHT_Constants.compact.OFF_ROUND0,NHT_Constants.compact.OFF_FOLDED_ROOT,NHT_Constants.compact.OFF_ROUND1,NHT_Constants.compact.OFF_FINAL,NHT_Constants.compact.OFF_OPENINGS,NHT_Constants.compact.FINAL_LEN]
 scalar_tac
theorem openings : NHT_Constants.compact.OFF_OPENINGS=ok 10055#usize := by
 simp only [NHT_Constants.compact.OFF_INACTIVE,NHT_Constants.compact.OFF_Y1,NHT_Constants.compact.COMPACT_Y1,NHT_Constants.compact.COMPACT_SEMANTIC,NHT_Constants.compact.OFF_SEMANTIC,NHT_Constants.compact.HEADER,NHT_Constants.compact.SEMANTIC_COMPACT_VALUES,NHT_Constants.compact.LOGICAL_SEMANTIC,NHT_Constants.verifier.SEMANTIC_BYTES,NHT_Constants.compact.OFF_ROUND0,NHT_Constants.compact.OFF_FOLDED_ROOT,NHT_Constants.compact.OFF_ROUND1,NHT_Constants.compact.OFF_FINAL,NHT_Constants.compact.OFF_OPENINGS,NHT_Constants.compact.FINAL_LEN]
 scalar_tac
#print axioms inactive
#print axioms round0
#print axioms folded
#print axioms round1
#print axioms final_message
#print axioms openings
end NKO_Offsets
