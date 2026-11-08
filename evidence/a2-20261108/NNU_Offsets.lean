import NNU_OffsetSubtract
import NNH_Tx2LiteralSlots
set_option autoImplicit false
namespace AspisR1.NNU_Offsets
open Aeneas Aeneas.Std Result

theorem semantic_values : NHT_Constants.compact.SEMANTIC_COMPACT_VALUES=(.ok 426#usize : Result Usize) := by
 simp only [NHT_Constants.compact.SEMANTIC_COMPACT_VALUES,
  NNU_OffsetArithmetic.mul 10#usize 28#usize 280#usize (by decide),bind_tc_ok,
  NNU_OffsetArithmetic.add 1#usize 280#usize 281#usize (by decide),
  NNU_OffsetArithmetic.add 87#usize 29#usize 116#usize (by decide),
  NNU_OffsetArithmetic.add 281#usize 116#usize 397#usize (by decide),
  NNU_OffsetArithmetic.add 397#usize 29#usize 426#usize (by decide)]

theorem logical : NHT_Constants.compact.LOGICAL_SEMANTIC=(.ok 13831#usize : Result Usize) := by
 simp only [NHT_Constants.compact.LOGICAL_SEMANTIC,NHT_Constants.verifier.SEMANTIC_BYTES,
  NNU_OffsetArithmetic.mul 29#usize 32#usize 928#usize (by decide),bind_tc_ok,
  NNU_OffsetArithmetic.add 12903#usize 928#usize 13831#usize (by decide)]

theorem semantic : NHT_Constants.compact.COMPACT_SEMANTIC=(.ok 7015#usize : Result Usize) := by
 simp only [NHT_Constants.compact.COMPACT_SEMANTIC,semantic_values,logical,bind_tc_ok,
  NNU_OffsetArithmetic.mul 16#usize 426#usize 6816#usize (by decide),
  NNU_OffsetSubtract.sub 13831#usize 6816#usize 7015#usize (by decide) (by decide)]

theorem y1 : NHT_Constants.compact.OFF_Y1=(.ok 7031#usize : Result Usize) := by
 simp only [NHT_Constants.compact.OFF_Y1,NHT_Constants.compact.OFF_SEMANTIC,
  NHT_Constants.compact.HEADER,semantic,bind_tc_ok,
  NNU_OffsetArithmetic.add 16#usize 7015#usize 7031#usize (by decide)]

theorem compact_y1 : NHT_Constants.compact.COMPACT_Y1=(.ok 464#usize : Result Usize) := by
 rw [NHT_Constants.compact.COMPACT_Y1]
 exact NNU_OffsetArithmetic.mul 29#usize 16#usize 464#usize (by decide)

theorem inactive : NHT_Constants.compact.OFF_INACTIVE=(.ok 7495#usize : Result Usize) := by
 simp only [NHT_Constants.compact.OFF_INACTIVE,y1,compact_y1,bind_tc_ok,
  NNU_OffsetArithmetic.add 7031#usize 464#usize 7495#usize (by decide)]

theorem round0 : NHT_Constants.compact.OFF_ROUND0=(.ok 7527#usize : Result Usize) := by
 simp only [NHT_Constants.compact.OFF_ROUND0,inactive,bind_tc_ok,
  NNU_OffsetArithmetic.add 7495#usize 32#usize 7527#usize (by decide)]

theorem folded : NHT_Constants.compact.OFF_FOLDED_ROOT=(.ok 7751#usize : Result Usize) := by
 simp only [NHT_Constants.compact.OFF_FOLDED_ROOT,round0,bind_tc_ok,
  NNU_OffsetArithmetic.add 7527#usize 224#usize 7751#usize (by decide)]

theorem round1 : NHT_Constants.compact.OFF_ROUND1=(.ok 7783#usize : Result Usize) := by
 simp only [NHT_Constants.compact.OFF_ROUND1,folded,bind_tc_ok,
  NNU_OffsetArithmetic.add 7751#usize 32#usize 7783#usize (by decide)]

theorem final_offset : NHT_Constants.compact.OFF_FINAL=(.ok 8007#usize : Result Usize) := by
 simp only [NHT_Constants.compact.OFF_FINAL,round1,bind_tc_ok,
  NNU_OffsetArithmetic.add 7783#usize 224#usize 8007#usize (by decide)]

theorem openings : NHT_Constants.compact.OFF_OPENINGS=(.ok 10055#usize : Result Usize) := by
 simp only [NHT_Constants.compact.OFF_OPENINGS,NHT_Constants.compact.FINAL_LEN,final_offset,bind_tc_ok,
  NNU_OffsetArithmetic.mul 64#usize 32#usize 2048#usize (by decide),
  NNU_OffsetArithmetic.add 8007#usize 2048#usize 10055#usize (by decide)]

theorem split_value : NHT_Constants.compact.SPLIT=10#usize := by
 rw [NHT_Constants.compact.SPLIT]
#print axioms semantic_values
#print axioms logical
#print axioms semantic
#print axioms y1
#print axioms compact_y1
#print axioms inactive
#print axioms round0
#print axioms folded
#print axioms round1
#print axioms final_offset
#print axioms openings
#print axioms split_value
end AspisR1.NNU_Offsets
