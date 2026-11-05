import NHT_Constants
import NHT_OffsetArithmetic
set_option autoImplicit false
namespace NHT_Offsets
open Aeneas Aeneas.Std Result AspisR1CurrentCaller.UsizeArithmetic
/-- Small straight-line source expressions, via checked scalar laws. -/
theorem split : NHT_Constants.compact.SPLIT=10#usize := by rw [NHT_Constants.compact.SPLIT]
theorem semantic : NHT_Constants.verifier.SEMANTIC_BYTES=ok 13831#usize := by
 have mul : (29#usize*32#usize : Result Usize)=ok 928#usize := by apply mul_eq_ok <;> scalar_tac
 unfold NHT_Constants.verifier.SEMANTIC_BYTES
 rw [mul,bind_tc_ok]
 apply add_eq_ok <;> scalar_tac

theorem count : NHT_Constants.compact.SEMANTIC_COMPACT_VALUES=ok 426#usize := by
 have m : (10#usize*28#usize : Result Usize)=ok 280#usize := by apply mul_eq_ok <;> scalar_tac
 have a : (1#usize+280#usize : Result Usize)=ok 281#usize := by apply add_eq_ok <;> scalar_tac
 have b : (87#usize+29#usize : Result Usize)=ok 116#usize := by apply add_eq_ok <;> scalar_tac
 have c : (281#usize+116#usize : Result Usize)=ok 397#usize := by apply add_eq_ok <;> scalar_tac
 unfold NHT_Constants.compact.SEMANTIC_COMPACT_VALUES
 rw [m,bind_tc_ok,a,bind_tc_ok,b,bind_tc_ok,c,bind_tc_ok]
 apply add_eq_ok <;> scalar_tac

theorem compact_semantic : NHT_Constants.compact.COMPACT_SEMANTIC=ok 7015#usize := by
 have mul : (16#usize*426#usize : Result Usize)=ok 6816#usize := by apply mul_eq_ok <;> scalar_tac
 unfold NHT_Constants.compact.COMPACT_SEMANTIC NHT_Constants.compact.LOGICAL_SEMANTIC
 rw [count,bind_tc_ok,mul,bind_tc_ok,semantic,bind_tc_ok]
 apply NHT_OffsetArithmetic.sub_eq_ok <;> scalar_tac

theorem y1 : NHT_Constants.compact.OFF_Y1=ok 7031#usize := by
 unfold NHT_Constants.compact.OFF_Y1 NHT_Constants.compact.OFF_SEMANTIC NHT_Constants.compact.HEADER
 rw [compact_semantic,bind_tc_ok]
 apply add_eq_ok <;> scalar_tac

theorem inactive : NHT_Constants.compact.OFF_INACTIVE=ok 7495#usize := by
 have mul : (29#usize*16#usize : Result Usize)=ok 464#usize := by apply mul_eq_ok <;> scalar_tac
 unfold NHT_Constants.compact.OFF_INACTIVE NHT_Constants.compact.COMPACT_Y1
 rw [y1,bind_tc_ok,mul,bind_tc_ok]
 apply add_eq_ok <;> scalar_tac

theorem round0 : NHT_Constants.compact.OFF_ROUND0=ok 7527#usize := by
 unfold NHT_Constants.compact.OFF_ROUND0
 rw [inactive,bind_tc_ok]
 apply add_eq_ok <;> scalar_tac

theorem folded : NHT_Constants.compact.OFF_FOLDED_ROOT=ok 7751#usize := by
 unfold NHT_Constants.compact.OFF_FOLDED_ROOT
 rw [round0,bind_tc_ok]
 apply add_eq_ok <;> scalar_tac

theorem round1 : NHT_Constants.compact.OFF_ROUND1=ok 7783#usize := by
 unfold NHT_Constants.compact.OFF_ROUND1
 rw [folded,bind_tc_ok]
 apply add_eq_ok <;> scalar_tac

theorem final : NHT_Constants.compact.OFF_FINAL=ok 8007#usize := by
 unfold NHT_Constants.compact.OFF_FINAL
 rw [round1,bind_tc_ok]
 apply add_eq_ok <;> scalar_tac

theorem openings : NHT_Constants.compact.OFF_OPENINGS=ok 10055#usize := by
 have mul : (64#usize*32#usize : Result Usize)=ok 2048#usize := by apply mul_eq_ok <;> scalar_tac
 unfold NHT_Constants.compact.OFF_OPENINGS NHT_Constants.compact.FINAL_LEN
 rw [mul,bind_tc_ok,final,bind_tc_ok]
 apply add_eq_ok <;> scalar_tac
#print axioms split
#print axioms semantic
#print axioms count
#print axioms compact_semantic
#print axioms y1
#print axioms inactive
#print axioms round0
#print axioms folded
#print axioms round1
#print axioms final
#print axioms openings
end NHT_Offsets
