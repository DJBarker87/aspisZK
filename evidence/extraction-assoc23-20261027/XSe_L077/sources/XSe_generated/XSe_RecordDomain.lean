import XSe_ValidatorTransport
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSe_RecordDomain
/-- Source row geometry bounds every reached validator payload by116 fields. -/
theorem source (row tag : U8) (size : Usize)
 (run : r1_wire.row_shape row=ok (some (tag,size))) : size.val≤3712 := by
 have a : (3#usize*29#usize : Result Usize)=ok 87#usize := by
  apply AspisR1CurrentCaller.UsizeArithmetic.mul_eq_ok <;> scalar_tac
 have b : (87#usize+29#usize : Result Usize)=ok 116#usize := by
  apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac
 have c : (116#usize*32#usize : Result Usize)=ok 3712#usize := by
  apply AspisR1CurrentCaller.UsizeArithmetic.mul_eq_ok <;> scalar_tac
 have d : (29#usize*32#usize : Result Usize)=ok 928#usize := by
  apply AspisR1CurrentCaller.UsizeArithmetic.mul_eq_ok <;> scalar_tac
 have e : (28#usize*32#usize : Result Usize)=ok 896#usize := by
  apply AspisR1CurrentCaller.UsizeArithmetic.mul_eq_ok <;> scalar_tac
 unfold r1_wire.row_shape at run
 simp only [r1_wire.CLAIMS,r1_wire.LANES,r1_wire.POINTS] at run
 repeat' first
 | split at run
 | simp only [a,b,c,d,e,bind_tc_ok] at run
 | (cases run <;> scalar_tac)
#print axioms source
end XSe_RecordDomain
