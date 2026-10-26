import CurrentCallerUsizeArithmeticV1
set_option autoImplicit false
namespace AspisR1.FIw_ScalarIndices
open Aeneas Aeneas.Std Result
theorem mul2 : 2#usize * 16#usize=ok 32#usize := by
  apply AspisR1CurrentCaller.UsizeArithmetic.mul_eq_ok <;> scalar_tac
#print axioms mul2
theorem mul31 : 31#usize * 16#usize=ok 496#usize := by
  apply AspisR1CurrentCaller.UsizeArithmetic.mul_eq_ok <;> scalar_tac
#print axioms mul31
theorem mul28 : 28#usize * 16#usize=ok 448#usize := by
  apply AspisR1CurrentCaller.UsizeArithmetic.mul_eq_ok <;> scalar_tac
#print axioms mul28
theorem mul63 : 16#usize * 63#usize=ok 1008#usize := by
  apply AspisR1CurrentCaller.UsizeArithmetic.mul_eq_ok <;> scalar_tac
#print axioms mul63
theorem add44 : 32#usize + 12#usize=ok 44#usize := by
  apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac
#print axioms add44
theorem add508 : 496#usize + 12#usize=ok 508#usize := by
  apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac
#print axioms add508
theorem add460 : 448#usize + 12#usize=ok 460#usize := by
  apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac
#print axioms add460
theorem add1010 : 1008#usize + 2#usize=ok 1010#usize := by
  apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac
#print axioms add1010
theorem add26 : 16#usize + 10#usize=ok 26#usize := by
  apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac
#print axioms add26
theorem add28 : 26#usize + 2#usize=ok 28#usize := by
  apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac
#print axioms add28
end AspisR1.FIw_ScalarIndices
