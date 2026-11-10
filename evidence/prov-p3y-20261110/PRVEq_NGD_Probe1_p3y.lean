import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxRecDepth 2048
theorem a1 : (28#usize * 32#usize : Result Std.Usize) = ok 896#usize := by decide
theorem a2 : (28#usize * 32#usize : Result Std.Usize) = ok 896#usize := by simp
theorem a3 : (28#usize * 32#usize : Result Std.Usize) = ok 896#usize := by
  simp [HMul.hMul, Mul.mul, Std.Usize.mul, Std.UScalar.mul, Std.UScalar.tryMk, Std.UScalar.ofNat]
theorem a4 : (28#usize * 32#usize : Result Std.Usize) = ok 896#usize := by
  have := @Aeneas.Std.UScalar.mul_equiv
  exact?
#print Aeneas.Std.UScalar.mul
#print Aeneas.Std.Usize.mul
