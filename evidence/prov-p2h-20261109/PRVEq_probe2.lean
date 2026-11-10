import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
#print UScalar.size
#print Std.Usize.numBits
#check @UScalar.size_eq
#check @Usize.size_eq
#check @UScalar.max_succ_eq_size
#check @UScalar.max_eq_size_sub_one
example : Std.Usize.max + 1 = UScalar.size UScalarTy.Usize := by
  rw [Std.Usize.max_def]
  trace_state
  unfold UScalar.size
  trace_state
  have := Nat.one_le_two_pow (n := Std.Usize.numBits)
  omega
