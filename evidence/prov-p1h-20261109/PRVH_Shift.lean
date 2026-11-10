import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error

namespace PRVH

/-- checked `x >>> i` (Usize by Usize) equals the wrapping shift by `i as u32` whenever the amount is below 32 (so below `Usize.numBits`, which is 32 or 64). -/
theorem usize_shr_usize (x i : Std.Usize) (h : i.val < 32) :
    (x >>> i : Result Std.Usize) = ok (Std.Usize.wrapping_shr x (UScalar.cast .U32 i)) := by
  show UScalar.shiftRight_UScalar x i = _
  unfold UScalar.shiftRight_UScalar
  have hc : (UScalar.cast .U32 i).val = i.val := by
    rw [UScalar.cast_val_eq]
    exact Nat.mod_eq_of_lt (by simp [UScalarTy.numBits]; omega)
  rcases System.Platform.numBits_eq with hb | hb
  · simp [UScalar.shiftRight, Std.Usize.wrapping_shr, UScalar.wrapping_shr, UScalarTy.numBits, hc, hb]
    rw [if_pos h, Nat.mod_eq_of_lt h]
  · simp [UScalar.shiftRight, Std.Usize.wrapping_shr, UScalar.wrapping_shr, UScalarTy.numBits, hc, hb]
    rw [if_pos (by omega), Nat.mod_eq_of_lt (by omega)]

/-- checked `x <<< i` (Usize by Usize) equals the wrapping shift by `i as u32` whenever the amount is below 32. -/
theorem usize_shl_usize (x i : Std.Usize) (h : i.val < 32) :
    (x <<< i : Result Std.Usize) = ok (Std.Usize.wrapping_shl x (UScalar.cast .U32 i)) := by
  show UScalar.shiftLeft_UScalar x i = _
  unfold UScalar.shiftLeft_UScalar
  have hc : (UScalar.cast .U32 i).val = i.val := by
    rw [UScalar.cast_val_eq]
    exact Nat.mod_eq_of_lt (by simp [UScalarTy.numBits]; omega)
  rcases System.Platform.numBits_eq with hb | hb
  · simp [UScalar.shiftLeft, Std.Usize.wrapping_shl, UScalar.wrapping_shl, UScalarTy.numBits, hc, hb]
    rw [if_pos h, Nat.mod_eq_of_lt h]
  · simp [UScalar.shiftLeft, Std.Usize.wrapping_shl, UScalar.wrapping_shl, UScalarTy.numBits, hc, hb]
    rw [if_pos (by omega), Nat.mod_eq_of_lt (by omega)]

end PRVH
#print axioms PRVH.usize_shr_usize
#print axioms PRVH.usize_shl_usize
