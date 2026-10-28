import R1Z.PV_CBL_Op208Extracted
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ShaCount
set_option autoImplicit false

theorem cast_count (n : Usize) : (UScalar.cast .U64 n).val = n.val := by
  rw [UScalar.cast_val_eq]
  refine Nat.mod_eq_of_lt (lt_of_lt_of_le n.hBounds ?_)
  simp only [UScalarTy.U64_numBits_eq, UScalarTy.Usize_numBits_eq]
  exact Nat.pow_le_pow_right (by omega) (by cases System.Platform.numBits_eq <;> simp_all)

theorem wrapping_count (old : U64) (n : Usize) :
    (U64.wrapping_add old (UScalar.cast .U64 n)).val =
      (old.val+n.val) % 2^64 := by
  rw [U64.wrapping_add_val_eq,cast_count]
  simp only [UScalar.size, UScalarTy.numBits]

theorem zero_count (old : U64) :
    U64.wrapping_add old (UScalar.cast .U64 0#usize) = old := by
  apply UScalar.eq_of_val_eq
  rw [wrapping_count]
  change (old.val+0) % 2^64 = old.val
  simp only [Nat.add_zero]
  exact Nat.mod_eq_of_lt (by simpa only [UScalar.size, UScalarTy.numBits] using old.hSize)

#print axioms cast_count
#print axioms wrapping_count
#print axioms zero_count
end R1Z.PV_CBL_ShaCount
