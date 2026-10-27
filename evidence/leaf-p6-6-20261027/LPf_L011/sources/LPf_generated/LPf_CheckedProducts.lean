import LPf_BaseMultiply
set_option autoImplicit false
namespace AspisR1.LPf_CheckedProducts
open Aeneas Aeneas.Std Result

/-- The checked operator appearing in Q.raw on every widened u32 limb.
The bounds are weaker than canonicality, so no caller strengthening is hidden. -/
theorem full_limb (x y : U64) (hx : x.val ≤ 4294967295)
    (hy : y.val ≤ 4294967295) :
    ∃ z, x * y = ok z ∧ z.val = x.val*y.val := by
  have bound := Nat.mul_le_mul hx hy
  have small : x.val*y.val < UScalar.size .U64 := by
    norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits]
    omega
  refine ⟨U64.wrapping_mul x y,FIo_ScalarBridge.mul x y small,?_⟩
  rw [U64.wrapping_mul_val_eq,Nat.mod_eq_of_lt small]

/-- Every multiplication by two in the folded Q.raw path is covered by
this bound; it also covers the constant PP and 3*P products. -/
theorem small_constant (x k : U64) (hx : x.val < 4611686018427387904)
    (hk : k.val ≤ 3) : ∃ z, k*x = ok z ∧ z.val = k.val*x.val := by
  have bound := Nat.mul_le_mul hk (show x.val ≤ 4611686018427387903 by omega)
  have small : k.val*x.val < UScalar.size .U64 := by
    norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits]
    omega
  refine ⟨U64.wrapping_mul k x,FIo_ScalarBridge.mul k x small,?_⟩
  rw [U64.wrapping_mul_val_eq,Nat.mod_eq_of_lt small]

#print axioms full_limb
#print axioms small_constant
end AspisR1.LPf_CheckedProducts
