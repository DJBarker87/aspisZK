import R1Z.PV_RunJoin_CircleNeutralScalar52
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralWord53
theorem add32 (a b : U32) (h : a.val+b.val < 4294967296) :
    (U32.wrapping_add a b).val = a.val+b.val := by
  rw [U32.wrapping_add_val_eq]
  norm_num only [UScalar.size,UScalarTy.numBits]
  exact Nat.mod_eq_of_lt h

theorem sub32 (a b : U32) (h : b.val ≤ a.val) :
    (U32.wrapping_sub a b).val = a.val-b.val := by
  rw [U32.wrapping_sub_val_eq]
  norm_num only [UScalar.size,UScalarTy.numBits]
  have ha := a.hBounds
  change a.val < 4294967296 at ha
  rw [show a.val+(4294967296-b.val) = (a.val-b.val)+4294967296 from by omega,
    Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

theorem add64 (a b : U64) (h : a.val+b.val < 18446744073709551616) :
    (U64.wrapping_add a b).val = a.val+b.val := by
  rw [U64.wrapping_add_val_eq]
  norm_num only [UScalar.size,UScalarTy.numBits]
  exact Nat.mod_eq_of_lt h

theorem sub64 (a b : U64) (h : b.val ≤ a.val) :
    (U64.wrapping_sub a b).val = a.val-b.val := by
  rw [U64.wrapping_sub_val_eq]
  norm_num only [UScalar.size,UScalarTy.numBits]
  have ha := a.hBounds
  change a.val < 18446744073709551616 at ha
  rw [show a.val+(18446744073709551616-b.val) = (a.val-b.val)+18446744073709551616 from by omega,
    Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

theorem mul64 (a b : U64) (h : a.val*b.val < 18446744073709551616) :
    (U64.wrapping_mul a b).val = a.val*b.val := by
  rw [U64.wrapping_mul_val_eq]
  norm_num only [UScalar.size,UScalarTy.numBits]
  exact Nat.mod_eq_of_lt h

#print axioms add32
#print axioms sub32
#print axioms add64
#print axioms sub64
#print axioms mul64
end R1Z.PV_RunJoin_CircleNeutralWord53
