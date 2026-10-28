import PV_B3P_FieldBase227
namespace PV_B3P_Zero227
open Aeneas Aeneas.Std PV_B3P_FieldBase227 PV_B3P_227
set_option autoImplicit false

theorem subtract_zero : subtract 0#u32 = 0#u32 := by decide
theorem reduce_zero : reduce 0#u64 = 0#u32 := by decide
theorem add_zero_zero : add 0#u32 0#u32 = 0#u32 := by decide
theorem sub_zero_zero : sub 0#u32 0#u32 = 0#u32 := by decide
theorem mul_zero_zero : mul 0#u32 0#u32 = 0#u32 := by decide

theorem u64_mul_zero_right (x : U64) : U64.wrapping_mul x 0#u64 = 0#u64 := by
  apply UScalar.eq_of_val_eq
  rw [U64.wrapping_mul_val_eq]
  change x.val * 0 % _ = 0
  simp only [Nat.mul_zero,Nat.zero_mod]

theorem u64_mul_zero_left (x : U64) : U64.wrapping_mul 0#u64 x = 0#u64 := by
  apply UScalar.eq_of_val_eq
  rw [U64.wrapping_mul_val_eq]
  change 0 * x.val % _ = 0
  simp only [Nat.zero_mul,Nat.zero_mod]

theorem mul_zero_right (x : U32) : mul x 0#u32 = 0#u32 := by
  unfold mul
  change reduce (U64.wrapping_mul (UScalar.cast .U64 x) 0#u64) = 0#u32
  rw [u64_mul_zero_right,reduce_zero]

theorem mul_zero_left (x : U32) : mul 0#u32 x = 0#u32 := by
  unfold mul
  change reduce (U64.wrapping_mul 0#u64 (UScalar.cast .U64 x)) = 0#u32
  rw [u64_mul_zero_left,reduce_zero]

#print axioms u64_mul_zero_right
#print axioms u64_mul_zero_left
#print axioms mul_zero_right
#print axioms mul_zero_left

#print axioms subtract_zero
#print axioms reduce_zero
#print axioms add_zero_zero
#print axioms sub_zero_zero
#print axioms mul_zero_zero
end PV_B3P_Zero227
