import R1Z.PV_RDB2C_PV_B2_D_ScalarCanonical
set_option autoImplicit false
namespace PV_B2_D_ScalarOperations
open Aeneas Aeneas.Std
open PV_B2_C_251FieldValue
abbrev Canon (x : U32) : Prop := x < aspis_core.field.P

theorem sub_zero (x : U32) : U32.wrapping_sub x 0#u32 = x := by
  apply UScalar.eq_of_val_eq
  rw [U32.wrapping_sub_val_eq]
  simp only [show (0#u32).val=0 from rfl,Nat.sub_zero,Nat.add_mod_right]
  rw [UScalar.size]
  exact Nat.mod_eq_of_lt x.hBounds

theorem subtract_shape (x : U32) : aspis_core.field.ct.subtract_p x =
    if x ≥ aspis_core.field.P then U32.wrapping_sub x aspis_core.field.P else x := by
  unfold aspis_core.field.ct.subtract_p
  by_cases h : x ≥ aspis_core.field.P
  · simp only [h,decide_true,if_pos]
    rfl
  · simp only [h,decide_false,if_neg]
    change U32.wrapping_sub x 0#u32 = x
    exact sub_zero x

theorem subtract_bound (x : U32) (hx : x.val < 4294967294) :
    Canon (aspis_core.field.ct.subtract_p x) := by
  rw [subtract_shape]
  by_cases h : x ≥ aspis_core.field.P
  · rw [if_pos h]
    change (U32.wrapping_sub x 2147483647#u32).val < 2147483647
    rw [U32.wrapping_sub_val_eq,UScalar.size]
    simp only [UScalarTy.numBits,show (2147483647#u32).val = 2147483647 from rfl]
    change (x.val + 2147483649) % 4294967296 < 2147483647
    change 2147483647 ≤ x.val at h
    omega
  · rw [if_neg h]
    exact Nat.lt_of_not_ge h

theorem add (a b : U32) (ha : Canon a) (hb : Canon b) :
    Canon (aspis_core.field.ct.add a b) := by
  unfold aspis_core.field.ct.add
  apply subtract_bound
  rw [core.num.U32.wrapping_add_val_eq,UScalar.size]
  change (a.val + b.val) % 4294967296 < 4294967294
  change a.val < 2147483647 at ha
  change b.val < 2147483647 at hb
  omega

theorem sub (a b : U32) (ha : Canon a) (hb : Canon b) :
    Canon (aspis_core.field.ct.sub a b) := by
  unfold aspis_core.field.ct.sub
  apply subtract_bound
  rw [core.num.U32.wrapping_sub_val_eq,core.num.U32.wrapping_add_val_eq,UScalar.size]
  change ((a.val + 2147483647) % 4294967296 + (4294967296 - b.val)) % 4294967296 < 4294967294
  change a.val < 2147483647 at ha
  change b.val < 2147483647 at hb
  omega

theorem mul (a b : U32) : Canon (aspis_core.field.M31.mul a b) :=
  PV_B2_D_ScalarCanonical.reduce_bound _
theorem reduce (a : U64) : Canon (aspis_core.field.M31.reduce_u64 a) :=
  PV_B2_D_ScalarCanonical.reduce_bound _
#print axioms sub_zero
#print axioms subtract_shape
#print axioms subtract_bound
#print axioms add
#print axioms sub
#print axioms mul
#print axioms reduce
end PV_B2_D_ScalarOperations
