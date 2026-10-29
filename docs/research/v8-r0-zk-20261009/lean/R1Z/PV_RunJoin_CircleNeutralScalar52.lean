import R1Z.PV_RunJoin_CircleNeutralBase52
import R1Z.PV_B2_C_MachineArithmetic
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RunJoin_CircleNeutralScalar52

theorem wrapping_sub_zero (x : U32) : U32.wrapping_sub x 0#u32 = x := by
  apply UScalar.eq_of_val_eq
  rw [U32.wrapping_sub_val_eq]
  simp only [show (0#u32).val=0 from rfl,Nat.sub_zero,Nat.add_mod_right]
  rw [UScalar.size]
  exact Nat.mod_eq_of_lt x.hBounds

theorem subtract_shape (x : U32) :
    PV_RunJoin_CircleRawScalar52.field.ct.subtract_p x =
      ok (if x ≥ 2147483647#u32 then U32.wrapping_sub x 2147483647#u32 else x) := by
  unfold PV_RunJoin_CircleRawScalar52.field.ct.subtract_p PV_RunJoin_CircleRawScalar52.field.P
  by_cases h : x ≥ 2147483647#u32
  · simp only [h,decide_true,if_pos]
    rfl
  · simp only [h,decide_false,if_neg]
    change ok (U32.wrapping_sub x 0#u32) = ok x
    rw [wrapping_sub_zero]

theorem checked_add (a b : U32) (h : a.val+b.val < 2^32) :
    a + b = ok (U32.wrapping_add a b) := by
  change a.val+b.val < 4294967296 at h
  obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists (U32.add_spec (x := a) (y := b)
    (by simp only [U32.max,U32.numBits]; omega))
  have he : z = U32.wrapping_add a b := by
    apply UScalar.eq_of_val_eq
    rw [U32.wrapping_add_val_eq]
    simp only [UScalar.size,UScalarTy.numBits]
    change z.val = (a.val+b.val)%4294967296
    rw [Nat.mod_eq_of_lt h]
    exact hv
  simpa only [he] using hz

theorem checked_sub (a b : U32) (h : b.val ≤ a.val) :
    a - b = ok (U32.wrapping_sub a b) := by
  obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists (U32.sub_spec (x := a) (y := b) h)
  have he : z = U32.wrapping_sub a b := by
    apply UScalar.eq_of_val_eq
    rw [U32.wrapping_sub_val_eq]
    have ha := a.hBounds
    have hb := b.hBounds
    change a.val < 4294967296 at ha
    change b.val < 4294967296 at hb
    simp only [UScalar.size,UScalarTy.numBits]
    change z.val = (a.val + (4294967296-b.val)) % 4294967296
    rw [show a.val + (4294967296-b.val) = (a.val-b.val)+4294967296 from by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    exact hv.1
  simpa only [he] using hz

#print axioms wrapping_sub_zero
#print axioms subtract_shape
#print axioms checked_add
#print axioms checked_sub
end R1Z.PV_RunJoin_CircleNeutralScalar52
