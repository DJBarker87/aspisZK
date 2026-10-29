import R1Z.PV_RunJoin_CircleNeutralBase52
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
    UScalar.add a b = ok (U32.wrapping_add a b) := by
  have ht : UScalar.tryMk .U32 (a.val+b.val) = ok (UScalar.ofNatCore (a.val+b.val) h) := by
    simp only [UScalar.tryMk,UScalar.tryMkOpt,UScalar.check_bounds,h,if_pos,Result.ofOption]
  change UScalar.tryMk .U32 (a.val+b.val) = _
  rw [ht]
  congr 1
  apply UScalar.eq_of_val_eq
  change a.val+b.val = (U32.wrapping_add a b).val
  rw [U32.wrapping_add_val_eq,UScalar.size]
  exact (Nat.mod_eq_of_lt h).symm

theorem checked_sub (a b : U32) (h : b.val ≤ a.val) :
    UScalar.sub a b = ok (U32.wrapping_sub a b) := by
  unfold UScalar.sub
  simp only [Nat.not_lt.mpr h,if_false]
  congr 1
  apply UScalar.eq_of_val_eq
  change (a.val-b.val)%4294967296 = (U32.wrapping_sub a b).val
  rw [U32.wrapping_sub_val_eq,UScalar.size]
  have ha := a.hBounds
  have hb := b.hBounds
  change a.val < 4294967296 at ha
  change b.val < 4294967296 at hb
  omega

#print axioms wrapping_sub_zero
#print axioms subtract_shape
#print axioms checked_add
#print axioms checked_sub
end R1Z.PV_RunJoin_CircleNeutralScalar52
