import XRp_CheckedWrapping
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRp_PowersScalar

theorem add (a b : U32) (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
    XRn_Join_Field.field.M31.add a b = AspisR1Qm31ArithmeticProbe.field.M31.add a b := by
  have had := XRp_CheckedWrapping.add a b (by omega)
  unfold XRn_Join_Field.field.M31.add AspisR1Qm31ArithmeticProbe.field.M31.add
  unfold XRn_Join_Field.field.P AspisR1Qm31ArithmeticProbe.field.P
  rw [had]
  change (if U32.wrapping_add a b ≥ 2147483647#u32 then
    ok (U32.wrapping_sub (U32.wrapping_add a b) 2147483647#u32) else ok (U32.wrapping_add a b)) =
    (if U32.wrapping_add a b ≥ 2147483647#u32 then do
      let z ← U32.wrapping_add a b - 2147483647#u32
      ok z
    else ok (U32.wrapping_add a b))
  by_cases hs : U32.wrapping_add a b ≥ 2147483647#u32
  · simp only [if_pos hs]
    rw [XRp_CheckedWrapping.sub _ _ (by scalar_tac)]
    rfl
  · simp only [if_neg hs]

theorem sub (a b : U32) (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
    XRn_Join_Field.field.M31.sub a b = AspisR1Qm31ArithmeticProbe.field.M31.sub a b := by
  have had := XRp_CheckedWrapping.add a 2147483647#u32 (by scalar_tac)
  let s := U32.wrapping_add a 2147483647#u32
  have hv : s.val = a.val + 2147483647 := by
    have h := UScalar.wrapping_add_val_eq a 2147483647#u32
    simp only [UScalar.size_def,UScalarTy.numBits] at h
    change s.val = (a.val+2147483647) % 4294967296 at h
    rw [Nat.mod_eq_of_lt (by omega)] at h
    exact h
  have hsub := XRp_CheckedWrapping.sub s b (by scalar_tac)
  unfold XRn_Join_Field.field.M31.sub AspisR1Qm31ArithmeticProbe.field.M31.sub
  unfold XRn_Join_Field.field.P AspisR1Qm31ArithmeticProbe.field.P
  rw [had]
  change (if U32.wrapping_sub s b ≥ 2147483647#u32 then
    ok (U32.wrapping_sub (U32.wrapping_sub s b) 2147483647#u32) else ok (U32.wrapping_sub s b)) =
    (do let t ← s-b
        if t ≥ 2147483647#u32 then do let z ← t-2147483647#u32; ok z else ok t)
  rw [hsub]
  change (if U32.wrapping_sub s b ≥ 2147483647#u32 then
    ok (U32.wrapping_sub (U32.wrapping_sub s b) 2147483647#u32) else ok (U32.wrapping_sub s b)) =
    (if U32.wrapping_sub s b ≥ 2147483647#u32 then do
      let z ← U32.wrapping_sub s b - 2147483647#u32; ok z
    else ok (U32.wrapping_sub s b))
  by_cases hs : U32.wrapping_sub s b ≥ 2147483647#u32
  · simp only [if_pos hs]
    rw [XRp_CheckedWrapping.sub _ _ (by scalar_tac)]
    rfl
  · simp only [if_neg hs]

#print axioms add
#print axioms sub
end XRp_PowersScalar
