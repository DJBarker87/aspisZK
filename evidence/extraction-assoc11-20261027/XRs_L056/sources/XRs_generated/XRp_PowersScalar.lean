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

#print axioms add
end XRp_PowersScalar
