import LPi_TowerValues
set_option autoImplicit false
namespace NBG_Additive
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

/-- Canonical caller operands imply the full double result and a canonical
return; no successful-return hypothesis is supplied. -/
theorem m31_double (x : U32) (hx : x.val < 2147483647) :
    ∃ z, FIo_Native.aspis_core.field.M31.double x = ok z ∧
      z.val = (x.val + x.val) % 2147483647 ∧ z.val < 2147483647 :=
  LPi_NatBase.add x x hx hx

theorem cm31_double (x : NC) (hx : canonC x) :
    ∃ z, FIo_Native.aspis_core.field.CM31.double x = ok z ∧
      canonC z ∧ cw z = addC (cw x) (cw x) :=
  LPi_FieldValues.cm_add x x hx hx

#print axioms m31_double
#print axioms cm31_double
#print axioms AspisR1.LPi_NatBase.add
#print axioms AspisR1.LPi_NatBase.sub
#print axioms AspisR1.LPi_FieldValues.cm_add
#print axioms AspisR1.LPi_FieldValues.cm_sub
#print axioms AspisR1.LPi_FieldValues.by_r
#print axioms AspisR1.LPi_TowerValues.qm_add
#print axioms AspisR1.LPi_TowerValues.qm_sub
end NBG_Additive
