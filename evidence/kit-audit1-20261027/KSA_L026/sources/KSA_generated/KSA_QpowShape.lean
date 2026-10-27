import KSA_Checks
open Aeneas Aeneas.Std Result XRn_Join_Release XRn_Join_FieldExternal
set_option autoImplicit false
namespace KSA
-- Symbolic, fixed four-cell spine, with field operations left opaque.
theorem qpow26_shape (x : aspis_core.field.QM31) :
    XRn_Join_qpow x 26 = (do
      let a ← aspis_core.field.QM31.mul qone x
      let b ← aspis_core.field.QM31.mul a a
      aspis_core.field.QM31.mul b b) := by
  have unit : aspis_core.field.QM31.mul qone qone = ok qone := by rfl
  have h5 : XRn_Join_qpow x 5 = aspis_core.field.QM31.mul qone x := by
    rw [XRn_Join_qpow]
    change (do
      let y ← XRn_Join_qpow x 2
      let z ← aspis_core.field.QM31.mul y y
      aspis_core.field.QM31.mul z x) = _
    rw [qpow_two]
    simp only [bind_tc_ok,unit]
  have h12 : XRn_Join_qpow x 12 = (do
      let a ← aspis_core.field.QM31.mul qone x
      aspis_core.field.QM31.mul a a) := by
    rw [XRn_Join_qpow]
    change (do
      let y ← XRn_Join_qpow x 5
      aspis_core.field.QM31.mul y y) = _
    rw [h5]
  rw [XRn_Join_qpow]
  change (do
    let y ← XRn_Join_qpow x 12
    aspis_core.field.QM31.mul y y) = _
  rw [h12]
  simp only [bind_assoc]
#print axioms qpow26_shape
end KSA
