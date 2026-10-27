import KSA_Checks
open Aeneas Aeneas.Std Result XRn_Join_Release XRn_Join_FieldExternal
set_option autoImplicit false
namespace KSA
theorem qpow_even (x : aspis_core.field.QM31) (n : Nat) :
    XRn_Join_qpow x (2*n+2) = (do
      let y ← XRn_Join_qpow x n
      aspis_core.field.QM31.mul y y) := by
  have h : 2*n+2=(2*n+1)+1 := by omega
  rw [h,XRn_Join_qpow]
  have hd : (2*n+1)/2=n := by omega
  have hm : (2*n+1)%2=1 := by omega
  simp only [hd,hm,show ¬(1:Nat)=0 by decide,ite_false]
  cases XRn_Join_qpow x n with
  | fail e => rfl
  | div => rfl
  | ok y => simp only [bind_tc_ok]; cases aspis_core.field.QM31.mul y y <;> rfl
#print axioms qpow_even

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
    rw [show 12=2*5+2 by decide,qpow_even,h5]
  rw [show 26=2*12+2 by decide,qpow_even,h12]
  simp only [bind_assoc]
#print axioms qpow26_shape
end KSA
