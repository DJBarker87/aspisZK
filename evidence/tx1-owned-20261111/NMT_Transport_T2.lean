import NMT_Transport_T1
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMT_Transport
open Aeneas Aeneas.Std
def toT2 (x : NMT_tx1.aspis_core.circle.SecureCirclePoint) : AspisR1CurrentCaller.aspis_core.circle.SecureCirclePoint :=
 ⟨toT1 (x.x),toT1 (x.y)⟩
def fromT2 (x : AspisR1CurrentCaller.aspis_core.circle.SecureCirclePoint) : NMT_tx1.aspis_core.circle.SecureCirclePoint :=
 ⟨fromT1 (x.x),fromT1 (x.y)⟩
@[simp] theorem toT2_inverse (x : NMT_tx1.aspis_core.circle.SecureCirclePoint) : fromT2 (toT2 x)=x := by
 cases x <;> simp [toT2,fromT2]
#print axioms toT2_inverse
@[simp] theorem fromT2_inverse (x : AspisR1CurrentCaller.aspis_core.circle.SecureCirclePoint) : toT2 (fromT2 x)=x := by
 cases x <;> simp [fromT2,toT2]
#print axioms fromT2_inverse
end AspisR1.NMT_Transport
