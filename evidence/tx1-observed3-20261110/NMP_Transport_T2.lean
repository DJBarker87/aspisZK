import NMP_Transport_T1
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_Transport
open Aeneas Aeneas.Std
open AspisR1.NMT_Transport (arr vec arr_inverse vec_inverse)
def toT2 (x : NMP_prepare.aspis_core.circle.SecureCirclePoint) : AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint :=
 ⟨toT1 (x.x),toT1 (x.y)⟩
def fromT2 (x : AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint) : NMP_prepare.aspis_core.circle.SecureCirclePoint :=
 ⟨fromT1 (x.x),fromT1 (x.y)⟩
@[simp] theorem toT2_inverse (x : NMP_prepare.aspis_core.circle.SecureCirclePoint) : fromT2 (toT2 x)=x := by
 cases x <;> simp [toT2,fromT2]
#print axioms toT2_inverse
@[simp] theorem fromT2_inverse (x : AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint) : toT2 (fromT2 x)=x := by
 cases x <;> simp [fromT2,toT2]
#print axioms fromT2_inverse
end AspisR1.NMP_Transport
