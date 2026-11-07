import NNG_Transport_T0
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Transport
open Aeneas Aeneas.Std
open AspisR1.NMT_Transport (arr vec arr_inverse vec_inverse)
def toT1 (x : NNG_verify_finish.aspis_core.field.QM31) : AspisR1PublicPreparation.aspis_core.field.QM31 :=
 ⟨toT0 (x.c0),toT0 (x.c1)⟩
def fromT1 (x : AspisR1PublicPreparation.aspis_core.field.QM31) : NNG_verify_finish.aspis_core.field.QM31 :=
 ⟨fromT0 (x.c0),fromT0 (x.c1)⟩
@[simp] theorem toT1_inverse (x : NNG_verify_finish.aspis_core.field.QM31) : fromT1 (toT1 x)=x := by
 cases x <;> simp [toT1,fromT1]
#print axioms toT1_inverse
@[simp] theorem fromT1_inverse (x : AspisR1PublicPreparation.aspis_core.field.QM31) : toT1 (fromT1 x)=x := by
 cases x <;> simp [fromT1,toT1]
#print axioms fromT1_inverse
end AspisR1.NNG_Transport
