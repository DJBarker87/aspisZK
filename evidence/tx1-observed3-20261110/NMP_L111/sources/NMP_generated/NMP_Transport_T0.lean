import NMP_TransportBase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_Transport
open Aeneas Aeneas.Std
open AspisR1.NMT_Transport (arr vec arr_inverse vec_inverse)
def toT0 (x : NMP_prepare.aspis_core.field.CM31) : AspisR1PublicPreparation.aspis_core.field.CM31 :=
 ⟨x.a,x.b⟩
def fromT0 (x : AspisR1PublicPreparation.aspis_core.field.CM31) : NMP_prepare.aspis_core.field.CM31 :=
 ⟨x.a,x.b⟩
@[simp] theorem toT0_inverse (x : NMP_prepare.aspis_core.field.CM31) : fromT0 (toT0 x)=x := by
 cases x <;> simp [toT0,fromT0]
#print axioms toT0_inverse
@[simp] theorem fromT0_inverse (x : AspisR1PublicPreparation.aspis_core.field.CM31) : toT0 (fromT0 x)=x := by
 cases x <;> simp [fromT0,toT0]
#print axioms fromT0_inverse
end AspisR1.NMP_Transport
