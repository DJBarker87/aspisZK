import NMP_Transport_T12
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_Transport
open Aeneas Aeneas.Std
open AspisR1.NMT_Transport (arr vec arr_inverse vec_inverse)
def toT13 (x : NMP_prepare.r1_wire.Prefix) : AspisR1PublicPreparation.r1_wire.Prefix :=
 ⟨x.c1_root,x.records⟩
def fromT13 (x : AspisR1PublicPreparation.r1_wire.Prefix) : NMP_prepare.r1_wire.Prefix :=
 ⟨x.c1_root,x.records⟩
@[simp] theorem toT13_inverse (x : NMP_prepare.r1_wire.Prefix) : fromT13 (toT13 x)=x := by
 cases x <;> simp [toT13,fromT13]
#print axioms toT13_inverse
@[simp] theorem fromT13_inverse (x : AspisR1PublicPreparation.r1_wire.Prefix) : toT13 (fromT13 x)=x := by
 cases x <;> simp [fromT13,toT13]
#print axioms fromT13_inverse
end AspisR1.NMP_Transport
