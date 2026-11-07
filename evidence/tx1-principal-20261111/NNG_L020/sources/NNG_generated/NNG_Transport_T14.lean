import NNG_Transport_T13
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Transport
open Aeneas Aeneas.Std
open AspisR1.NMT_Transport (arr vec arr_inverse vec_inverse)
def toT14 (x : NNG_verify_finish.r1_wire.ValidatedRecord) : AspisR1PublicPreparation.r1_wire.ValidatedRecord :=
 ⟨x.row,x.framed⟩
def fromT14 (x : AspisR1PublicPreparation.r1_wire.ValidatedRecord) : NNG_verify_finish.r1_wire.ValidatedRecord :=
 ⟨x.row,x.framed⟩
@[simp] theorem toT14_inverse (x : NNG_verify_finish.r1_wire.ValidatedRecord) : fromT14 (toT14 x)=x := by
 cases x <;> simp [toT14,fromT14]
#print axioms toT14_inverse
@[simp] theorem fromT14_inverse (x : AspisR1PublicPreparation.r1_wire.ValidatedRecord) : toT14 (fromT14 x)=x := by
 cases x <;> simp [fromT14,toT14]
#print axioms fromT14_inverse
end AspisR1.NNG_Transport
