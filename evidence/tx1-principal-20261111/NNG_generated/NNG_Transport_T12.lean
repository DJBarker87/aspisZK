import NNG_Transport_T11
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Transport
open Aeneas Aeneas.Std
open AspisR1.NMT_Transport (arr vec arr_inverse vec_inverse)
def toT12 (x : NNG_verify_finish.r1_wire.Prefix) : AspisR1PublicPreparation.r1_wire.Prefix :=
 ⟨x.c1_root,x.records⟩
def fromT12 (x : AspisR1PublicPreparation.r1_wire.Prefix) : NNG_verify_finish.r1_wire.Prefix :=
 ⟨x.c1_root,x.records⟩
@[simp] theorem toT12_inverse (x : NNG_verify_finish.r1_wire.Prefix) : fromT12 (toT12 x)=x := by
 cases x <;> simp [toT12,fromT12]
#print axioms toT12_inverse
@[simp] theorem fromT12_inverse (x : AspisR1PublicPreparation.r1_wire.Prefix) : toT12 (fromT12 x)=x := by
 cases x <;> simp [fromT12,toT12]
#print axioms fromT12_inverse
end AspisR1.NNG_Transport
