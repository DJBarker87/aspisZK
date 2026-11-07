import NMP_Transport_T10
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_Transport
open Aeneas Aeneas.Std
open AspisR1.NMT_Transport (arr vec arr_inverse vec_inverse)
def toT11 {H : Type} (x : NMP_prepare.r1_semantic.Verified H) : AspisR1PublicPreparation.r1_semantic.Verified H :=
 ⟨x.roots,toT3 (x.challenges),arr (fun z => toT1 (z)) (x.alpha),arr (fun z => arr (fun z => toT1 (z)) (z)) (x.claims),arr (fun z => toT1 (z)) (x.extra),arr (fun z => toT1 (z)) (x.before_z1),x.state_before_z0,arr (fun z => toT2 (z)) (x.z),toT10 (x.transcript)⟩
def fromT11 {H : Type} (x : AspisR1PublicPreparation.r1_semantic.Verified H) : NMP_prepare.r1_semantic.Verified H :=
 ⟨x.roots,fromT3 (x.challenges),arr (fun z => fromT1 (z)) (x.alpha),arr (fun z => arr (fun z => fromT1 (z)) (z)) (x.claims),arr (fun z => fromT1 (z)) (x.extra),arr (fun z => fromT1 (z)) (x.before_z1),x.state_before_z0,arr (fun z => fromT2 (z)) (x.z),fromT10 (x.transcript)⟩
@[simp] theorem toT11_inverse {H : Type} (x : NMP_prepare.r1_semantic.Verified H) : fromT11 (toT11 x)=x := by
 cases x <;> simp [toT11,fromT11]
#print axioms toT11_inverse
@[simp] theorem fromT11_inverse {H : Type} (x : AspisR1PublicPreparation.r1_semantic.Verified H) : toT11 (fromT11 x)=x := by
 cases x <;> simp [fromT11,toT11]
#print axioms fromT11_inverse
end AspisR1.NMP_Transport
