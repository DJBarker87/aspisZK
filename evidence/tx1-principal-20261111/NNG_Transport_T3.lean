import NNG_Transport_T2
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Transport
open Aeneas Aeneas.Std
open AspisR1.NMT_Transport (arr vec arr_inverse vec_inverse)
def toT3 (x : NNG_verify_finish.aspis_core.state_only_prefix.r0.Challenges) : AspisR1PublicPreparation.r1_wire.Challenges :=
 ⟨toT1 (x.lambda),toT1 (x.chi),toT1 (x.theta),arr (fun z => toT1 (z)) (x.zc),toT1 (x.mu),toT1 (x.eta)⟩
def fromT3 (x : AspisR1PublicPreparation.r1_wire.Challenges) : NNG_verify_finish.aspis_core.state_only_prefix.r0.Challenges :=
 ⟨fromT1 (x.lambda),fromT1 (x.chi),fromT1 (x.theta),arr (fun z => fromT1 (z)) (x.zc),fromT1 (x.mu),fromT1 (x.eta)⟩
@[simp] theorem toT3_inverse (x : NNG_verify_finish.aspis_core.state_only_prefix.r0.Challenges) : fromT3 (toT3 x)=x := by
 cases x <;> simp [toT3,fromT3]
#print axioms toT3_inverse
@[simp] theorem fromT3_inverse (x : AspisR1PublicPreparation.r1_wire.Challenges) : toT3 (fromT3 x)=x := by
 cases x <;> simp [fromT3,toT3]
#print axioms fromT3_inverse
end AspisR1.NNG_Transport
