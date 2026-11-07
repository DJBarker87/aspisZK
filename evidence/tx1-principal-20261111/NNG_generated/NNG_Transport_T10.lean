import NNG_Transport_T9
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Transport
open Aeneas Aeneas.Std
open AspisR1.NMT_Transport (arr vec arr_inverse vec_inverse)
def toT10 {H : Type} (x : NNG_verify_finish.r1_wire.SemanticTranscript H) : AspisR1PublicPreparation.r1_wire.SemanticTranscript H :=
 ⟨x.state,x.hash,x.next_row⟩
def fromT10 {H : Type} (x : AspisR1PublicPreparation.r1_wire.SemanticTranscript H) : NNG_verify_finish.r1_wire.SemanticTranscript H :=
 ⟨x.state,x.hash,x.next_row⟩
@[simp] theorem toT10_inverse {H : Type} (x : NNG_verify_finish.r1_wire.SemanticTranscript H) : fromT10 (toT10 x)=x := by
 cases x <;> simp [toT10,fromT10]
#print axioms toT10_inverse
@[simp] theorem fromT10_inverse {H : Type} (x : AspisR1PublicPreparation.r1_wire.SemanticTranscript H) : toT10 (fromT10 x)=x := by
 cases x <;> simp [fromT10,toT10]
#print axioms fromT10_inverse
end AspisR1.NNG_Transport
