import NNG_InstallBase
import NNG_EmittedContext
import NJM_InvocationRoots
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Model134
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NMP_ResultTransport (outer inner outer_inverse inner_inverse)
open AspisR1.NMT_Transport (arr arr_inverse)
abbrev OldQ := AspisR1PublicPreparation.aspis_core.field.QM31
abbrev OldT (H : Type) := AspisR1PublicPreparation.r1_wire.SemanticTranscript H
abbrev OldReply (H : Type) := OldQ × Array OldQ 10#usize × OldT H
abbrev Reply (H : Type) := Q × Alpha × r1_wire.SemanticTranscript H

def raiseReply {H : Type} (r : OldReply H) : Reply H :=
  ⟨fromT1 r.1,arr fromT1 r.2.1,fromT10 r.2.2⟩
def lowerReply {H : Type} (r : Reply H) : OldReply H :=
  ⟨toT1 r.1,arr toT1 r.2.1,toT10 r.2.2⟩
theorem roundtrip {H : Type} (r : OldReply H) : lowerReply (raiseReply r) = r := by
  rcases r with ⟨q,a,t⟩
  simp only [lowerReply,raiseReply,fromT1_inverse,fromT10_inverse]
  rw [arr_inverse fromT1 toT1 fromT1_inverse]
#print axioms roundtrip

/-- Exactly the deterministic MODEL occurring on the source side of the
CLOSED134 root NJM_InvocationRoots.rounds. No native observation, Cut, token
or frame selects this value. The complete digest-call log is retained. -/
def model {H : Type} (d : aspis_core.digest.Digest32 H)
    (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) :=
  AspisR1PublicPreparation.PreparedHashCode.run
    (AspisR1PublicPreparation.S1SemanticCode.rounds NJM_RoundJoin.R
      (NNG_Install.digest d) (toT12 p) (toT10 t))

/-- Fresh emitted-call carrier for the deterministic model; not a VLib field
instance. LIB supplies the field's graph of model, together with its domain. -/
def rounds {H : Type} (d : aspis_core.digest.Digest32 H)
    (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) :
    Result (core.result.Result (Reply H) r1_wire.Error) :=
  outer (inner raiseReply fromT13) (model d p t).2

/-- Every Result arm is transported to the CLOSED model, never to the
arbitrary native-cut chain image used by the retired support lemma. -/
theorem call_model {H : Type} (d : aspis_core.digest.Digest32 H)
    (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) :
    outer (inner lowerReply toT13) (rounds d p t) = (model d p t).2 := by
  apply outer_inverse
  intro r
  exact inner_inverse raiseReply lowerReply fromT13 toT13 roundtrip fromT13_inverse r
#print axioms call_model
end AspisR1.NNG_Model134
