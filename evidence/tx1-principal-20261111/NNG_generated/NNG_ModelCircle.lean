import NNG_InstallBase
import NNG_EmittedContext
import NJM_InvocationRoots
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ModelCircle
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NMP_ResultTransport (outer inner outer_inverse inner_inverse)
abbrev OldPoint := AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint
abbrev Point := aspis_core.circle.SecureCirclePoint
abbrev OldT (H : Type) := AspisR1PublicPreparation.r1_wire.SemanticTranscript H
abbrev T (H : Type) := r1_wire.SemanticTranscript H

def raiseReply {H : Type} (x : core.result.Result OldPoint AspisR1PublicPreparation.r1_wire.Error × OldT H) :
    core.result.Result Point r1_wire.Error × T H := ⟨inner fromT2 fromT13 x.1,fromT10 x.2⟩
def lowerReply {H : Type} (x : core.result.Result Point r1_wire.Error × T H) :
    core.result.Result OldPoint AspisR1PublicPreparation.r1_wire.Error × OldT H := ⟨inner toT2 toT13 x.1,toT10 x.2⟩
theorem roundtrip {H : Type} (x : core.result.Result OldPoint AspisR1PublicPreparation.r1_wire.Error × OldT H) :
    lowerReply (raiseReply x) = x := by
  rcases x with ⟨reply,t⟩
  unfold lowerReply raiseReply
  rw [inner_inverse fromT2 toT2 fromT13 toT13 fromT2_inverse fromT13_inverse,fromT10_inverse]
#print axioms roundtrip

def model {H : Type} (d : aspis_core.digest.Digest32 H) (t : T H) (r : r1_wire.ValidatedRecord) :=
  AspisR1PublicPreparation.PreparedHashCode.run
    (NJM_CircleCode.source (NNG_Install.digest d) (toT10 t) (toT14 r))

def call {H : Type} (d : aspis_core.digest.Digest32 H) (t : T H) (r : r1_wire.ValidatedRecord) :=
  outer raiseReply (model d t r).2

theorem call_model {H : Type} (d : aspis_core.digest.Digest32 H) (t : T H) (r : r1_wire.ValidatedRecord) :
    outer lowerReply (call d t r) = (model d t r).2 :=
  outer_inverse raiseReply lowerReply roundtrip _
#print axioms call_model
end AspisR1.NNG_ModelCircle
