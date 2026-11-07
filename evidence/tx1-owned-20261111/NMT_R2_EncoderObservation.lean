import NMT_R2_EncoderTotal
import NMT_R2_ConcreteS1
import NMT_R2_EmittedData
set_option autoImplicit false
noncomputable section
namespace NMT_R2_EncoderObservation
open Aeneas Aeneas.Std NMT_345 RSL NMT_R2_EmittedData

def run (st : Statement) : Obs (Except ProgramError Bytes) :=
 observe (fun a : Array U8 688#usize => a.val.map byte)
  (mapOuter (mapCore id (fun _ : EncodeError => (.InvalidAccountData : PE)))
   (encodeCall (commonValue st).lane_transition.candidate_afterstate))

theorem law (st : Statement) (env : Env) :
 RS.ofOption (NMT_R2_ConcreteS1.encode st) .invalidAccountData env (run st) := by
 unfold NMT_R2_ConcreteS1.encode run
 rw [NMT_R2_EncoderTotal.source]
 cases NMT_R2_EncoderTotal.value (commonValue st).lane_transition.candidate_afterstate <;> rfl
#print axioms law
end NMT_R2_EncoderObservation
end
