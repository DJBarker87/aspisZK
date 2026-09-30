import AspisR136BeforeOod.Funs
import AspisV8R19.R139NonzeroModelBridge

/-! Exact value/error/state correspondence for the `sample` helper extracted
from the selected R136 callback.  This is a deterministic callback bridge;
it makes no distribution, privacy, or soundness claim. -/
set_option autoImplicit false
namespace AspisV8R19.R140BeforeOodSampleBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR136BeforeOod
open AspisV8R19
open R137SamplerChallengeBridge R139NonzeroModelBridge
open R137TranscriptPrimitiveBridge
open DuplexFrames SourceDuplexStep

def mapInner
    (r : core.result.Result AspisR137Transcript.field.QM31
      AspisR137Transcript.transcript.ChallengeSampleExhausted) :
    core.result.Result AspisR136BeforeOod.aspis_core.field.QM31
      AspisR136BeforeOod.Error :=
  match r with
  | .Ok q => .Ok (AspisR136BeforeOod.fromR137QM31 q)
  | .Err _ => .Err AspisR136BeforeOod.Error.Sampler

def sampleModelFalse (H : Bytes → State) (s : State) :
    Result ((core.result.Result AspisR136BeforeOod.aspis_core.field.QM31
      AspisR136BeforeOod.Error) ×
      AspisR136BeforeOod.aspis_core.transcript.Transcript) :=
  .ok (mapInner (R137SamplerChallengeBridge.encodeResult
      (QM31SamplerProgram.challengeRun H s).2.1),
    transcriptFor H (QM31SamplerProgram.challengeRun H s).2.2)

def sampleModelTrue (H : Bytes → State) (s : State) :
    Result ((core.result.Result AspisR136BeforeOod.aspis_core.field.QM31
      AspisR136BeforeOod.Error) ×
      AspisR136BeforeOod.aspis_core.transcript.Transcript) :=
  .ok (mapInner (R139NonzeroModelBridge.encodePolicyResult
      (SamplerWrapperPolicies.nonzeroRun H s).2.1),
    transcriptFor H (SamplerWrapperPolicies.nonzeroRun H s).2.2)

theorem map_err_mapChallenge
    (r : core.result.Result AspisR137Transcript.field.QM31
      AspisR137Transcript.transcript.ChallengeSampleExhausted) :
    core.result.Result.map_err
      AspisR136BeforeOod.sample.closure.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedError
      (AspisR136BeforeOod.mapChallenge r) () = .ok (mapInner r) := by
  cases r <;> rfl

theorem sample_false_exact (H : Bytes → State) (s : State) :
    AspisR136BeforeOod.sample (transcriptFor H s) false =
      sampleModelFalse H s := by
  simp [AspisR136BeforeOod.sample,
    AspisR136BeforeOod.aspis_core.transcript.Transcript.challenge_qm31,
    R137SamplerChallengeBridge.challenge_exact,
    map_err_mapChallenge, sampleModelFalse, mapInner]

theorem sample_true_exact (H : Bytes → State) (s : State) :
    AspisR136BeforeOod.sample (transcriptFor H s) true =
      sampleModelTrue H s := by
  simp [AspisR136BeforeOod.sample,
    AspisR136BeforeOod.aspis_core.transcript.Transcript.challenge_nonzero_qm31,
    R139NonzeroModelBridge.nonzero_source_model_exact,
    map_err_mapChallenge, sampleModelTrue, mapInner]

#print axioms map_err_mapChallenge
#print axioms sample_false_exact
#print axioms sample_true_exact

end AspisV8R19.R140BeforeOodSampleBridge
