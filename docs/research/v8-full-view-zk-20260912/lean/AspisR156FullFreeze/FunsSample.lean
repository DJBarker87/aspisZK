import AspisR156FullFreeze.FunsCore

open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR156FullFreeze

/-- [aspis_v8_performance_host::sample::{impl core::ops::function::FnOnce<(aspis_core::transcript::ChallengeSampleExhausted,), aspis_v8_performance_host::Error> for aspis_v8_performance_host::sample::closure}::call_once]:
    Source: '../relation_callback.rs', lines 108:131-108:148 -/
def
  sample.closure.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedError.call_once
  (c : sample.closure)
  (tupled_args : aspis_core.transcript.ChallengeSampleExhausted) :
  Result Error
  := do
  ok Error.Sampler

/-- Trait implementation: [aspis_v8_performance_host::sample::{impl core::ops::function::FnOnce<(aspis_core::transcript::ChallengeSampleExhausted,), aspis_v8_performance_host::Error> for aspis_v8_performance_host::sample::closure}]
    Source: '../relation_callback.rs', lines 108:131-108:148 -/
@[reducible]
def
  sample.closure.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedError
  : core.ops.function.FnOnce sample.closure
  aspis_core.transcript.ChallengeSampleExhausted Error := {
  call_once :=
    sample.closure.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedError.call_once
}

/-- [aspis_v8_performance_host::sample]:
    Source: '../relation_callback.rs', lines 108:0-108:150 -/
def sample
  (t : aspis_core.transcript.Transcript) (nonzero : Bool) :
  Result ((core.result.Result aspis_core.field.QM31 Error) ×
    aspis_core.transcript.Transcript)
  := do
  let (t1, r) ←
    if nonzero
    then
      do
      let (r1, t2) ←
        aspis_core.transcript.Transcript.challenge_nonzero_qm31 t
      ok (t2, r1)
    else
      do
      let (r1, t2) ← aspis_core.transcript.Transcript.challenge_qm31 t
      ok (t2, r1)
  let r1 ←
    core.result.Result.map_err
      sample.closure.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedError
      r ()
  ok (r1, t1)

#print axioms sample
end AspisR156FullFreeze
