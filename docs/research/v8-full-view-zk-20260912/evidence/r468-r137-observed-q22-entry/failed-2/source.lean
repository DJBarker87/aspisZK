import AspisV8R19.R467R137ObservedSqueeze
import AspisV8R19.QueryObservedExecution
import AspisV8R19.R150QueryPublicBridge

set_option autoImplicit false
namespace AspisV8R19.R468R137ObservedQ22Entry
open Aeneas Aeneas.Std Result

abbrev Values := AspisV8R19.QueryChunkExecution.Values
abbrev R86QueryError := AspisR86Query.transcript.QuerySampleError
abbrev R137QueryError := AspisR137Q22.transcript.QuerySampleError
abbrev Bytes := AspisV8R19.R149QueryLoopBridge.Bytes
abbrev State := AspisV8R19.R149QueryLoopBridge.State

/-- Constructor-preserving transport between the separately generated error
inductives in the R86 observer and R137 entry. -/
def mapQueryError : R86QueryError → R137QueryError
  | .BoundNotPowerOfTwo bound => .BoundNotPowerOfTwo bound
  | .CountExceedsBound count bound => .CountExceedsBound count bound
  | .DrawLimitExhausted count maxDraws => .DrawLimitExhausted count maxDraws

def mapEntryResult : core.result.Result Values R86QueryError →
    core.result.Result Values R137QueryError
  | .Ok out => .Ok out
  | .Err e => .Err (mapQueryError e)

/-- Run the observed R86 query entry on the exact model transcript, and map
both its returned transcript and its nominal query-error type to R137. -/
def observedR137Entry (H : Bytes → State) (s : State) :
    AspisV8R19.SamplerObservation.Observed
      ((core.result.Result Values R137QueryError) × AspisR137Q22.transcript.Transcript) :=
  fun history => do
    let ((result, next), history') ←
      AspisV8R19.QueryObservedSource.query_probe
        (AspisV8R19.QueryBlockStep.queryTranscript H s) history
    pure ((mapEntryResult result,
      AspisV8R19.R147QuerySqueezeBridge.toR137 next), history')

def eraseObservedR137Entry (H : Bytes → State) (s : State) (history : AspisV8R19.SamplerObservation.Trace) :
    Result ((core.result.Result Values R137QueryError) × AspisR137Q22.transcript.Transcript) := do
  let ((result, next), _) ← observedR137Entry H s history
  pure (result, next)

theorem observed_entry_model (H : Bytes → State) (s : State)
    (history : AspisV8R19.SamplerObservation.Trace) :
    ∃ out : Values, ∃ observed : AspisV8R19.SamplerObservation.Trace,
      observedR137Entry H s history =
        .ok ((AspisV8R19.QueryEntryExecution.finishSource out,
          AspisV8R19.R148QueryBlockBridge.queryTranscript H
            (AspisV8R19.Q22SamplerProgram.challengeRun H s).2.2), observed) ∧
      eraseObservedR137Entry H s history =
        AspisR137Q22.r137_query_probe
          (AspisV8R19.R148QueryBlockBridge.queryTranscript H s) ∧
      AspisV8R19.SamplerObservation.decodeTrace observed =
        AspisV8R19.SamplerObservation.decodeTrace history ++
          (AspisV8R19.Q22SamplerProgram.challengeRun H s).1 ∧
      (AspisV8R19.QueryEntryExecution.decodeResult
          (AspisV8R19.QueryEntryExecution.finishSource out),
        AspisV8R19.SqueezeOracleBridge.decodeState
          (AspisV8R19.R148QueryBlockBridge.queryTranscript H
            (AspisV8R19.Q22SamplerProgram.challengeRun H s).2.2).state) =
        (AspisV8R19.Q22SamplerProgram.challengeRun H s).2 := by
  obtain ⟨out, observed, hobs, hfinish, _hout, htrace⟩ :=
    AspisV8R19.QueryObservedExecution.public_result H s history
  have hencoded : AspisV8R19.R150QueryPublicBridge.encodeModelResult
      (AspisV8R19.Q22SamplerProgram.challengeRun H s).2.1 =
      .ok (AspisV8R19.R150QueryPublicBridge.finishSource out) := by
    rw [← hfinish]
    exact AspisV8R19.R150QueryPublicBridge.encode_finish out
  have hfinishMap : mapEntryResult
      (AspisV8R19.QueryEntryExecution.finishSource out) =
      AspisV8R19.R150QueryPublicBridge.finishSource out := by
    simp [mapEntryResult, mapQueryError,
      AspisV8R19.QueryEntryExecution.finishSource,
      AspisV8R19.R143QueryEntryBridge.finishSource]
  have hmapped : observedR137Entry H s history =
      .ok ((AspisV8R19.R150QueryPublicBridge.finishSource out,
        AspisV8R19.R148QueryBlockBridge.queryTranscript H
          (AspisV8R19.Q22SamplerProgram.challengeRun H s).2.2), observed) := by
    simp [observedR137Entry, hobs, hfinishMap,
      AspisV8R19.R467R137ObservedSqueeze.queryTranscript_toR137]
  have hactual : AspisR137Q22.r137_query_probe
      (AspisV8R19.R148QueryBlockBridge.queryTranscript H s) =
      .ok (AspisV8R19.R150QueryPublicBridge.finishSource out,
        AspisV8R19.R148QueryBlockBridge.queryTranscript H
          (AspisV8R19.Q22SamplerProgram.challengeRun H s).2.2) := by
    rw [AspisV8R19.R150QueryPublicBridge.public_exact, hencoded]
    simp [AspisV8R19.R150QueryPublicBridge.queryTranscript,
      AspisV8R19.R149QueryLoopBridge.queryTranscript,
      AspisV8R19.R148QueryBlockBridge.queryTranscript]
  have herase : eraseObservedR137Entry H s history =
      AspisR137Q22.r137_query_probe
        (AspisV8R19.R148QueryBlockBridge.queryTranscript H s) := by
    rw [eraseObservedR137Entry, hmapped, hactual]
    rfl
  have hdecode := AspisV8R19.QueryEntryExecution.decode_finish out
  rw [hfinish] at hdecode
  have hstate : AspisV8R19.SqueezeOracleBridge.decodeState
      (AspisV8R19.R148QueryBlockBridge.queryTranscript H
        (AspisV8R19.Q22SamplerProgram.challengeRun H s).2.2).state =
      (AspisV8R19.Q22SamplerProgram.challengeRun H s).2.2 := by
    simp [AspisV8R19.R148QueryBlockBridge.queryTranscript,
      AspisV8R19.R467R137ObservedSqueeze.queryTranscript_toR137,
      AspisV8R19.R149QueryLoopBridge.queryTranscript,
      AspisV8R19.SqueezeOracleBridge.state_roundtrip]
  refine ⟨out, observed, ?_, herase, htrace, ?_⟩
  · simpa only [hfinishMap] using hmapped
  · exact Prod.ext hdecode hstate

#print axioms mapQueryError
#print axioms mapEntryResult
#print axioms observedR137Entry
#print axioms eraseObservedR137Entry
#print axioms observed_entry_model
end AspisV8R19.R468R137ObservedQ22Entry
