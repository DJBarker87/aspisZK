import AspisV8R19.R467R137ObservedSqueeze
import AspisV8R19.QueryObservedExecution
import AspisV8R19.R150QueryPublicBridge

set_option autoImplicit false
namespace AspisV8R19.R468R137ObservedQ22Entry
open Aeneas Aeneas.Std Result
open AspisV8R19.R147QuerySqueezeBridge
open AspisV8R19.R148QueryBlockBridge
open AspisV8R19.R149QueryLoopBridge
open AspisV8R19.R150QueryPublicBridge
open AspisV8R19.QueryEntryExecution
open AspisV8R19.QueryObservedExecution
open AspisV8R19.QueryBlockStep
open AspisV8R19.QueryObservedBlock
open AspisV8R19.SamplerObservation
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.SourceDuplexStep
open AspisV8R19.DuplexFrames
open AspisV8R19.Q22SamplerProgram

abbrev Values := AspisV8R19.QueryChunkExecution.Values
abbrev QueryError := AspisR137Q22.transcript.QuerySampleError

/-- Run the observed R86 query entry on the exact model transcript, then map
its returned transcript representation to the actual R137 transcript type. -/
def observedR137Entry (H : Bytes → State) (s : State) : Observed
    ((core.result.Result Values QueryError) × AspisR137Q22.transcript.Transcript) :=
  fun history => do
    let ((result, next), history') ←
      QueryObservedSource.query_probe (QueryBlockStep.queryTranscript H s) history
    pure ((result, toR137 next), history')

def eraseObservedR137Entry (H : Bytes → State) (s : State) (history : Trace) :
    Result ((core.result.Result Values QueryError) × AspisR137Q22.transcript.Transcript) := do
  let ((result, next), _) ← observedR137Entry H s history
  pure (result, next)

theorem observed_entry_model (H : Bytes → State) (s : State) (history : Trace) :
    ∃ out : Values, ∃ observed : Trace,
      observedR137Entry H s history =
        .ok ((finishSource out,
          AspisV8R19.R148QueryBlockBridge.queryTranscript H
            (Q22SamplerProgram.challengeRun H s).2.2), observed) ∧
      eraseObservedR137Entry H s history =
        AspisR137Q22.r137_query_probe
          (AspisV8R19.R148QueryBlockBridge.queryTranscript H s) ∧
      decodeTrace observed = decodeTrace history ++ (Q22SamplerProgram.challengeRun H s).1 ∧
      (decodeResult (finishSource out),
        decodeState (AspisV8R19.R148QueryBlockBridge.queryTranscript H
          (Q22SamplerProgram.challengeRun H s).2.2).state) =
        (Q22SamplerProgram.challengeRun H s).2 := by
  obtain ⟨out, observed, hobs, hfinish, hout, htrace⟩ :=
    QueryObservedExecution.public_result H s history
  have hencoded : encodeModelResult (Q22SamplerProgram.challengeRun H s).2.1 =
      .ok (finishSource out) := by
    rw [← hfinish]
    exact R150QueryPublicBridge.encode_finish out
  have hmapped : observedR137Entry H s history =
      .ok ((finishSource out,
        AspisV8R19.R148QueryBlockBridge.queryTranscript H
          (Q22SamplerProgram.challengeRun H s).2.2), observed) := by
    simp [observedR137Entry, hobs,
      AspisV8R19.R467R137ObservedSqueeze.queryTranscript_toR137]
  have hactual : AspisR137Q22.r137_query_probe
      (AspisV8R19.R148QueryBlockBridge.queryTranscript H s) =
      .ok (finishSource out,
        AspisV8R19.R148QueryBlockBridge.queryTranscript H
          (Q22SamplerProgram.challengeRun H s).2.2) := by
    rw [R150QueryPublicBridge.public_exact, hencoded]
    simp [R150QueryPublicBridge.queryTranscript,
      AspisV8R19.R149QueryLoopBridge.queryTranscript,
      AspisV8R19.R148QueryBlockBridge.queryTranscript]
  have herase : eraseObservedR137Entry H s history =
      AspisR137Q22.r137_query_probe
        (AspisV8R19.R148QueryBlockBridge.queryTranscript H s) := by
    rw [eraseObservedR137Entry, hmapped, hactual]
    rfl
  have hdecode := QueryEntryExecution.decode_finish out
  rw [hfinish] at hdecode
  have hstate : decodeState
      (AspisV8R19.R148QueryBlockBridge.queryTranscript H
        (Q22SamplerProgram.challengeRun H s).2.2).state =
      (Q22SamplerProgram.challengeRun H s).2.2 := by
    simp [AspisV8R19.R148QueryBlockBridge.queryTranscript,
      AspisV8R19.R467R137ObservedSqueeze.queryTranscript_toR137,
      AspisV8R19.R149QueryLoopBridge.queryTranscript, state_roundtrip]
  refine ⟨out, observed, hmapped, herase, htrace, ?_⟩
  exact Prod.ext hdecode hstate

#print axioms observedR137Entry
#print axioms eraseObservedR137Entry
#print axioms observed_entry_model
end AspisV8R19.R468R137ObservedQ22Entry
