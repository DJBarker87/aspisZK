import AspisV8R19.R468R137ObservedQ22Entry
import AspisV8R19.R466Q22TraceBound

/-! The R137 entry observer is bounded by the actual Q22 model trace.
This is a total-oracle entry result only: it does not account for the
incoming callback memo table or establish any distributional law. -/
set_option autoImplicit false
namespace AspisV8R19.R469ActualR137Q22TraceBound

open Aeneas Aeneas.Std Result
open AspisV8R19

abbrev Bytes := R149QueryLoopBridge.Bytes
abbrev State := R149QueryLoopBridge.State
abbrev Trace := SamplerObservation.Trace

theorem observed_entry_trace_bound (H : Bytes → State) (s : State)
    (history : Trace) :
    ∃ out observed,
      R468R137ObservedQ22Entry.observedR137Entry H s history =
        .ok ((R468R137ObservedQ22Entry.mapEntryResult
          (QueryEntryExecution.finishSource out),
          R148QueryBlockBridge.queryTranscript H
            (Q22SamplerProgram.challengeRun H s).2.2), observed) ∧
      SamplerObservation.decodeTrace observed =
        SamplerObservation.decodeTrace history ++
          (Q22SamplerProgram.challengeRun H s).1 ∧
      (SamplerObservation.decodeTrace observed).length ≤
        (SamplerObservation.decodeTrace history).length + 16 := by
  obtain ⟨out, observed, hrun, _herase, htrace, _hresult⟩ :=
    R468R137ObservedQ22Entry.observed_entry_model H s history
  refine ⟨out, observed, hrun, htrace, ?_⟩
  rw [htrace, List.length_append]
  have hbound := R466Q22TraceBound.challengeRun_trace_length_le H s
  omega

#print axioms observed_entry_trace_bound
end AspisV8R19.R469ActualR137Q22TraceBound
