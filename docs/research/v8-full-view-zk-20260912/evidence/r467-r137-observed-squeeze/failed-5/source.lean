import AspisV8R19.R147QuerySqueezeBridge
import AspisV8R19.QueryObservedBlock
import AspisV8R19.R148QueryBlockBridge

set_option autoImplicit false
namespace AspisV8R19.R467R137ObservedSqueeze
open Aeneas Aeneas.Std Result
open AspisV8R19.R147QuerySqueezeBridge
open AspisV8R19.QueryObservedBlock
open AspisV8R19.QueryBlockStep
open AspisV8R19.SamplerObservation
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.SourceDuplexStep
open AspisV8R19.DuplexFrames
open AspisV8R19.SamplerObservedSqueeze (rawCalls raw_calls_decode)

def eraseObservedSqueeze (t : AspisR86Query.transcript.Transcript)
    (history : Trace) :
    Result ((Array U8 32#usize) × AspisR137Q22.transcript.Transcript) := do
  let ((block, next), _) ← QueryObservedSource.squeeze_block t history
  pure (block, toR137 next)

theorem observed_squeeze_erases (t : AspisR86Query.transcript.Transcript)
    (history : Trace) :
    eraseObservedSqueeze t history =
      AspisR137Q22.transcript.Transcript.squeeze_block (toR137 t) := by
  have hm1 : SqueezeSourceExecution.message t.state 1#u8 =
      AspisV8R19.R147QuerySqueezeBridge.message t.state 1#u8 := rfl
  have hm2 : SqueezeSourceExecution.message t.state 2#u8 =
      AspisV8R19.R147QuerySqueezeBridge.message t.state 2#u8 := rfl
  rw [eraseObservedSqueeze, QueryObservedBlock.squeeze_execution, hm1, hm2]
  rw [squeeze_map, r86_execution]
  cases h1 : t.hash (AspisV8R19.R147QuerySqueezeBridge.message t.state 1#u8) <;>
    cases h2 : t.hash (AspisV8R19.R147QuerySqueezeBridge.message t.state 2#u8) <;>
    simp [toR137, bind_tc_ok, h1, h2]

theorem queryTranscript_toR137 (H : Bytes → State) (s : State) :
    AspisV8R19.R148QueryBlockBridge.queryTranscript H s =
      toR137 (QueryBlockStep.queryTranscript H s) := rfl

theorem query_adapter_records (H : Bytes → State) (s : State)
    (history : Trace) :
    QueryObservedSource.squeeze_block (QueryBlockStep.queryTranscript H s) history =
      .ok ((encodeState (step H s).1, QueryBlockStep.queryTranscript H (step H s).2),
        history ++ rawCalls H s) :=
  QueryObservedBlock.squeeze_step H s history

theorem query_adapter_trace_decodes (H : Bytes → State) (s : State)
    (history : Trace) :
    decodeTrace (history ++ rawCalls H s) = decodeTrace history ++ calls H s := by
  rw [decode_append, raw_calls_decode]

#print axioms observed_squeeze_erases
#print axioms queryTranscript_toR137
#print axioms query_adapter_records
#print axioms query_adapter_trace_decodes
end AspisV8R19.R467R137ObservedSqueeze
