import AspisV8R19.SamplerObservedSource
import AspisV8R19.SamplerObservedLaws

/-! The instrumented generated squeeze records its two actual hash inputs
and outputs in order. Unlike returned-value equality, this statement includes
the observer state. Instrumentation provenance remains separately checked. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerObservedSqueeze
open Aeneas Aeneas.Std Result AspisR72Sampler SamplerObservation
open SqueezeSourceExecution SqueezeOracleBridge DuplexFrames SourceDuplexStep
open SamplerObservedLaws

theorem execution (s : transcript.Transcript) (history : Trace) :
    SamplerObservedSource.squeeze_block s history = (do
      let out ← s.hash (message s.state 1#u8)
      let next ← s.hash (message s.state 2#u8)
      ok ((out,{s with state := next}),history ++
        [(message s.state 1#u8,out),(message s.state 2#u8,next)])) := by
  have hs : s.state.val.length = 32 := s.state.property
  have ht : s.state.val.take 32 = s.state.val := List.take_of_length_le (by omega)
  simp [SamplerObservedSource.squeeze_block,core.array.Array.index_mut,
    core.ops.index.IndexMutSlice,core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    Array.repeat,Array.to_slice,Slice.length,Slice.len,
    core.slice.Slice.copy_from_slice,Array.from_slice,List.setSlice!,List.slice,
    Array.update,transcript.DOM_SQUEEZE,transcript.DOM_ADVANCE,
    message,frame,Array.make,lift,bind_tc_ok,hs,List.set_append,ht,
    bind_apply,lift_apply,map_apply,observeHash,List.append_assoc]

theorem erase (s : transcript.Transcript) (history : Trace) :
    (do let (out,_) ← SamplerObservedSource.squeeze_block s history
        ok out) = transcript.Transcript.squeeze_block s := by
  rw [execution,SqueezeSourceExecution.execution]
  cases h1 : s.hash (message s.state 1#u8) <;>
    cases h2 : s.hash (message s.state 2#u8) <;> simp [bind_tc_ok]

def rawCalls (H : Bytes → State) (s : State) : Trace :=
  [(message (encodeState s) 1#u8,encodeState (step H s).1),
   (message (encodeState s) 2#u8,encodeState (step H s).2)]

theorem adapter_execution (H : Bytes → State) (s : State) (history : Trace) :
    SamplerObservedSource.squeeze_block (transcriptFor H s) history =
      .ok ((encodeState (step H s).1,transcriptFor H (step H s).2),
        history++rawCalls H s) := by
  rw [execution]
  simp only [transcriptFor,hashAdapter,squeeze_address,advance_address,bind_tc_ok,step,rawCalls]

theorem raw_calls_decode (H : Bytes → State) (s : State) :
    decodeTrace (rawCalls H s)=calls H s := by
  simp only [decodeTrace,rawCalls,List.map_cons,List.map_nil,state_roundtrip]
  exact addresses_match H s

theorem decoded_execution (H : Bytes → State) (s : State) (history : Trace) :
    (do let ((out,next),observed) ← SamplerObservedSource.squeeze_block (transcriptFor H s) history
        ok (decodeTrace observed,(decodeState out,decodeState next.state))) =
      .ok (decodeTrace history++calls H s,step H s) := by
  rw [adapter_execution]
  simp only [bind_tc_ok,decode_append,raw_calls_decode,state_roundtrip,transcriptFor]

#print axioms execution
#print axioms erase
#print axioms adapter_execution
#print axioms raw_calls_decode
#print axioms decoded_execution
end AspisV8R19.SamplerObservedSqueeze
