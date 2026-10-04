import AspisR156FullFreeze.FunsCore
import AspisV8R19.R147QuerySqueezeBridge
import AspisV8R19.R137TranscriptPrimitiveBridge

set_option autoImplicit false
namespace AspisV8R19.R167TranscriptPrimitiveExecution
open Aeneas Aeneas.Std Result
open AspisR156FullFreeze.aspis_core
open R147QuerySqueezeBridge (message frame)

def toR137 (t : transcript.Transcript) : AspisR137Transcript.transcript.Transcript :=
  ⟨t.state,t.hash⟩
def fromR137 (t : AspisR137Transcript.transcript.Transcript) : transcript.Transcript :=
  ⟨t.state,t.hash⟩

theorem r156_execution (s : transcript.Transcript) :
    transcript.Transcript.squeeze_block s = (do
      let out ← s.hash (message s.state 1#u8)
      let next ← s.hash (message s.state 2#u8)
      ok (out, {s with state := next})) := by
  have hs : s.state.val.length = 32 := s.state.property
  have ht : s.state.val.take 32 = s.state.val := List.take_of_length_le (by omega)
  simp [transcript.Transcript.squeeze_block,
    core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    Array.repeat,Array.to_slice,Slice.length,Slice.len,
    core.slice.Slice.copy_from_slice,Array.from_slice,List.setSlice!,
    List.slice,Array.update,transcript.DOM_SQUEEZE,
    transcript.DOM_ADVANCE,message,frame,Array.make,
    lift,bind_tc_ok,hs,List.set_append,ht]

theorem r137_execution (s : AspisR137Transcript.transcript.Transcript) :
    AspisR137Transcript.transcript.Transcript.squeeze_block s = (do
      let out ← s.hash (message s.state 1#u8)
      let next ← s.hash (message s.state 2#u8)
      ok (out, {s with state := next})) := by
  have hs : s.state.val.length = 32 := s.state.property
  have ht : s.state.val.take 32 = s.state.val := List.take_of_length_le (by omega)
  simp [AspisR137Transcript.transcript.Transcript.squeeze_block,
    core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    Array.repeat,Array.to_slice,Slice.length,Slice.len,
    core.slice.Slice.copy_from_slice,Array.from_slice,List.setSlice!,
    List.slice,Array.update,AspisR137Transcript.transcript.DOM_SQUEEZE,
    AspisR137Transcript.transcript.DOM_ADVANCE,message,frame,Array.make,
    lift,bind_tc_ok,hs,List.set_append,ht]

theorem squeeze_map (s : transcript.Transcript) :
    transcript.Transcript.squeeze_block s = (do
      let (block,next) ← AspisR137Transcript.transcript.Transcript.squeeze_block (toR137 s)
      ok (block,fromR137 next)) := by
  cases s with
  | mk state hash =>
    rw [r156_execution,r137_execution]
    simp only [toR137,fromR137,bind_assoc_eq,bind_tc_ok]

theorem absorb_map (s : transcript.Transcript) (label : U8) (data : Slice U8) :
    transcript.Transcript.absorb s label data = (do
      let next ← AspisR137Transcript.transcript.Transcript.absorb (toR137 s) label data
      ok (fromR137 next)) := by
  cases s with
  | mk state hash =>
    simp only [transcript.Transcript.absorb,
      AspisR137Transcript.transcript.Transcript.absorb,
      transcript.Transcript.absorb.PACKED_ABSORB_BYTES,
      AspisR137Transcript.transcript.Transcript.absorb.PACKED_ABSORB_BYTES,
      transcript.DOM_ABSORB,AspisR137Transcript.transcript.DOM_ABSORB,
      toR137,fromR137,lift,bind_tc_ok]
    split <;> simp only [bind_assoc_eq,bind_tc_ok]

theorem to_from (s : AspisR137Transcript.transcript.Transcript) :
    toR137 (fromR137 s) = s := by cases s; rfl

theorem from_to (s : transcript.Transcript) :
    fromR137 (toR137 s) = s := by cases s; rfl

def transcriptFor (H : DuplexFrames.Bytes → SourceDuplexStep.State)
    (s : SourceDuplexStep.State) : transcript.Transcript :=
  fromR137 (R137TranscriptPrimitiveBridge.transcriptFor H s)

theorem squeeze_exact (H : DuplexFrames.Bytes → SourceDuplexStep.State)
    (s : SourceDuplexStep.State) :
    transcript.Transcript.squeeze_block (transcriptFor H s) =
      .ok (SqueezeOracleBridge.encodeState (SourceDuplexStep.step H s).1,
        transcriptFor H (SourceDuplexStep.step H s).2) := by
  rw [squeeze_map]
  simp only [transcriptFor, to_from,
    R137TranscriptPrimitiveBridge.squeeze_source_step, bind_tc_ok]

theorem absorb_exact (H : DuplexFrames.Bytes → SourceDuplexStep.State)
    (s : SourceDuplexStep.State) (label : U8) (data : Slice U8) :
    transcript.Transcript.absorb (transcriptFor H s) label data =
      .ok (transcriptFor H
        (H (DuplexFrames.absorb (SourceDuplexStep.bytes s)
          (SqueezeOracleBridge.decodeByte label)
          (R137TranscriptPrimitiveBridge.decodedSlice data)))) := by
  rw [absorb_map]
  simp only [transcriptFor, to_from]
  by_cases h : data.len ≤
    AspisR137Transcript.transcript.Transcript.absorb.PACKED_ABSORB_BYTES.wrapping_sub
      34#usize
  · rw [R137TranscriptPrimitiveBridge.short_absorb_execution H s label data h]
    rfl
  · rw [R137TranscriptPrimitiveBridge.long_absorb_execution H s label data h]
    rfl

#print axioms to_from
#print axioms from_to
#print axioms squeeze_exact
#print axioms absorb_exact
#print axioms r156_execution
#print axioms r137_execution
#print axioms squeeze_map
#print axioms absorb_map
end AspisV8R19.R167TranscriptPrimitiveExecution
