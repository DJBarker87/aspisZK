import AspisR72Sampler.Funs
import Mathlib.Tactic

/-! Exact byte framing of the actual generated duplex squeeze. The hash
parameter stays arbitrary and may fail/diverge; no randomness is assumed. -/
set_option autoImplicit false
namespace AspisV8R19.SqueezeSourceExecution
open Aeneas Aeneas.Std Result AspisR72Sampler

def frame (s : Array U8 32#usize) (tag : U8) : Array U8 33#usize :=
  ⟨s.val ++ [tag],by simp only [List.length_append,List.length_singleton,s.property]; rfl⟩
def message (s : Array U8 32#usize) (tag : U8) : Slice (Slice U8) :=
  Array.to_slice (Array.make 1#usize [Array.to_slice (frame s tag)])

theorem frame_bytes (s : Array U8 32#usize) (tag : U8) :
    (frame s tag).val = s.val ++ [tag] := rfl
theorem message_bytes (s : Array U8 32#usize) (tag : U8) :
    (message s tag).val.map (fun x => x.val) = [s.val ++ [tag]] := rfl

theorem execution (s : transcript.Transcript) :
    transcript.Transcript.squeeze_block s = (do
      let out ← s.hash (message s.state 1#u8)
      let next ← s.hash (message s.state 2#u8)
      ok (out,{s with state := next})) := by
  have hs : s.state.val.length = 32 := s.state.property
  have ht : s.state.val.take 32 = s.state.val := List.take_of_length_le (by omega)
  simp [transcript.Transcript.squeeze_block,core.array.Array.index_mut,
    core.ops.index.IndexMutSlice,core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    Array.repeat,Array.to_slice,Slice.length,Slice.len,
    core.slice.Slice.copy_from_slice,Array.from_slice,List.setSlice!,List.slice,
    Array.update,transcript.DOM_SQUEEZE,transcript.DOM_ADVANCE,
    message,frame,Array.make,lift,bind_tc_ok,hs,List.set_append,ht]

theorem success (s : transcript.Transcript) (out next : Array U8 32#usize)
    (ho : s.hash (message s.state 1#u8) = .ok out)
    (hn : s.hash (message s.state 2#u8) = .ok next) :
    transcript.Transcript.squeeze_block s = .ok (out,{s with state := next}) := by
  rw [execution,ho]; simp only [bind_tc_ok,hn]
theorem first_failure (s : transcript.Transcript) (e : Error)
    (h : s.hash (message s.state 1#u8) = .fail e) :
    transcript.Transcript.squeeze_block s = .fail e := by rw [execution,h]; rfl
theorem second_failure (s : transcript.Transcript) (out : Array U8 32#usize) (e : Error)
    (ho : s.hash (message s.state 1#u8) = .ok out)
    (hn : s.hash (message s.state 2#u8) = .fail e) :
    transcript.Transcript.squeeze_block s = .fail e := by rw [execution,ho]; simp only [bind_tc_ok,hn]; rfl
theorem first_divergence (s : transcript.Transcript)
    (h : s.hash (message s.state 1#u8) = .div) :
    transcript.Transcript.squeeze_block s = .div := by rw [execution,h]; rfl

#print axioms frame_bytes
#print axioms message_bytes
#print axioms execution
#print axioms success
#print axioms first_failure
#print axioms second_failure
#print axioms first_divergence
end AspisV8R19.SqueezeSourceExecution
