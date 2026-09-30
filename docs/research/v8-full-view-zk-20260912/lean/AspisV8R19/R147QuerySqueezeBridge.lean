import AspisR137Q22.Funs
import AspisR86Query.Loops
import Mathlib.Tactic

/-! Exact transcript representation transport between the separately
extracted R137 and R86 squeeze functions. Arbitrary hash failures and
divergence remain visible; no oracle distribution is assumed. -/
set_option autoImplicit false
namespace AspisV8R19.R147QuerySqueezeBridge

open Aeneas Aeneas.Std Result

def toR137 (t : AspisR86Query.transcript.Transcript) :
    AspisR137Q22.transcript.Transcript :=
  ⟨t.state, t.hash⟩

def frame (s : Array U8 32#usize) (tag : U8) : Array U8 33#usize :=
  ⟨s.val ++ [tag], by
    simp only [List.length_append, List.length_singleton, s.property]
    rfl⟩

def message (s : Array U8 32#usize) (tag : U8) : Slice (Slice U8) :=
  Array.to_slice (Array.make 1#usize [Array.to_slice (frame s tag)])

theorem r137_execution (s : AspisR137Q22.transcript.Transcript) :
    AspisR137Q22.transcript.Transcript.squeeze_block s = (do
      let out ← s.hash (message s.state 1#u8)
      let next ← s.hash (message s.state 2#u8)
      ok (out, {s with state := next})) := by
  have hs : s.state.val.length = 32 := s.state.property
  have ht : s.state.val.take 32 = s.state.val := List.take_of_length_le (by omega)
  simp [AspisR137Q22.transcript.Transcript.squeeze_block,
    core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    Array.repeat, Array.to_slice, Slice.length, Slice.len,
    core.slice.Slice.copy_from_slice, Array.from_slice, List.setSlice!,
    List.slice, Array.update, AspisR137Q22.transcript.DOM_SQUEEZE,
    AspisR137Q22.transcript.DOM_ADVANCE, message, frame, Array.make,
    lift, bind_tc_ok, hs, List.set_append, ht]

theorem r86_execution (s : AspisR86Query.transcript.Transcript) :
    AspisR86Query.transcript.Transcript.squeeze_block s = (do
      let out ← s.hash (message s.state 1#u8)
      let next ← s.hash (message s.state 2#u8)
      ok (out, {s with state := next})) := by
  have hs : s.state.val.length = 32 := s.state.property
  have ht : s.state.val.take 32 = s.state.val := List.take_of_length_le (by omega)
  simp [AspisR86Query.transcript.Transcript.squeeze_block,
    core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    Array.repeat, Array.to_slice, Slice.length, Slice.len,
    core.slice.Slice.copy_from_slice, Array.from_slice, List.setSlice!,
    List.slice, Array.update, AspisR86Query.transcript.DOM_SQUEEZE,
    AspisR86Query.transcript.DOM_ADVANCE, message, frame, Array.make,
    lift, bind_tc_ok, hs, List.set_append, ht]

theorem squeeze_map (t : AspisR86Query.transcript.Transcript) :
    AspisR137Q22.transcript.Transcript.squeeze_block (toR137 t) = (do
      let (block, next) ← AspisR86Query.transcript.Transcript.squeeze_block t
      ok (block, toR137 next)) := by
  cases t with
  | mk state hash =>
      rw [r137_execution, r86_execution]
      simp only [toR137]
      simp only [bind_assoc_eq]
      simp only [bind_tc_ok]

#print axioms r137_execution
#print axioms r86_execution
#print axioms squeeze_map

end AspisV8R19.R147QuerySqueezeBridge
