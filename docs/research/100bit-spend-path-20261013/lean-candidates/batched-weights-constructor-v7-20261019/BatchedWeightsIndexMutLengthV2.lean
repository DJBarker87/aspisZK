import AspisR1BatchedWeightsExtraction.Funs
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP
open AspisR1BatchedWeightsExtraction
namespace BatchedWeightsIndexMutLengthV2

abbrev Row := Array Std.U64 4#usize
abbrev Raw := alloc.vec.Vec Row

theorem index_mut_callback_length (raw : Raw) (i : Std.Usize)
    (row : Row) (back : Row → Raw)
    (h : alloc.vec.Vec.index_mut
      (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize)) raw i = .ok (row, back)) :
    ∀ row', (back row').length = raw.length := by
  intro row'
  simp only [alloc.vec.Vec.index_mut,
    core.slice.index.SliceIndexUsizeSlice,
    core.slice.index.Usize.index_mut,
    Slice.index_mut_usize] at h
  cases hread : Slice.index_usize (raw : Slice Row) i with
  | fail e => simp [hread] at h
  | div => simp [hread] at h
  | ok readRow =>
    simp only [hread, bind_tc_ok] at h
    injection h with hp
    rcases hp with ⟨_, hback⟩
    simp [alloc.vec.Vec.length, Slice.set, List.length_set]
#print axioms index_mut_callback_length
end BatchedWeightsIndexMutLengthV2
