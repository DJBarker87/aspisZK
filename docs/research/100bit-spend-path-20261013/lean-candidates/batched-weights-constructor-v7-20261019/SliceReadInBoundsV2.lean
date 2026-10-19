import AspisR1BatchedWeightsExtraction.Funs
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace SliceReadInBoundsV1
theorem read_success {α : Type} (s : Slice α) (i : Usize) (h : i.val < s.len.val) :
    ∃ x, Slice.index_usize s i = .ok x := by
  have hn : i.val < s.length := by simpa [Slice.len_val] using h
  refine ⟨s.val[i.val], ?_⟩
  simp [Slice.index_usize, hn]
end SliceReadInBoundsV1
