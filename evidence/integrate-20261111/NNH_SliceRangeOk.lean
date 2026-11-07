import NNH_ResultWp
import NND_Carrier
set_option autoImplicit false
namespace NNH_SliceRangeOk
open Aeneas Aeneas.Std NND_Carrier

theorem value (xs : Slice U8) (start stop : Usize) (ordered : start≤stop) (bounded : stop.val≤xs.length) :
 ∃ out,core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) xs ⟨start,stop⟩=.ok out ∧
 bytes out=RSL.slice (bytes xs) start.val stop.val := by
 obtain ⟨out,run,same,length⟩ := NNH_ResultWp.expose _ _ (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec ⟨start,stop⟩ xs ordered bounded)
 refine ⟨out,run,?_⟩
 unfold bytes RSL.slice
 rw [same]
 simp only [List.slice,List.map_take,List.map_drop]
#print axioms value
end NNH_SliceRangeOk
