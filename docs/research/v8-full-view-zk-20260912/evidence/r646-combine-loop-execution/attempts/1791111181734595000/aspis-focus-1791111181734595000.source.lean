import AspisR614SelectedCombineBeta.Funs
import AspisV8R19.GeneratedInverseLoop
import Mathlib.Tactic

set_option autoImplicit false

namespace AspisV8R19.R646CombineLoopExecution

open Aeneas Aeneas.Std Result ControlFlow
open AspisR614SelectedCombineBeta

private abbrev U4 := Fin 4

/-- The selected 26-word C1 chunk, expressed as the exact drop/take slice. -/
def c1Chunk (c1 : Array U32 104#usize) (slot : U4) : Array U32 26#usize :=
  Array.make 26#usize (c1.val.drop (26 * slot.val) |>.take 26) (by
    have hlen : c1.val.length = 104 := by
      have h := c1.property
      have hu : (104#usize : Usize).val = 104 := by scalar_tac
      simpa only [hu] using h
    rw [List.length_take, List.length_drop, hlen]
    have hbound : 26 ≤ 104 - 26 * slot.val := by omega
    rw [Nat.min_eq_left hbound]
    have h26 : (26#usize : Usize).val = 26 := by scalar_tac
    simpa only [h26])

lemma c1Chunk_val (c1 : Array U32 104#usize) (slot : U4) :
    (c1Chunk c1 slot).val = (c1.val.drop (26 * slot.val)).take 26 := rfl

#check core.array.TryFromSharedArraySlice.try_from
#check core.array.Array.index
#check core.ops.index.IndexSlice
#check core.slice.index.SliceIndexRangeUsizeSlice

end AspisV8R19.R646CombineLoopExecution
