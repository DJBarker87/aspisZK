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
    have hlen : c1.val.length = 104 := c1.property
    rw [List.length_take]
    simp only [Nat.min_eq_left (by omega)]
    rw [List.length_drop]
    omega)

lemma c1Chunk_val (c1 : Array U32 104#usize) (slot : U4) :
    (c1Chunk c1 slot).val = c1.val.drop (26 * slot.val) |>.take 26 := rfl

#check core.array.TryFromSharedArraySlice.try_from
#check core.array.Array.index
#check core.ops.index.IndexSlice
#check core.slice.index.SliceIndexRangeUsizeSlice

end AspisV8R19.R646CombineLoopExecution
