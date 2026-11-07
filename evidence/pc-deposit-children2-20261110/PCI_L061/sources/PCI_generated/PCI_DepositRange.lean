import PCI_DepositActual.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_DepositRange

def window {T : Type} (bytes : Slice T) (start last : Usize)
    (ordered : start≤last) (bounded : last.val≤bytes.length) : Slice T :=
  ⟨List.slice start.val last.val bytes.val, by
    have h := bytes.property
    simp only [List.slice,List.length_take,List.length_drop]
    omega⟩

theorem index {T : Type} (bytes : Slice T) (start last : Usize)
    (ordered : start≤last) (bounded : last.val≤bytes.length) :
    core.slice.index.SliceIndexRangeUsizeSlice.index {start,«end»:=last} bytes=
      ok (window bytes start last ordered bounded) := by
  simp only [core.slice.index.SliceIndexRangeUsizeSlice.index,ordered,bounded,and_self,↓reduceIte]
  rfl

theorem length {T : Type} (bytes : Slice T) (start last : Usize)
    (ordered : start≤last) (bounded : last.val≤bytes.length) :
    (window bytes start last ordered bounded).length=last.val-start.val := by
  change (List.slice start.val last.val bytes.val).length=last.val-start.val
  have hs : start.val≤last.val := by scalar_tac
  simp only [List.slice,List.length_take,List.length_drop]
  omega

#print axioms index
#print axioms length
end PCI_DepositRange
