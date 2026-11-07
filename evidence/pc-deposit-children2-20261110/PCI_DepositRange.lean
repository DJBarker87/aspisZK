import PCI_DepositActual.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_DepositRange

def window {T : Type} (bytes : Slice T) (start last : Usize)
    (ordered : start≤last) (bounded : last.val≤bytes.length) : Slice T :=
  ⟨List.slice start.val last.val bytes.val, by
    have h := bytes.property
    have : (List.slice start.val last.val bytes.val).length≤bytes.val.length := by
      simp only [List.slice]
      exact le_trans (List.length_take_le _ _) (List.length_drop_le _ _)
    scalar_tac⟩

theorem index {T : Type} (bytes : Slice T) (start last : Usize)
    (ordered : start≤last) (bounded : last.val≤bytes.length) :
    core.slice.index.SliceIndexRangeUsizeSlice.index {start,«end»:=last} bytes=
      ok (window bytes start last ordered bounded) := by
  simp only [core.slice.index.SliceIndexRangeUsizeSlice.index,ordered,bounded,and_self,↓reduceIte]
  rfl

theorem length {T : Type} (bytes : Slice T) (start last : Usize)
    (ordered : start≤last) (bounded : last.val≤bytes.length) :
    (window bytes start last ordered bounded).length=last.val-start.val := by
  simp only [window,Slice.length,List.length_slice]
  scalar_tac

#print axioms index
#print axioms length
end PCI_DepositRange
