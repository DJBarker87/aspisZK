import PCI_DepositActual.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_DepositSuffix

def suffix {T : Type} (bytes : Slice T) (start : Usize) : Slice T :=
 ⟨bytes.val.drop start.val,by have h:=bytes.property;simp only [List.length_drop];omega⟩

theorem index {T : Type} (bytes : Slice T) (start : Usize) (bound : start.val≤bytes.length) :
    core.slice.index.SliceIndexRangeFromUsizeSlice.index {start} bytes=ok (suffix bytes start) := by
 unfold core.slice.index.SliceIndexRangeFromUsizeSlice.index
 simp only [bound,ite_true]
 rfl

theorem length {T : Type} (bytes : Slice T) (start : Usize) :
    (suffix bytes start).length=bytes.length-start.val := by
 change (bytes.val.drop start.val).length=bytes.val.length-start.val
 exact List.length_drop

#print axioms index
#print axioms length
end PCI_DepositSuffix
