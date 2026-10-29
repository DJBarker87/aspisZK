import Aeneas
set_option autoImplicit false
namespace NEC_HeaderIndex
open Aeneas Aeneas.Std Result
#print instGetElem?ArrayUsizeLtNatValLengthValListEq

theorem index_read {α : Type} {n : Usize} (a : Array α n) (i : Usize) (hi : i.val<n.val) :
 Array.index_usize a i=ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
 have hidx : i.val<a.val.length := by simpa [a.property] using hi
 unfold Array.index_usize
 simp only [getElem?,instGetElem?ArrayUsizeLtNatValLengthValListEq]
 rw [List.getElem?_eq_getElem hidx]

#print axioms index_read
end NEC_HeaderIndex
