import Aeneas
set_option autoImplicit false
namespace NEC_HeaderIndex
open Aeneas Aeneas.Std Result
#print instGetElem?ArrayUsizeLtNatValLengthValListEq

theorem index_read {α : Type} {n : Usize} (a : Array α n) (i : Usize) (hi : i.val<n.val) :
 Array.index_usize a i=ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
 unfold Aeneas.Std.Array at a
 rcases a with ⟨values,length⟩
 have bound : i.val<values.length := by simpa [length] using hi
 unfold Array.index_usize
 change (match values[i.val]? with
   | none=>Result.fail Error.arrayOutOfBounds
   | some value=>Result.ok value)=ok (values[i.val]'bound)
 rw [List.getElem?_eq_getElem bound]

#print axioms index_read
end NEC_HeaderIndex
