import Aeneas
set_option autoImplicit false
namespace NEC_HeaderIndex
open Aeneas Aeneas.Std Result
attribute [local reducible] Aeneas.Std.Array
#print instGetElem?ArrayUsizeLtNatValLengthValListEq

theorem index_read {α : Type} {n : Usize} (a : Array α n) (i : Usize) (hi : i.val<n.val) :
 Array.index_usize a i=ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
 have hidx : i.val<a.val.length := by simpa [a.property] using hi
 have hget := List.getElem?_eq_getElem hidx
 have lifted := congrArg (fun o : Option α => match o with
   | none=>Result.fail Error.arrayOutOfBounds
   | some value=>Result.ok value) hget
 simpa only [Array.index_usize,getElem?] using lifted

#print axioms index_read
end NEC_HeaderIndex
