import NJB_StubLaws
set_option autoImplicit false
namespace AspisR1.NJB_ArrayReads
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (decode)
theorem read {α : Type} {N : Usize} (a : Array α N) (i : Usize) (bound : i.val<N.val) :
 Array.index_usize a i=ok (a.val[i.val]'(by rw [a.property];exact bound)) := by
 have h : i.val<a.val.length := by rw [a.property];exact bound
 unfold Array.index_usize
 change (match a.val[i.val]? with | none=>fail Error.arrayOutOfBounds | some x=>ok x)=_
 rw [List.getElem?_eq_getElem h]
theorem value {N : Usize} (a : Array NQ N) (n : Nat) (bound : n<a.val.length) :
 FIv_NativeArray.value a n=decode (a.val[n]'bound) := by
 simp only [FIv_NativeArray.value,List.getElem?_eq_getElem bound]
#print axioms read
#print axioms value
end AspisR1.NJB_ArrayReads
