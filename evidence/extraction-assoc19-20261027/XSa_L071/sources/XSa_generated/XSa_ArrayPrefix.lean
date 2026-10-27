import XSa_ClaimSumJoin
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSa_ArrayPrefix

theorem write {A : Type} {N : Usize} (a : Array A N) (i : Usize) (x : A) (hi : i.val<N.val) :
 (a.set i x).val.take (i.val+1)=a.val.take i.val++[x] := by
 rw [Array.set_val_eq]
 rw [List.take_succ_eq_append_getElem (by simpa only [List.length_set,a.property] using hi),List.take_set]
 rw [List.set_eq_of_length_le (by simp only [List.length_take];omega)]
 simp only [List.getElem_set_self]

theorem last {A : Type} {N : Usize} (a : Array A N) (i : Usize) (x : A)
 (hi : i.val+1=N.val) : (a.set i x).val=a.val.take i.val++[x] := by
 have h := write a i x (by omega)
 have hl : (a.set i x).val.length=i.val+1 := by rw [(a.set i x).property,hi]
 rw [←hl,List.take_length] at h
 exact h

#print axioms write
#print axioms last
end XSa_ArrayPrefix
