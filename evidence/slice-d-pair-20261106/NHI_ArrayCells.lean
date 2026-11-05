import NHI_ScalarDomain
set_option autoImplicit false
namespace NHI_ArrayCells
open Aeneas Aeneas.Std Result

def put {T : Type} {n : Usize} (a : Array T n) (i : Usize) (x : T) : Array T n :=
 ⟨a.val.set i.val x,by simpa only [List.length_set] using a.property⟩

theorem update {T : Type} {n : Usize} (a : Array T n) (i : Usize) (x : T)
 (hi : i.val<n.val) : Array.update a i x=ok (put a i x) := by
 have h : i.val<a.val.length := by rw [a.property];exact hi
 simp [Array.update,put,h]

theorem frame {T : Type} {n : Usize} (a : Array T n) (i : Usize) (x : T)
 (j : Nat) (different : j≠i.val) : (put a i x).val[j]?=a.val[j]? := by
 simp only [put,List.getElem?_set]
 split <;> simp_all

theorem selected {T : Type} {n : Usize} (a : Array T n) (i : Usize) (x : T)
 (hi : i.val<n.val) : (put a i x).val[i.val]?=some x := by
 have h : i.val<a.val.length := by rw [a.property];exact hi
 simp [put,List.getElem?_set,h]

#print axioms update
#print axioms frame
#print axioms selected
end NHI_ArrayCells
