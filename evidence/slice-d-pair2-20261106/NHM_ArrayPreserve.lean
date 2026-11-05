import NHM_ArrayCanon
import NHI_ArrayCells
set_option autoImplicit false
namespace NHM_ArrayPreserve
open Aeneas Aeneas.Std Result

theorem canonical {T : Type} {n : Usize} (P : T→Prop) (a b : Array T n)
 (i : Usize) (value : T) (before : ∀ x∈a.val,P x) (hv : P value)
 (run : Array.update a i value=ok b) : ∀ x∈b.val,P x := by
 unfold Array.update at run
 split at run
 · cases run
 · cases Result.ok.inj run
   exact NHI_CellCanon.list_set P a.val i.val value before hv

theorem frame {T : Type} {n : Usize} (a b : Array T n) (i : Usize) (value : T)
 (run : Array.update a i value=ok b) (j : Nat) (different : j≠i.val) : b.val[j]?=a.val[j]? := by
 unfold Array.update at run
 split at run
 · cases run
 · cases Result.ok.inj run
   simp only [List.getElem?_set]
   split <;> simp_all

#print axioms canonical
#print axioms frame
end NHM_ArrayPreserve
