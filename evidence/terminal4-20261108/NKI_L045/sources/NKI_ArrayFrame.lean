import NJB_ArrayCarrier
import RPv_FIy_ArraySlot
set_option autoImplicit false
namespace AspisR1.NKI_ArrayFrame
open Aeneas Aeneas.Std Result
theorem read {A : Type} {N : Usize} (a : Array A N) (i : Usize) (j : Fin N.val) (x : A)
 (same : i.val=j.val) (call : Array.index_usize a i=ok x) :
 x=NJB_ArrayCarrier.cell a j := by
 have h:=FIy_ArraySlot.value a i x call
 have bound : j.val<a.val.length := by rw [a.property];exact j.isLt
 rw [same,List.getElem?_eq_getElem bound] at h
 exact (Option.some.inj h).symm
/-- Raw full-carrier write/frame law, no payload inferred from an address. -/
theorem update {A : Type} {N : Usize} (a b : Array A N) (i : Usize) (x : A)
 (call : Array.update a i x=ok b) (j : Fin N.val) :
 NJB_ArrayCarrier.cell b j=if i.val=j.val then x else NJB_ArrayCarrier.cell a j := by
 unfold Array.update at call
 split at call
 · cases call
 · have same:=Result.ok.inj call
   subst b
   simp only [NJB_ArrayCarrier.cell,List.getElem_set]
#print axioms read
#print axioms update
end AspisR1.NKI_ArrayFrame
