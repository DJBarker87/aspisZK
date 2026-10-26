import JFr_TX2_DotTerm

import JFr_TX2_FirstLane
import JFs_TX2_ArrayEight
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_ArrayRead
open Aeneas Aeneas.Std Result

theorem source {α : Type} {N : Usize} (a : Array α N) (j : Usize)
    (bound : j.val<N.val) :
    ∃ x, Array.index_usize a j=ok x ∧ x∈a.val := by
  let x := a.val[j.val]'(by rw [a.property];exact bound)
  refine ⟨x,?_,List.getElem_mem _⟩
  unfold Array.index_usize
  change (match a.val[j.val]? with | none => _ | some y => ok y)=ok x
  rw [List.getElem?_eq_getElem (by rw [a.property];exact bound)]

theorem powers (term : Fin 26) :
    Array.index_usize JFr_TX2_FirstLane.native (JFr_TX2_DotTerm.cursor term.val (by have:=term.isLt;omega))=
      ok (JFr_TX2_FirstLane.coefficient term) := by
  unfold Array.index_usize
  change (match (JFr_TX2_Powers.value.val.map FIo_Install.toE)[term.val]? with
    | none => _ | some y => ok y)=_
  rw [List.getElem?_map,List.getElem?_eq_getElem (by rw [JFr_TX2_Powers.value.property];change term.val<29;have:=term.isLt;omega)]
  rfl

#print axioms source
#print axioms powers
end AspisR1.JFs_TX2_ArrayRead
end
