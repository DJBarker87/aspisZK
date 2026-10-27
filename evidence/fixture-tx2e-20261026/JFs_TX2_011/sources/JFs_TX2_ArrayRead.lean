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
  obtain ⟨x,run,same⟩ := WP.spec_imp_exists
    (Array.index_usize_spec JFr_TX2_FirstLane.native
      (JFr_TX2_DotTerm.cursor term.val (by have:=term.isLt;omega))
      (by change _ < JFr_TX2_FirstLane.native.val.length; rw [JFr_TX2_FirstLane.native.property]; have:=term.isLt; unfold JFr_TX2_DotTerm.cursor; scalar_tac))
  rw [same] at run
  simpa only [JFr_TX2_FirstLane.native,FIp_DotsAdapter.toArray,
    JFr_TX2_DotTerm.cursor,List.getElem_map,
    JFr_TX2_FirstLane.coefficient] using run

#print axioms source
#print axioms powers
end AspisR1.JFs_TX2_ArrayRead
end
