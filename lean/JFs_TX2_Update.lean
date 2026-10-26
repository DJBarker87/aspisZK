import JFs_TX2_ArrayRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_Update
open Aeneas Aeneas.Std Result

theorem limbs (term : Fin 26) : JFs_TX2_ArrayEight.Canon (JFr_TX2_FirstLane.limbs term) := by
  have h := JFr_TX2_Powers.canonical ⟨term.val,by have:=term.isLt;omega⟩
  intro x hx
  change x∈[_,_,_,_,_,_,_,_] at hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.1.1.1
  · exact h.1.1.2
  · exact h.1.2.1
  · exact h.1.2.2
  · exact h.2.1.1
  · exact h.2.1.2
  · exact h.2.2.1
  · exact h.2.2.2

theorem source (i : Fin 12) (slot : Fin 4) (term : Fin 26)
    (sums : Array U64 8#usize) (n : Nat) (hn : n<4)
    (hs : JFs_TX2_ArrayEight.Bound sums n) :
    ∃ out, JFr_TX2_DotStep.update JFr_TX2_FirstLane.native
      (JFr_TX2_DotTerm.cursor term.val (by have:=term.isLt;omega))
      ((JFr_TX2_Scalars.values i slot).val[term.val]'(by rw [(JFr_TX2_Scalars.values i slot).property];exact term.isLt)) sums=ok out ∧
      JFs_TX2_ArrayEight.Bound out (n+1) := by
  obtain ⟨out,run,bound⟩ := JFs_TX2_ArrayEight.source (JFr_TX2_FirstLane.limbs term)
    ((JFr_TX2_Scalars.values i slot).val[term.val]'(by rw [(JFr_TX2_Scalars.values i slot).property];exact term.isLt))
    sums n (limbs term) (JFr_TX2_Scalars.canonical i slot term) hn hs
  refine ⟨out,?_,bound⟩
  rw [JFr_TX2_DotLanes.update,JFs_TX2_ArrayRead.powers]
  simpa only [bind_tc_ok,FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs,
    JFr_TX2_FirstLane.limbs] using run

#print axioms limbs
#print axioms source
end AspisR1.JFs_TX2_Update
end
