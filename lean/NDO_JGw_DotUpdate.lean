import RPt_JFs_TX2_Update
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_DotUpdate
open Aeneas Aeneas.Std Result
/-- Existing arithmetic bounds applied to an arbitrary canonical scalar read. -/
theorem source (term : Fin 26) (scalar : U32) (canonical : scalar.val<2147483647)
    (sums : Array U64 8#usize) (n : Nat) (hn : n<4)
    (hs : JFs_TX2_ArrayEight.Bound sums n) :
    ∃ out, JFr_TX2_DotStep.update JFr_TX2_FirstLane.native
      (JFr_TX2_DotTerm.cursor term.val (by have:=term.isLt;omega)) scalar sums=ok out ∧
      JFs_TX2_ArrayEight.Bound out (n+1) := by
  obtain ⟨out,run,bound⟩ := JFs_TX2_ArrayEight.source (JFr_TX2_FirstLane.limbs term)
    scalar sums n (JFs_TX2_Update.limbs term) canonical hn hs
  refine ⟨out,?_,bound⟩
  rw [JFr_TX2_DotLanes.update,JFs_TX2_ArrayRead.powers]
  simpa only [bind_tc_ok,FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs,
    JFr_TX2_FirstLane.limbs] using run
#print axioms source
end AspisR1.JGw_DotUpdate
end
