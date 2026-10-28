import NDO_JHa_DotContext
import RPt_JFv_TX2_ArrayMeaning
import RPt_JFs_TX2_Update
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_DotUpdateMeaning
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)

theorem source (d : JHa_DotContext.Data) (term : Fin 26)
    (sums : Array U64 8#usize) (n : Nat) (hn : n<4)
    (hs : JFs_TX2_ArrayEight.Bound sums n) :
    ∃ out, JFr_TX2_DotStep.update JFr_TX2_FirstLane.native
      (JFr_TX2_DotTerm.cursor term.val (by have:=term.isLt;omega))
      (d.scalars term) sums=ok out ∧ JFs_TX2_ArrayEight.Bound out (n+1) ∧
      ∀ j : Fin 8, (cell out j).val=(cell sums j).val+
        (cell (JFr_TX2_FirstLane.limbs term) j).val*(d.scalars term).val := by
  obtain ⟨out,run,bound,values⟩ := JFv_TX2_ArrayMeaning.source (JFr_TX2_FirstLane.limbs term)
    (d.scalars term) sums n (JFs_TX2_Update.limbs term)
    (d.canonical term) hn hs
  refine ⟨out,?_,bound,values⟩
  rw [JFr_TX2_DotLanes.update,JFs_TX2_ArrayRead.powers]
  simpa only [bind_tc_ok,FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs,
    JFr_TX2_FirstLane.limbs] using run
#print axioms source
end AspisR1.JHa_DotUpdateMeaning
end
