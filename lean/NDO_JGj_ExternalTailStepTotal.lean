import NDO_JGj_ExternalTailRowTotal
import RPv_FJb_TailStep
import RPv_JFy_ArrayTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_ExternalTailStepTotal
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical)
open FJb_MatrixGroupStep (State)
theorem source (s : State) (sums : FJb_ColumnTable.Table) (i : Usize)
    (hi : i.val<16) (hs : canonical s) (hb : FJb_TailCell.Bounded sums) :
    ∃ out,FJb_TailStep.step s sums i=ok out ∧ canonical out := by
  obtain ⟨q,rq,_⟩ := JFy_ArrayTotal.read s i hi hs
  obtain ⟨q1,rq1,cq1⟩ := JGj_ExternalTailRowTotal.source q sums i hb
  obtain ⟨out,ro,co⟩ := JFy_ArrayTotal.update s i q1 hi hs cq1
  exact ⟨out,by simp only [FJb_TailStep.step,rq,rq1,ro,bind_tc_ok],co⟩
#print axioms source
end AspisR1.JGj_ExternalTailStepTotal
end
