import RPv_FJb_QmRoundStep
import RPv_JFy_Specs
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_QmStepTotal
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical)
open FJb_QmRoundStep (State)
theorem source (a s : State) (i : Usize) (hi : i.val<16)
    (ha : canonical a) (hs : canonical s) :
    ∃ out,FJb_QmRoundStep.step a s i=ok out ∧ canonical out := by
  obtain ⟨x,rx,cx⟩ := JFy_ArrayTotal.read s i hi hs
  obtain ⟨y,ry,cy⟩ := JFy_ArrayTotal.read a i hi ha
  obtain ⟨q,rq,cq,_⟩ := FIv_PreparedTotal.add x y cx cy
  obtain ⟨q5,rq5,cq5,_⟩ := JFy_Pow5.source q cq
  obtain ⟨out,ro,co⟩ := JFy_ArrayTotal.update s i q5 hi hs cq5
  exact ⟨out,by simp only [FJb_QmRoundStep.step,rx,ry,rq,rq5,ro,bind_tc_ok],co⟩
#print axioms source
end AspisR1.JGj_QmStepTotal
end
