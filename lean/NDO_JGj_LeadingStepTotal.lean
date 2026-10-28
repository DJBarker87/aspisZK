import RPv_FJb_LeadingStep
import RPv_JFy_ArrayTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_LeadingStepTotal
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical)
open FJb_LeadingStep (State)
theorem source (a s : State) (i : Usize) (hi : i.val<16)
    (ha : canonical a) (hs : canonical s) :
    ∃ out,FJb_LeadingStep.step a s i=ok out ∧ canonical out := by
  obtain ⟨x,rx,cx⟩ := JFy_ArrayTotal.read s i hi hs
  obtain ⟨y,ry,cy⟩ := JFy_ArrayTotal.read a i hi ha
  obtain ⟨q,rq,cq,_⟩ := FIv_PreparedTotal.add x y cx cy
  obtain ⟨out,ro,co⟩ := JFy_ArrayTotal.update s i q hi hs cq
  exact ⟨out,by simp only [FJb_LeadingStep.step,rx,ry,rq,ro,bind_tc_ok],co⟩
#print axioms source
end AspisR1.JGj_LeadingStepTotal
end
