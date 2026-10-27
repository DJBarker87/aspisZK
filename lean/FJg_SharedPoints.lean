import FJf_ArraySlots

import FJf_OriginalPoint
import FJc_WeightArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_SharedPoints
open Aeneas Aeneas.Std Result
open FJc_WeightQMBridge (SQ)
/-- Actual absorption point has precisely the two installed updates. All
other coordinates retain the original bytes, even without canonicality. -/
theorem source (alpha : Array SQ 10#usize) (points : FJf_PointBody.Points)
    (run : FIn_WeightsExtract.state_only_prefix.r0.statement_points alpha=ok points) :
    ∃ (p p' : Array SQ 10#usize) (q q' x x' : SQ),
      Array.index_usize points 2#usize=ok p' ∧
      Array.index_usize alpha 7#usize=ok q ∧
      FIn_WeightsExtract.field.QM31.sub FIn_WeightsExtract.field.QM31.ONE q=ok x ∧
      Array.update alpha 7#usize x=ok p ∧
      Array.index_usize p 6#usize=ok q' ∧
      FIn_WeightsExtract.field.QM31.sub FIn_WeightsExtract.field.QM31.ONE q'=ok x' ∧
      Array.update p 6#usize x'=ok p' ∧
      (∀ i,i≠6 → i≠7 → p'.val[i]?=alpha.val[i]?) := by
  unfold FIn_WeightsExtract.state_only_prefix.r0.statement_points
    FIn_WeightsExtract.state_only_prefix.state_only_statement_points at run
  obtain ⟨s,hs,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨iter,hi,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨successor,hsc,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q,hq,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨x,hx,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨p,hp,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q',hq',run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨x',hx',run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨p',hp',run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases Result.ok.inj run
  refine ⟨p,p',q,q',x,x',rfl,hq,hx,hp,hq',hx',hp',?_⟩
  intro i h6 h7
  rw [FJf_ArraySlots.update_slot p p' 6#usize x' hp' i,
    if_neg (by simpa only [show (6#usize).val=6 from by decide] using Ne.symm h6),
    FJf_ArraySlots.update_slot alpha p 7#usize x hp i,
    if_neg (by simpa only [show (7#usize).val=7 from by decide] using Ne.symm h7)]
#print axioms source
end AspisR1.FJg_SharedPoints
end
