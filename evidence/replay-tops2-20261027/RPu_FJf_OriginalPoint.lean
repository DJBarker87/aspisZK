import RPt_FJf_PointBody
set_option autoImplicit false
namespace AspisR1.FJf_OriginalPoint
open Aeneas Aeneas.Std Result
open FJc_WeightQMBridge (SQ)
/-- The first point returned by the actual constructor helper is the original
array, before successor carry or absorption flips. -/
theorem value (alpha : Array SQ 10#usize) (points : FJf_PointBody.Points)
    (run : FIn_WeightsExtract.state_only_prefix.r0.statement_points alpha=ok points) :
    Array.index_usize points 0#usize=ok alpha := by
  unfold FIn_WeightsExtract.state_only_prefix.r0.statement_points
    FIn_WeightsExtract.state_only_prefix.state_only_statement_points at run
  obtain ⟨s,hs,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨iter,hi,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨successor,hsc,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q,hq,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q1,hq1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨abs,habs,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q2,hq2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q3,hq3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨abs1,habs1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases Result.ok.inj run
  rfl
#print axioms value
end AspisR1.FJf_OriginalPoint
