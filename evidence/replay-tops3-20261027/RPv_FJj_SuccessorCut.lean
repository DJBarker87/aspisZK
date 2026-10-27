import RPv_FJj_SuccessorCell
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_SuccessorCut
open Aeneas Aeneas.Std Result
open FJc_WeightQMBridge (SQ)

theorem value (alpha : Array SQ 10#usize) (points : FJf_PointBody.Points)
    (run : FIn_WeightsExtract.state_only_prefix.r0.statement_points alpha=ok points) :
    ∃ (iter : FJj_SuccessorCell.Rev) (successor : Array SQ 10#usize),
      core.iter.traits.iterator.Iterator.rev.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
        {start:=0#usize,«end»:=Slice.len (Array.to_slice alpha)}=ok iter ∧
      FIn_WeightsExtract.state_only_prefix.state_only_statement_points_loop iter alpha alpha
        FIn_WeightsExtract.field.QM31.ONE=ok successor ∧
      Array.index_usize points 1#usize=ok successor := by
  unfold FIn_WeightsExtract.state_only_prefix.r0.statement_points
    FIn_WeightsExtract.state_only_prefix.state_only_statement_points at run
  obtain ⟨s,hs,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have es : s=Array.to_slice alpha := (Result.ok.inj hs).symm
  subst s
  obtain ⟨iter,hi,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨successor,hsc,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q,hq,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q1,hq1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨abs,habs,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q2,hq2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q3,hq3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨abs1,habs1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases Result.ok.inj run
  exact ⟨iter,successor,hi,hsc,rfl⟩
#print axioms value
end AspisR1.FJj_SuccessorCut
end
