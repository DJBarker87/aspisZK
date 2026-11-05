import NGM_QueryExit
import NGM_NGC_FinishFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGM_FinishDomain
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
/-- Only the accumulator part of the tail domain. Prepared and proof-view
provenance remain separate obligations of the TX2 producer. -/
structure AccumulatorDomain (a : verifier.Accumulator) : Prop where
 width : a.weights.val.length=64
 canonical : ∀ q∈a.weights.val,Port3_FlushInstall.Canonical q
 rhs : NBO_TailDomain.WideCanonical a.rhs
 power : NBF_PowerStep.Canonical a.power
 next : a.next.val=22

/-- Derives the finish input from the same query-loop output and total
write-back. There is no assumed successful finish call or output equality. -/
theorem tx2_writeback (base : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a after : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (geometry : verifier.QueryGeometry) (b pending : verifier.BatchedWeights)
 (domain : NFS_QueryInvariant.Domain p 10 22 a b) (start : a.next.val=10)
 (accepted : verifier.candidate.query_loop (NFS_QueryOps.installed base)
  proof p a g none geometry b 22#usize=ok (.Ok (after,pending))) :
 ∃ out : Slice aspis_core.field.QM31,
 Port3_FlushInstall.flush pending after.weights.deref=ok out ∧
 AccumulatorDomain {after with weights:=⟨out.val,out.property⟩} ∧
 ({after with weights:=⟨out.val,out.property⟩} : verifier.Accumulator).rhs=after.rhs ∧
 ({after with weights:=⟨out.val,out.property⟩} : verifier.Accumulator).power=after.power ∧
 ({after with weights:=⟨out.val,out.property⟩} : verifier.Accumulator).next=after.next := by
 obtain ⟨post,next⟩ := NGM_QueryExit.tx2 base proof p a after g geometry b pending domain start accepted
 obtain ⟨out,run,len,canonical,frame⟩ := NGC_FinishFrame.result_frame p 10 22 after pending post
 exact ⟨out,run,⟨len,canonical,post.rhs,post.power,next⟩,frame⟩
#print axioms tx2_writeback
end AspisR1.NGM_FinishDomain
end
