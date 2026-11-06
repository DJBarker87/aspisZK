import NKO_C06Result
import NKO_PowersResult
import NGM_QueryExit
set_option autoImplicit false
noncomputable section
namespace NKO_QueryPost
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages
/-- Internal actual-query bind law. All domains are derived from the same
resume fields and pending/powers calls; none becomes a new root premise. -/
theorem returned (rr : NP6_StdModel.Reservation) (proof : Slice U8)
 (p : verifier.Prepared) (a after : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (geometry : verifier.QueryGeometry) (b pending : verifier.BatchedWeights)
 (fields : NID_ResumeFields.Domain p a) (start : a.next=10#usize)
 (powers : NHT_PacketOps.powers 29#usize p.gamma=ok g)
 (allocation : NJJ_Common.pending rr a.weights.deref=ok (.Ok b))
 (query : NJJ_Common.query proof p a g none geometry b 22#usize=ok (.Ok (after,pending))) :
 NFS_QueryInvariant.Domain p 10 22 after pending ∧ after.next.val=22 := by
 have same := NKO_C06.pending_eq rr a fields.width b allocation
 subst b
 obtain ⟨native,nativeCall,sameG⟩ := NKO_PowersResult.returned p.gamma g powers
 subst g
 have initial := NFW_QueryResume.domain p a fields.width
  (NID_ResumeQuery.weights a fields.weights)
  (NID_ResumeCallerDomain.wide a.rhs fields.rhs)
  (NID_ResumeCallerDomain.power a.power fields.power)
  (NID_ResumeCallerDomain.power p.rho fields.rho) (by rw [start];rfl)
 have source := NHT_PacketOps.query_source NJJ_QueryOps.concrete proof p a fields.width
  (NID_ResumeQuery.weights a fields.weights)
  (NID_ResumeCallerDomain.wide a.rhs fields.rhs)
  (NID_ResumeCallerDomain.power a.power fields.power)
  (NID_ResumeCallerDomain.power p.rho fields.rho) (by rw [start];rfl)
  (FIo_Install.toE p.gamma) (NID_ResumeCallerDomain.gamma p.gamma fields.gamma)
  native nativeCall geometry 0 0
 change NHT_PacketOps.query NJJ_QueryOps.concrete 0 0 proof p a
  (FIp_DotsAdapter.fromArray native) none geometry (NFW_QueryResume.pending a)
  22#usize=ok (.Ok (after,pending)) at query
 rw [source] at query
 have actual := NKE_ResumeDomain.action_ok _ _ query
 exact NGM_QueryExit.tx2 NJJ_QueryOps.concrete proof p a after
  (FIp_DotsAdapter.fromArray native) geometry (NFW_QueryResume.pending a) pending
  initial (by rw [start];rfl) actual

theorem widths (rr : NP6_StdModel.Reservation) (proof : Slice U8)
 (p : verifier.Prepared) (a after : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (geometry : verifier.QueryGeometry) (b pending : verifier.BatchedWeights)
 (fields : NID_ResumeFields.Domain p a) (start : a.next=10#usize)
 (powers : NHT_PacketOps.powers 29#usize p.gamma=ok g)
 (allocation : NJJ_Common.pending rr a.weights.deref=ok (.Ok b))
 (query : NJJ_Common.query proof p a g none geometry b 22#usize=ok (.Ok (after,pending))) :
 pending.raw.val.length=64 ∧ after.weights.val.length=64 := by
 have post := (returned rr proof p a after g geometry b pending fields start powers allocation query).1
 exact ⟨post.progress.2.1,post.width⟩
#print axioms returned
#print axioms widths
end NKO_QueryPost
