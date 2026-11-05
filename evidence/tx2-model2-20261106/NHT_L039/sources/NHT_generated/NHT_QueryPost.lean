import NHT_PacketOps
import NHT_ResultSuccess
set_option autoImplicit false
noncomputable section
namespace NHT_QueryPost
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
/-- Exact poststate of the SAME mapped query packet. Resume primitive domains
are explicit; the query output, pending and flush output are never reselected. -/
theorem finish_domain (base : Port3_NativeQueryBody.Ops)
 (proof : Slice U8) (p : verifier.Prepared) (a after : verifier.Accumulator)
 (width : a.weights.val.length=64)
 (weights : NFS_NEV_WeightDomains.Canonical (NEV_AccumulateCarriers.fromAccumulator a).weights)
 (rhs : NBO_TailDomain.WideCanonical a.rhs) (power : NBF_PowerStep.Canonical a.power)
 (rho : NBF_PowerStep.Canonical p.rho) (start : a.next.val=10)
 (gamma : NFN_LPi_FieldValues.NE) (canonicalGamma : NFN_LPi_FieldValues.canonE gamma)
 (g : Array NFN_LPi_FieldValues.NE 29#usize)
 (powers : FIo_Native.weights.powers 29#usize gamma=ok g)
 (geometry : verifier.QueryGeometry) (qPlace gPlace : Nat)
 (pending : verifier.BatchedWeights)
 (returned : NHT_PacketOps.query base qPlace gPlace proof p a
   (FIp_DotsAdapter.fromArray g) none geometry (NFW_QueryResume.pending a) 22#usize=
   ok (.Ok (after,pending))) :
 ∃ out : Slice aspis_core.field.QM31,
 Port3_FlushInstall.flush pending after.weights.deref=ok out ∧
 NGM_FinishDomain.AccumulatorDomain {after with weights:=⟨out.val,out.property⟩} ∧
 ({after with weights:=⟨out.val,out.property⟩} : verifier.Accumulator).rhs=after.rhs ∧
 ({after with weights:=⟨out.val,out.property⟩} : verifier.Accumulator).power=after.power ∧
 ({after with weights:=⟨out.val,out.property⟩} : verifier.Accumulator).next=after.next := by
 rw [NHT_PacketOps.query_source base proof p a width weights rhs power rho start
   gamma canonicalGamma g powers geometry qPlace gPlace] at returned
 have native := NHT_ResultSuccess.source _ (after,pending) returned
 exact NGM_FinishDomain.tx2_writeback base proof p a after (FIp_DotsAdapter.fromArray g)
   geometry (NFW_QueryResume.pending a) pending
   (NFW_QueryResume.domain p a width weights rhs power rho start) start native
#print axioms finish_domain
end NHT_QueryPost
