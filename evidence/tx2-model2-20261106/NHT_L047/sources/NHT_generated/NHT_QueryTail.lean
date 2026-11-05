import NHT_QueryPost
import NHT_TailView
set_option autoImplicit false
noncomputable section
namespace NHT_QueryTail
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
abbrev TopOps := VTop_Stages.Ops
abbrev Packet := verifier.View → verifier.Prepared → verifier.Accumulator →
 Option (VTop_Stages.verifier.Phase → Result Unit) →
 Result (core.result.Result Unit VTop_Stages.verifier.Error)

theorem source (top : TopOps) (base : Port3_NativeQueryBody.Ops)
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
   ok (.Ok (after,pending)))
 (inactive : aspis_core.field.wide_exact.WideExact) (round0 folded round1 : Usize)
 (packet : Packet)
 (NHM_finish : ∀ out : Slice aspis_core.field.QM31,
   Port3_FlushInstall.flush pending after.weights.deref=ok out →
   NGM_FinishDomain.AccumulatorDomain {after with weights:=⟨out.val,out.property⟩} →
   ∀ v, NHT_TailView.view (NHT_PacketOps.installed top base qPlace gPlace)
     proof p none inactive round0 folded round1=ok v →
   top.op19 v p {after with weights:=⟨out.val,out.property⟩} none=
     packet v p {after with weights:=⟨out.val,out.property⟩} none) :
 ∃ out : Slice aspis_core.field.QM31,
 Port3_FlushInstall.flush pending after.weights.deref=ok out ∧
 NGM_FinishDomain.AccumulatorDomain {after with weights:=⟨out.val,out.property⟩} ∧
 NHQ_Tx2CommonModel.afterQuery (NHT_PacketOps.installed top base qPlace gPlace)
   proof p none inactive round0 folded round1 (.Ok (after,pending)) =
 (do let v ← NHT_TailView.view (NHT_PacketOps.installed top base qPlace gPlace)
       proof p none inactive round0 folded round1
     packet v p {after with weights:=⟨out.val,out.property⟩} none) := by
 obtain ⟨out,flush,domain,_⟩ := NHT_QueryPost.finish_domain base proof p a after width
   weights rhs power rho start gamma canonicalGamma g powers geometry qPlace gPlace pending returned
 refine ⟨out,flush,domain,?_⟩
 rw [NHT_TailCall.after_query _ _ _ _ _ _ _ _ _ _ out flush]
 apply NHT_TailView.finish_packet
 intro v reached
 exact NHM_finish out flush domain v reached
#print axioms source
end NHT_QueryTail
