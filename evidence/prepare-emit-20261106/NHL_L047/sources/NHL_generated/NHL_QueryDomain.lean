import NHL_PreparedRecompose
import NFW_PrepareQuery
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHL_QueryDomain
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NFW_PreparedControl
open NHL_PreparedScalars

theorem dictionary : actual=
 AspisR1ClaimPreparedBridge.concreteBoundaries
   (AspisR1ClaimPreparedBridge.withCandidateSamplers actual.sampling) := by
 simp only [actual,NGT_NBA_Installed.actual,AspisR1ClaimPreparedBridge.concreteBoundaries,
   AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries,
   PreparedFromQmSourceBridge.withSourceFromQm,AspisR1ClaimPreparedBridge.CurrentQueryRho.withConcreteQueries,
   AspisR1ClaimPreparedBridge.withCandidateSamplers,AspisR1ClaimPreparedBridge.withCandidateGamma,
   AspisR1Post25SamplerOrdinaryCallbackV2.withCandidateOrdinary]
 rfl

/-- The NEW emitted producer result supplies both domains of the CLOSED NFS
consumer. This is a model implication, never a native whole-output premise.
NHL_PreparedRecompose.source constructs this input on its explicit packet domain. -/
theorem emitted {H : Type} (D : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
 (old scratch : Scratch) (out : verifier.Prepared)
 (producer : NGN_Emitted.prepared actual D sem v hash old=ok (.Ok out,scratch))
 (base : Port3_NativeQueryBody.Ops) (proof : Slice U8)
 (geometry : AspisR1Stage2.verifier.QueryGeometry) (qPlace gPlace : Nat) :
 NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray (NFW_PreparedPort.map NFW_PreparedPort.e scratch)) ∧
 NFS_QueryInvariant.Domain (NFW_PreparedPort.prepared out) 0 10 NFW_QueryEntry.initial NFW_QueryEntry.pending ∧
 NFG_QueryLoopDefs.run
   (NFS_QueryLoopRoot.child base proof (NFW_PreparedPort.prepared out)
     (NFW_PreparedPort.map NFW_PreparedPort.e scratch) geometry qPlace gPlace)
   10#usize 10 (.Ok (NFW_QueryEntry.initial,NFW_QueryEntry.pending)) =
 AspisR1Stage2.verifier.candidate.query_loop (NFS_QueryOps.installed base) proof
   (NFW_PreparedPort.prepared out) NFW_QueryEntry.initial (NFW_PreparedPort.map NFW_PreparedPort.e scratch)
   none geometry NFW_QueryEntry.pending 10#usize := by
 have model := (NGN_EmittedEq.source actual D sem v hash old).symm.trans producer
 rw [dictionary] at model
 have domains := NFW_PrepareQuery.domains actual.sampling D sem v hash out scratch old model
 exact ⟨domains.1,domains.2,NFW_PrepareQuery.tx1 actual.sampling D sem v hash out scratch old
   model base proof geometry qPlace gPlace⟩
#print axioms dictionary
#print axioms emitted
end AspisR1.NHL_QueryDomain
