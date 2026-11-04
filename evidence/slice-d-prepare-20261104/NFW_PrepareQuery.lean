import NFW_PreparedProducer
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFW_PrepareQuery
open Aeneas Aeneas.Std Result NFW_PreparedPort AspisR1Stage2 Port3_NativeQueryBody
/-- Complete primitive consumer domains from the SAME adopted Prepared and
scratch outputs. Native preparation is still the separately named producer
boundary. There is no independent canonicality or whole-output match premise. -/
theorem domains {H : Type}
 (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
 (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
 (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
 (v : AspisR1PublicPreparation.verifier.View) (hash : H)
 (out : AspisR1PublicPreparation.verifier.Prepared) (scratch old : Array PE 29#usize)
 (run : AspisR1PublicPreparation.PreparedScratchModel.prepare
  (AspisR1ClaimPreparedBridge.concreteBoundaries
   (AspisR1ClaimPreparedBridge.withCandidateSamplers sampling)) D sem v hash old=ok (.Ok out,scratch)) :
 NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray (map e scratch)) ∧
 NFS_QueryInvariant.Domain (prepared out) 0 10 NFW_QueryEntry.initial NFW_QueryEntry.pending := by
 obtain ⟨g,native,same,ports,canonical⟩ :=
  NFW_PreparedProducer.scratch sampling D sem v hash out scratch old run
 exact ⟨canonical,NFW_QueryEntry.domain _ (NFW_ScalarRho.prepared _ D sem v hash out scratch old run)⟩

/-- Installs the CLOSED NFS TX1 root on the original produced scratch itself,
not a second arbitrary powers vector. All query consumer domains are derived. -/
theorem tx1 {H : Type}
 (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
 (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
 (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
 (v : AspisR1PublicPreparation.verifier.View) (hash : H)
 (out : AspisR1PublicPreparation.verifier.Prepared) (scratch old : Array PE 29#usize)
 (run : AspisR1PublicPreparation.PreparedScratchModel.prepare
  (AspisR1ClaimPreparedBridge.concreteBoundaries
   (AspisR1ClaimPreparedBridge.withCandidateSamplers sampling)) D sem v hash old=ok (.Ok out,scratch))
 (base : Port3_NativeQueryBody.Ops) (proof : Slice U8)
 (geometry : AspisR1Stage2.verifier.QueryGeometry) (qPlace gPlace : Nat) :
 NFG_QueryLoopDefs.run
  (NFS_QueryLoopRoot.child base proof (prepared out) (map e scratch) geometry qPlace gPlace)
  10#usize 10 (.Ok (NFW_QueryEntry.initial,NFW_QueryEntry.pending)) =
 verifier.candidate.query_loop (NFS_QueryOps.installed base) proof
  (prepared out) NFW_QueryEntry.initial (map e scratch) none geometry NFW_QueryEntry.pending 10#usize := by
 have both := domains sampling D sem v hash out scratch old run
 exact NFS_QueryLoopRoot.tx1 base proof (prepared out) NFW_QueryEntry.initial
  (map e scratch) geometry NFW_QueryEntry.pending qPlace gPlace both.1 both.2 rfl
#print axioms domains
#print axioms tx1
end AspisR1.NFW_PrepareQuery
