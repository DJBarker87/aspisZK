import NDO_JHm_PreparedClaim
import NDO_JHk_PreparedScalarBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHn_ClaimBytes
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry JHe_CurrentWriterImage
/-- Serialize the already proved actual claim without importing the SDK/joint
statement environment. No claim arithmetic is recomputed. -/
theorem source (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (prepare : verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch)) :
    (WAdm_SourceBody.put (prepared p).claim).map CheckpointBytes5Writer.u8=JFq_Claim.bytes := by
  change (WAdm_SourceBody.put (CheckpointBytes3Namespaces.toE (Tx1Q_Carriers.e p.claim))).map _=_
  rw [JHm_PreparedClaim.source p input scratch prepare]
  simp only [WAdm_SourceBody.put,WAdm_SourceWriter.map_bytes,CheckpointBytesE.rawBytes,
    JHk_PreparedScalarBytes.rawKBytes]
  rfl
#print axioms source
end AspisR1.JHn_ClaimBytes
end
