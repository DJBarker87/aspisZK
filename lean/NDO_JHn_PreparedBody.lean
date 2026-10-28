import NDO_JHn_BodyIdentity
import NDO_JHn_ClaimBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHn_PreparedBody
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry JHe_CurrentWriterImage
/-- All field hypotheses of the byte-composition theorem are derived from
one successful preparation, query, and flush. Only digest values are fixed. -/
theorem source (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (initial out : verifier.Accumulator) (pending after : verifier.BatchedWeights)
    (g : verifier.QueryGeometry) (flushed : Slice aspis_core.field.QM31)
    (prepare : verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch))
    (init : installed.op20 .S2=ok (.Ok initial))
    (pend : installed.op18 initial.weights.deref=ok (.Ok pending))
    (geo : installed.op19 p.queries 0#usize 10#usize=ok (.Ok g))
    (query : installed.op7 JFx_NativeBytes.proof p initial scratch none g pending 10#usize=
      ok (.Ok (out,after))) (flush : installed.op17 after out.weights.deref=ok flushed)
    (variant : p.variant=.S2) (next : out.next.val=10) :
    (WAdm_SourceBody.body (prepared p)
      (accumulator {out with weights:=⟨flushed.val,flushed.property⟩})
      JFq_AuthBytes.proofHash JFq_AuthBytes.publicHash).map CheckpointBytes5Writer.u8=
        JFx_NativeBytes.checkpoint.val.take 1736 :=
  JHn_BodyIdentity.source p {out with weights:=⟨flushed.val,flushed.property⟩}
    _ _ (JHl_KnownFields.source p input scratch initial out pending after g flushed
      prepare init pend geo query flush) (JHn_ClaimBytes.source p input scratch prepare)
    rfl rfl variant next
#print axioms source
end AspisR1.JHn_PreparedBody
end
