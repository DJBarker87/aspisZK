import NDO_JHk_QueryPower
import NDO_JHk_PreparedScalarBytes
import NDO_JHe_CurrentWriterImage
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_PowerBytes
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry JHe_CurrentWriterImage

theorem encode (a : verifier.Accumulator)
    (identity : Tx1Q_Carriers.k a.power=JFq_Power.scalar) :
    (WAdm_SourceBody.putK (accumulator a).power).map CheckpointBytes5Writer.u8=JFq_Power.bytes := by
  change (WAdm_SourceBody.putK (CheckpointBytes3Namespaces.toK
    (Tx1Q_Carriers.k a.power))).map _=_
  rw [identity]
  rw [JHk_PreparedScalarBytes.encodeK]
  rfl
#print axioms encode

/-- Serialization of the SAME query output's power. Flush replaces only
weights, so this is also its writer operand's sixteen-byte power field. -/
theorem source (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (initial out : verifier.Accumulator) (pending after : verifier.BatchedWeights)
    (g : verifier.QueryGeometry)
    (prepare : verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch))
    (queries : p.queries=JFq_Queries.value)
    (init : installed.op20 .S2=ok (.Ok initial))
    (pend : installed.op18 initial.weights.deref=ok (.Ok pending))
    (geo : installed.op19 p.queries 0#usize 10#usize=ok (.Ok g))
    (query : installed.op7 JFx_NativeBytes.proof p initial scratch none g pending 10#usize=
      ok (.Ok (out,after))) :
    (WAdm_SourceBody.putK (accumulator out).power).map CheckpointBytes5Writer.u8=JFq_Power.bytes :=
  encode out (JHk_QueryPower.source p input scratch initial out pending after g prepare queries init pend geo query)
#print axioms source
end AspisR1.JHk_PowerBytes
end
