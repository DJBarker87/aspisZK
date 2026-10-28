import NDO_JHk_QueryRhs
import NDO_JHk_PreparedScalarBytes
import NDO_JHe_CurrentWriterImage
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_RhsBytes
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry JHe_CurrentWriterImage

theorem encode (a : verifier.Accumulator)
    (identity : Tx1Q_Carriers.e a.rhs=JFq_Rhs.scalar) :
    (WAdm_SourceBody.put (accumulator a).rhs).map CheckpointBytes5Writer.u8=JFq_Rhs.bytes := by
  change (WAdm_SourceBody.put (CheckpointBytes3Namespaces.toE
    (Tx1Q_Carriers.e a.rhs))).map _=_
  rw [identity]
  simp only [WAdm_SourceBody.put,WAdm_SourceWriter.map_bytes,CheckpointBytesE.rawBytes,
    JHk_PreparedScalarBytes.rawKBytes]
  rfl
#print axioms encode

/-- Serialization of the SAME query output's rhs. Flush replaces only
weights, so this is also its writer operand's thirty-two-byte rhs field. -/
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
    (WAdm_SourceBody.put (accumulator out).rhs).map CheckpointBytes5Writer.u8=JFq_Rhs.bytes :=
  encode out (JHk_QueryRhs.source p input scratch initial out pending after g prepare queries init pend geo query)
#print axioms source
end AspisR1.JHk_RhsBytes
end
