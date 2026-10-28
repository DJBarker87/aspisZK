import NDO_JHk_PreparedRemaining
import NDO_JHk_PreparedScalarBytes
import NDO_JHk_RhsBytes
import NDO_JHk_PowerBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_KnownFields
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry JHe_CurrentWriterImage

/-- Outputs derived from one actual prepare/query pair. This is not an
assumption container, a complete body identity, or a saved-vector identity. -/
structure Fields (p : verifier.Prepared) (a : verifier.Accumulator) : Prop where
  early :
    (WAdm_SourceBody.put (prepared p).gamma).map CheckpointBytes5Writer.u8=JFq_Gamma.bytes ∧
    (WAdm_SourceBody.put (prepared p).kappa).map CheckpointBytes5Writer.u8=JFq_Kappa.bytes ∧
    ((prepared p).alpha.val.flatMap WAdm_SourceBody.put).map CheckpointBytes5Writer.u8=
      JFq_Alpha0.bytes++JFq_Alpha1.bytes ∧
    (WAdm_SourceBody.putK (prepared p).rho).map CheckpointBytes5Writer.u8=JFq_Rho.bytes
  fixed :
    (MultiproofConeCanonical.bytesOf (prepared p).state.val).map CheckpointBytes5Writer.u8=JFq_State.bytes ∧
    ((prepared p).roots.val.flatMap (fun r => MultiproofConeCanonical.bytesOf r.val)).map
      CheckpointBytes5Writer.u8=JFq_Root0.bytes++JFq_Root1.bytes ∧
    ((prepared p).queries.val.flatMap (fun q => MultiproofConeCanonical.bytesOf
      (core.num.U32.to_le_bytes q).val)).map CheckpointBytes5Writer.u8=JHk_PreparedRemaining.queryBytes
  rhs : (WAdm_SourceBody.put (accumulator a).rhs).map CheckpointBytes5Writer.u8=JFq_Rhs.bytes
  power : (WAdm_SourceBody.putK (accumulator a).power).map CheckpointBytes5Writer.u8=JFq_Power.bytes

theorem source (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (initial out : verifier.Accumulator) (pending after : verifier.BatchedWeights)
    (g : verifier.QueryGeometry)
    (prepare : verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch))
    (init : installed.op20 .S2=ok (.Ok initial))
    (pend : installed.op18 initial.weights.deref=ok (.Ok pending))
    (geo : installed.op19 p.queries 0#usize 10#usize=ok (.Ok g))
    (query : installed.op7 JFx_NativeBytes.proof p initial scratch none g pending 10#usize=
      ok (.Ok (out,after))) : Fields p out := by
  have queries := JGp_CurrentQueries.source _ _ _ JGn_TerminalIdentified.shaDictionary () p input scratch prepare
  exact ⟨JHk_PreparedScalarBytes.source p input scratch prepare,
    JHk_PreparedRemaining.source p input scratch prepare,
    JHk_RhsBytes.source p input scratch initial out pending after g prepare queries init pend geo query,
    JHk_PowerBytes.source p input scratch initial out pending after g prepare queries init pend geo query⟩
#print axioms source

theorem afterFlush (p : verifier.Prepared) (out : verifier.Accumulator)
    (flushed : Slice aspis_core.field.QM31) (h : Fields p out) :
    Fields p {out with weights:=⟨flushed.val,flushed.property⟩} :=
  ⟨h.early,h.fixed,h.rhs,h.power⟩
#print axioms afterFlush

/-- Non-vacuity of these auxiliary field laws on the inherited actual
query/flush witness and its final writer accumulator. NOT headline inhabitance. -/
theorem inhabited : ∃ (p : verifier.Prepared) (out : verifier.Accumulator)
    (after : verifier.BatchedWeights) (flushed : Slice aspis_core.field.QM31),
    installed.op17 after out.weights.deref=ok flushed ∧
    Fields p {out with weights:=⟨flushed.val,flushed.property⟩} := by
  obtain ⟨p,scratch,initial,out,pending,after,g,flushed,prepare,init,pend,geo,query,flush⟩ :=
    JHc_InstalledQuery.inhabited
  exact ⟨p,out,after,flushed,flush,
    afterFlush p out flushed (source p _ scratch initial out pending after g prepare init pend geo query)⟩
#print axioms inhabited
end AspisR1.JHk_KnownFields
end
