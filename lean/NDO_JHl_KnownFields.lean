import NDO_JHk_KnownFields
import NDO_JHl_SemanticBytes
import NDO_JHl_ZBytes
import NDO_JHl_WeightOutput
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_KnownFields
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry JHe_CurrentWriterImage

/-- Derived outputs of one actual preparation/query/flush. Claim is intentionally
absent: these laws do not imply full body or saved-vector identity. -/
structure Fields (p : verifier.Prepared) (a : verifier.Accumulator) : Prop where
  inherited : JHk_KnownFields.Fields p a
  semantic : ((prepared p).semantic_alpha.val.flatMap WAdm_SourceBody.putK).map CheckpointBytes5Writer.u8=
    JFq_Sem00.bytes++JFq_Sem01.bytes++JFq_Sem02.bytes++JFq_Sem03.bytes++JFq_Sem04.bytes++
    JFq_Sem05.bytes++JFq_Sem06.bytes++JFq_Sem07.bytes++JFq_Sem08.bytes++JFq_Sem09.bytes
  z : ((prepared p).z.val.flatMap (fun z => WAdm_SourceBody.putK z.x++WAdm_SourceBody.putK z.y)).map
    CheckpointBytes5Writer.u8=JFq_Z0.bytes++JFq_Z1.bytes++JFq_Z2.bytes++JFq_Z3.bytes
  weights : ((accumulator a).weights.val.flatMap WAdm_SourceBody.putK).map CheckpointBytes5Writer.u8=
    (JFx_NativeBytes.checkpoint.val.drop 712).take 1024

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
      ok (.Ok (out,after))) (flush : installed.op17 after out.weights.deref=ok flushed) :
    Fields p {out with weights:=⟨flushed.val,flushed.property⟩} :=
  ⟨JHk_KnownFields.afterFlush p out flushed (JHk_KnownFields.source p input scratch initial out pending after g
    prepare init pend geo query),JHl_SemanticBytes.source p input scratch prepare,
    JHl_ZBytes.source p input scratch prepare,
    JHl_WeightOutput.source p input scratch initial out pending after g flushed prepare init pend geo query flush⟩
#print axioms source

/-- Non-vacuity of1624 identified body-field bytes on the SAME actual final
writer accumulator. This is not full headline hypothesis inhabitance. -/
theorem inhabited : ∃ (p : verifier.Prepared) (out : verifier.Accumulator)
    (after : verifier.BatchedWeights) (flushed : Slice aspis_core.field.QM31),
    installed.op17 after out.weights.deref=ok flushed ∧
    Fields p {out with weights:=⟨flushed.val,flushed.property⟩} := by
  obtain ⟨p,scratch,initial,out,pending,after,g,flushed,prepare,init,pend,geo,query,flush⟩ :=
    JHc_InstalledQuery.inhabited
  exact ⟨p,out,after,flushed,flush,
    source p _ scratch initial out pending after g flushed prepare init pend geo query flush⟩
#print axioms inhabited
end AspisR1.JHl_KnownFields
end
