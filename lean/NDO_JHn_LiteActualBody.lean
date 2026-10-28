import NDO_JHn_PreparedBody
import NDO_JHn_ByteSHA
import NDO_JHn_ImageBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHn_LiteActualBody
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry JHe_CurrentWriterImage
variable [sha : JHn_ByteSHA]
/-- The writer's actual digest results and actual converted body, identified
on the SAME preparation/query/flush witness. -/
theorem source (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (initial out : verifier.Accumulator) (pending after : verifier.BatchedWeights)
    (g : verifier.QueryGeometry) (flushed : Slice aspis_core.field.QM31)
    (hp hu : Array U8 32#usize) (body : Slice U8)
    (prepare : verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch))
    (init : installed.op20 .S2=ok (.Ok initial))
    (pend : installed.op18 initial.weights.deref=ok (.Ok pending))
    (geo : installed.op19 p.queries 0#usize 10#usize=ok (.Ok g))
    (query : installed.op7 JFx_NativeBytes.proof p initial scratch none g pending 10#usize=
      ok (.Ok (out,after))) (flush : installed.op17 after out.weights.deref=ok flushed)
    (variant : p.variant=.S2) (next : out.next.val=10)
    (hpCall : dictionary.digest () (AspisR1Stage2.WireTx2.singletonParts JFx_NativeBytes.proof)=ok hp)
    (huCall : dictionary.digest () (AspisR1Stage2.WireTx2.singletonParts JFx_NativeBytes.publicInput)=ok hu)
    (bodyCall : WAdm_SourceWriter.toSlice (WAdm_SourceBody.body (prepared p)
      (accumulator {out with weights:=⟨flushed.val,flushed.property⟩}) hp hu)=ok body) :
    body.val=JFx_NativeBytes.checkpoint.val.take 1736 := by
  have bytes := JHn_ImageBytes.source _ body bodyCall
  rw [JHn_ByteSHA.proofCall hp hpCall,JHn_ByteSHA.publicCall hu huCall] at bytes
  exact bytes.trans (JHn_PreparedBody.source p input scratch initial out pending after g flushed
    prepare init pend geo query flush variant next)
#print axioms source
end AspisR1.JHn_LiteActualBody
end
