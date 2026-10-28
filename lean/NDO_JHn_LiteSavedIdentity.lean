import NDO_JHn_LiteActualBody
import NDO_JHn_RetainedChecksum
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHn_LiteSavedIdentity
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry JHe_CurrentWriterImage
variable [sha : JHn_ByteSHA]
/-- Full1768-byte identity, including the checksum field, for the vector
returned by the actual installed writer on this preparation/query/flush. -/
theorem source (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (initial out : verifier.Accumulator) (pending after : verifier.BatchedWeights)
    (g : verifier.QueryGeometry) (flushed : Slice aspis_core.field.QM31) (saved : alloc.vec.Vec U8)
    (prepare : verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch))
    (init : installed.op20 .S2=ok (.Ok initial))
    (pend : installed.op18 initial.weights.deref=ok (.Ok pending))
    (geo : installed.op19 p.queries 0#usize 10#usize=ok (.Ok g))
    (query : installed.op7 JFx_NativeBytes.proof p initial scratch none g pending 10#usize=
      ok (.Ok (out,after))) (flush : installed.op17 after out.weights.deref=ok flushed)
    (variant : p.variant=.S2) (next : out.next.val=10) (size : flushed.val.length=64)
    (write : installed.op16 digest p {out with weights:=⟨flushed.val,flushed.property⟩}
      JFx_NativeBytes.proof JFx_NativeBytes.publicInput ()=ok saved) :
    saved.val=JFx_NativeBytes.checkpoint.val := by
  let a : verifier.Accumulator := {out with weights:=⟨flushed.val,flushed.property⟩}
  have asize : (accumulator a).weights.val.length=64 := by
    simpa only [accumulator,a,CheckpointBytes3Namespaces.toAccumulator,
      CheckpointBytes3Namespaces.mapVec,Tx1Q_Carriers.accumulator,Tx1Q_Carriers.vec,List.length_map] using size
  have pv : (prepared p).variant=.S2 := by
    change CheckpointBytes3Namespaces.toVariant (Tx1Q_Carriers.variant p.variant)=_
    rw [variant]
    rfl
  obtain ⟨hp,hu,hc,body,hpCall,huCall,bodyCall,hcCall,bodySize,image⟩ :=
    JHe_WriterImage.source dictionary () total (prepared p) (accumulator a)
      JFx_NativeBytes.proof JFx_NativeBytes.publicInput saved.deref asize pv next
      (code_run p a saved write)
  have identity := JHn_LiteActualBody.source p input scratch initial out pending after g flushed hp hu body
    prepare init pend geo query flush variant next hpCall huCall bodyCall
  have bytes := JHn_ImageBytes.source _ body bodyCall
  have image' : saved.val=body.val++hc.val := by rw [bytes];exact image
  exact JHn_ImageIdentity.source saved body hc image' identity
    (JHn_RetainedChecksum.request body identity) hcCall
    JHn_ByteSHA.checksum JHn_RetainedChecksum.suffix
#print axioms source
end AspisR1.JHn_LiteSavedIdentity
end
