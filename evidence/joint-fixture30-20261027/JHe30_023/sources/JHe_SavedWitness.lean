import JHc_TX1Candidate
import JHe_CurrentWriterImage
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_SavedWitness
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry
open JHe_CurrentWriterImage

/-- This witness is selected by the actual source return, including its full
constructed image and actual three digest calls. No retained output is supplied. -/
theorem inhabited : ∃ (p : verifier.Prepared) (a : verifier.Accumulator) (saved : alloc.vec.Vec U8)
    (hp hu hc : CheckpointBytes5Effect.Digest) (body : Slice U8),
    verifier.candidate.tx1 installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.publicInput JFx_NativeBytes.proof 10#usize () none=ok (.Ok saved) ∧
    installed.op16 digest p a JFx_NativeBytes.proof JFx_NativeBytes.publicInput ()=ok saved ∧
    saved.val.length=1768 ∧ saved.val.take 16=JFx_NativeBytes.checkpoint.val.take 16 ∧
    dictionary.digest () (AspisR1Stage2.WireTx2.singletonParts JFx_NativeBytes.proof)=ok hp ∧
    dictionary.digest () (AspisR1Stage2.WireTx2.singletonParts JFx_NativeBytes.publicInput)=ok hu ∧
    WAdm_SourceWriter.toSlice (WAdm_SourceBody.body (prepared p) (accumulator a) hp hu)=ok body ∧
    dictionary.digest () (AspisR1Stage2.WireTx2.checksumParts body)=ok hc ∧
    body.val.length=1736 ∧
    saved.val=(WAdm_SourceBody.body (prepared p) (accumulator a) hp hu).map CheckpointBytes5Writer.u8 ++ hc.val := by
  obtain ⟨p,scratch,initial,out,pending,after,g,flushed,saved,
    prepare,batch,query,flush,write,returned,length,variant,next,size⟩ := JHc_TX1Candidate.returns
  let a : verifier.Accumulator := {out with weights:=⟨flushed.val,flushed.property⟩}
  have asize : (accumulator a).weights.val.length=64 := by
    simpa only [accumulator,a,CheckpointBytes3Namespaces.toAccumulator,
      CheckpointBytes3Namespaces.mapVec,Tx1Q_Carriers.accumulator,Tx1Q_Carriers.vec,List.length_map] using size
  have pvariant : (prepared p).variant=.S2 := by
    change CheckpointBytes3Namespaces.toVariant (Tx1Q_Carriers.variant p.variant)=_
    rw [variant]
    rfl
  obtain ⟨hp,hu,hc,body,hpCall,huCall,bodyCall,hcCall,bodySize,image⟩ :=
    JHe_WriterImage.source dictionary () total (prepared p) (accumulator a)
      JFx_NativeBytes.proof JFx_NativeBytes.publicInput saved.deref asize pvariant next
      (code_run p a saved write)
  exact ⟨p,a,saved,hp,hu,hc,body,returned,write,length,
    header p a saved size variant next write,hpCall,huCall,bodyCall,hcCall,bodySize,image⟩
#print axioms inhabited
end AspisR1.JHe_SavedWitness
end
