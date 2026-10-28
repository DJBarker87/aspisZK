import NDO_JHe_WriterHeader
import NDO_JGr_Geometry
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_CurrentWriterImage
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry
open CheckpointBytes5Effect

abbrev dictionary := VTop_Checkpoint.digest (Tx1Q_Install.digest digest)
abbrev prepared (p : verifier.Prepared) := CheckpointBytes3Namespaces.toPrepared (Tx1Q_Carriers.prepared p)
abbrev accumulator (a : verifier.Accumulator) := CheckpointBytes3Namespaces.toAccumulator (Tx1Q_Carriers.accumulator a)

theorem total : ∀ parts, ∃ value, dictionary.digest () parts=ok value := by
  intro parts
  exact ⟨_,rfl⟩
#print axioms total

/-- Successful op16 exposes the code execution that constructed THAT saved
vector. The slice is the returned vector's dereference, not a chosen fixture. -/
theorem code_run (p : verifier.Prepared) (a : verifier.Accumulator) (saved : alloc.vec.Vec U8)
    (write : installed.op16 digest p a JFx_NativeBytes.proof JFx_NativeBytes.publicInput ()=ok saved) :
    erase dictionary () (WAdm_SourceWriter.code (prepared p) (accumulator a)
      JFx_NativeBytes.proof JFx_NativeBytes.publicInput)=ok saved.deref := by
  change WAdm_Install.writer digest p a JFx_NativeBytes.proof JFx_NativeBytes.publicInput ()=ok saved at write
  unfold WAdm_Install.writer WAdm_SourceWriter.writer at write
  obtain ⟨out,run,returned⟩ := Port3_PushFrame.bind_success _ _ _ write
  have same := Result.ok.inj returned
  have bytes := congrArg (fun x : alloc.vec.Vec U8 => x.val) same
  have slices : out=saved.deref := Subtype.ext bytes
  rw [slices] at run
  exact run
#print axioms code_run

theorem header (p : verifier.Prepared) (a : verifier.Accumulator) (saved : alloc.vec.Vec U8)
    (size : a.weights.val.length=64) (variant : p.variant=.S2) (next : a.next.val=10)
    (write : installed.op16 digest p a JFx_NativeBytes.proof JFx_NativeBytes.publicInput ()=ok saved) :
    saved.val.take 16=JFx_NativeBytes.checkpoint.val.take 16 := by
  apply JHe_WriterHeader.source dictionary () total (prepared p) (accumulator a)
    JFx_NativeBytes.proof JFx_NativeBytes.publicInput saved.deref
  · simpa only [accumulator,CheckpointBytes3Namespaces.toAccumulator,
      CheckpointBytes3Namespaces.mapVec,Tx1Q_Carriers.accumulator,Tx1Q_Carriers.vec,List.length_map] using size
  · change CheckpointBytes3Namespaces.toVariant (Tx1Q_Carriers.variant p.variant)=_
    rw [variant]
    rfl
  · exact next
  · exact code_run p a saved write
#print axioms header
end AspisR1.JHe_CurrentWriterImage
end
