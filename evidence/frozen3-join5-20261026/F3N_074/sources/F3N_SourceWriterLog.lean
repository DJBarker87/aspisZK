import F3N_SourceEffect
import CheckpointBytes5Writer
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_SourceWriterLog
open Aeneas Aeneas.Std Result AspisR1Stage2 CheckpointBytes5Effect CheckpointBytes5Inputs
open CheckpointBytes5Writer
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
theorem writer_effects (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (p : Prepared) (a : Accumulator) (proof public1 ck : Slice U8)
    (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22, (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields (CheckpointBytesBody.fields p a size qb))
    (next : a.next.val = 10)
    (success : (SdkC_Source.run hashv (writer p a proof public1) []).1=ok ck) :
    let pm := CheckpointBytesBlocks.prepared (CheckpointBytesBody.fields p a size qb) canonical
    let am := CheckpointBytesBlocks.accumulator (CheckpointBytesBody.fields p a size qb) canonical
    let stored := MultiproofConeCanonical.bytesOf proof.val
    let pub := MultiproofConeCanonical.bytesOf public1.val
    let address := OraclePortPhysicalFrameDraft.domain ++
      OraclePortCheckpointAbiC5.body pm am (H stored) (H pub)
    MultiproofConeCanonical.bytesOf ck.val=OraclePortCheckpointAbiC5.encode H stored pub pm am ∧
      SdkC_Source.readLog (SdkC_Source.run hashv (writer p a proof public1) []).2=
        [(stored,H stored),(pub,H pub),(address,H address)] := by
  have oracle : Oracle (SdkC_Source.dictionary hashv) () H := by
    intro parts digest returned
    exact (syscall.returningValue parts digest returned).trans (p1.realization _)
  obtain ⟨after,ran,logs⟩ := F3N_SourceEffect.accepted hashv (writer p a proof public1) ck [] [] rfl success
  have source := CheckpointBytes5Writer.writer_effects (SdkC_Source.dictionary hashv) () H oracle
    p a proof public1 ck size qb canonical next [] after ran
  refine ⟨source.1,?_⟩
  rw [← logs]
  simpa only [observe,List.map_nil,List.nil_append] using source.2

#print axioms writer_effects
end AspisR1.F3N_SourceWriterLog
end
