import F3S_EffectLog
import F3S_ReaderSyntax
import F3S_Forward
import F3S_MapLog
import GExp_FirstCode
import F3Q_SliceIdentity
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_CheckpointSplice
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
 theorem raw {Hash : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (law : ∀ parts,D.digest hash parts=hashv parts)
    (reserved : Bool) (wp : CheckpointBytes5Writer.Prepared) (wa : CheckpointBytes5Writer.Accumulator)
    (proof pub : Slice U8) (saved : alloc.vec.Vec U8)
    (p : AspisR1Stage2.verifier.Prepared) (a : AspisR1Stage2.verifier.Accumulator) (after : Log)
    (writer : erase (SdkC_Source.dictionary hashv) () (CheckpointBytes5Writer.writer wp wa proof pub)=ok saved.deref)
    (size : 32≤saved.val.length)
    (ran : CheckpointBytes5Effect.run D hash (CheckpointBytes5Join.stage reserved wp wa proof pub) []=ok (.Ok (p,a),after)) :
    SdkC_Source.readLog (SdkC_Source.run hashv (CheckpointBytes5Writer.writer wp wa proof pub) []).2 ++
      SdkC_Source.readLog (SdkC_Source.run hashv (GExq_RetainedReader.code reserved saved.deref proof pub .S2) []).2=
        CheckpointBytes5Inputs.observe after := by
  have actual := F3S_EffectLog.accepted hashv D hash law (CheckpointBytes5Join.stage reserved wp wa proof pub)
    (core.result.Result.Ok (p,a)) after ran
  unfold CheckpointBytes5Join.stage at actual
  rw [F3S_Forward.bind_log hashv _ _ saved.deref writer] at actual
  rw [F3S_ReaderSyntax.log hashv reserved saved.deref proof pub size]
  exact actual
 theorem writer (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (p : AspisR1CurrentCaller.verifier.Prepared) (a : AspisR1CurrentCaller.verifier.Accumulator)
    (proof pub : Slice U8) :
    SdkC_Source.readLog (SdkC_Source.run hashv (GExp_FirstCode.writerCode p a proof pub) []).2=
    SdkC_Source.readLog (SdkC_Source.run hashv (CheckpointBytes5Writer.writer
      (CheckpointBytes3Namespaces.toPrepared (Tx1Q_Carriers.prepared p))
      (CheckpointBytes3Namespaces.toAccumulator (Tx1Q_Carriers.accumulator a)) proof pub) []).2 := by
  exact congrArg SdkC_Source.readLog (F3S_MapLog.run_map hashv _ (fun (ck : Slice U8)=> (⟨ck.val,ck.property⟩ : alloc.vec.Vec U8)) [])
#print axioms raw
#print axioms writer
end AspisR1.F3S_CheckpointSplice
end
