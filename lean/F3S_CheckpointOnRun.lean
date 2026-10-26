import F3K_CheckpointPreparedFields
import F3S_CheckpointSplice
import F3N_WriterReturned
import S2X_RuntimeRetention
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_CheckpointOnRun
open Aeneas Aeneas.Std Result CheckpointBytes5Effect Tx1Q_Carriers
 theorem log (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Unit)
    (law : ∀ parts,D.digest () parts=hashv parts) (reserved : Bool)
    (p : AspisR1CurrentCaller.verifier.Prepared) (a : AspisR1CurrentCaller.verifier.Accumulator)
    (out : AspisR1PublicPreparation.verifier.Prepared)
    (same : AspisR1CurrentCaller.InstalledPreparation.currentPrepared out=p)
    (proof pub proof2 pub2 ck : Slice U8) (saved : alloc.vec.Vec U8)
    (p2 : AspisR1Stage2.verifier.Prepared) (a2 : AspisR1Stage2.verifier.Accumulator)
    (after : Log)
    (writer : Port3_CheckpointInstall.writer (Tx1Q_Install.digest D) (prepared p) (accumulator a) proof pub ()=ok saved)
    (size : 32≤saved.val.length)
    (history : S2X.CheckpointVersionBinding (MultiproofConeCanonical.bytesOf saved.val) (MultiproofConeCanonical.bytesOf ck.val))
    (sameProof : MultiproofConeCanonical.bytesOf proof2.val=MultiproofConeCanonical.bytesOf proof.val)
    (samePub : MultiproofConeCanonical.bytesOf pub2.val=MultiproofConeCanonical.bytesOf pub.val)
    (ran : CheckpointBytes5Effect.run (VTop_Checkpoint.digest (Tx1Q_Install.digest D)) ()
      (CheckpointBytes5Join.stage reserved (F3K_CheckpointPreparedFields.writerPrepared out)
        (CheckpointBytes3Namespaces.toAccumulator (accumulator a)) proof pub) []=ok (.Ok (p2,a2),after)) :
    SdkC_Source.readLog (SdkC_Source.run hashv (GExp_FirstCode.writerCode p a proof pub) []).2 ++
      SdkC_Source.readLog (SdkC_Source.run hashv (GExq_RetainedReader.code reserved ck proof2 pub2 .S2) []).2=
        CheckpointBytes5Inputs.observe after := by
  have wrote := F3N_WriterReturned.erased (Tx1Q_Install.digest D) () (prepared p) (accumulator a) proof pub saved writer
  have rawWriter : erase (SdkC_Source.dictionary hashv) () (CheckpointBytes5Writer.writer
      (CheckpointBytes3Namespaces.toPrepared (prepared p))
      (CheckpointBytes3Namespaces.toAccumulator (accumulator a)) proof pub)=ok saved.deref := by
    rw [←SdkC_Source.erasure hashv _ []]
    rw [SdkC_Source.erasure_to (VTop_Checkpoint.digest (Tx1Q_Install.digest D)) () hashv law]
    exact wrote
  have wp : F3K_CheckpointPreparedFields.writerPrepared out=
      CheckpointBytes3Namespaces.toPrepared (prepared p) := by
    rw [←same]
    rfl
  rw [wp] at ran
  have result := F3S_CheckpointSplice.raw hashv (VTop_Checkpoint.digest (Tx1Q_Install.digest D)) () law
    reserved _ _ proof pub saved p2 a2 after rawWriter size ran
  rw [F3S_CheckpointSplice.writer]
  have ckEq : ck=saved.deref := F3Q_SliceIdentity.slice _ _ (S2X.checkpoint_persistence _ _ history)
  have proofEq := F3Q_SliceIdentity.slice _ _ sameProof
  have pubEq := F3Q_SliceIdentity.slice _ _ samePub
  rw [ckEq,proofEq,pubEq]
  exact result
#print axioms log
end AspisR1.F3S_CheckpointOnRun
end
