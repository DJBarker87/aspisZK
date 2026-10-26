import F3N_CheckpointLog
import F3N_SourceEffect
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_SourceCheckpointLog
open Aeneas Aeneas.Std Result
open AspisR1Stage2 CheckpointBytes5Effect CheckpointBytes5Inputs CheckpointBytes5Join
open CheckpointBytes4SavedFields
open F3K_CheckpointPreparedFields CheckpointBytes3Namespaces
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- The complete six source reads are on the numeric source body. Identifying
that numeric body with F3's discovered model remains a separate obligation. -/
theorem stage (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) (reserved : Bool)
    (out : AspisR1PublicPreparation.verifier.Prepared) (a : verifier.Accumulator)
    (proof pub : Slice U8) (stored physical : Bytes)
    (proofBytes : MultiproofConeCanonical.bytesOf proof.val=stored)
    (publicBytes : MultiproofConeCanonical.bytesOf pub.val=physical)
    (variant : out.variant=.S2) (size : a.weights.val.length=64)
    (qb : ∀ j : Fin 22,((writerPrepared out).queries.val[j.val]'(by have h : (writerPrepared out).queries.val.length=22:=(writerPrepared out).queries.property;omega)).val<262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields (CheckpointBytesBody.fields (writerPrepared out)
      (toAccumulator a) (by simpa only [toAccumulator,mapVec,List.length_map] using size) qb))
    (next : a.next.val=10) (p2 : verifier.Prepared) (a2 : verifier.Accumulator)
    (success : (SdkC_Source.run hashv (CheckpointBytes5Join.stage reserved (writerPrepared out) (toAccumulator a) proof pub)
      []).1=ok (.Ok (p2,a2)))
    (p : OraclePortCompactDraft.Parsed) (i : RecordedBinaryExperimentBin.SourceInputs)
    (v : LiteralOpeningView.View) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (prepared : F3L_SourcePrepared.numeric out=OraclePortCheckpointResumeC5.prepared
      (OraclePortAcceptedContextC6.context p i v) i.data (SelectedChallengeMap.rhoOf i.rho) q)
    (accumulator : CheckpointBytes5Output.accumulator a=
      (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model i.data
        (SelectedChallengeMap.rhoOf i.rho) q)).accumulator) :
    BodyMatches p2 a2
      (OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context p i v)
        i.data (SelectedChallengeMap.rhoOf i.rho) q)
      (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model i.data
        (SelectedChallengeMap.rhoOf i.rho) q)).accumulator ∧
    SdkC_Source.readLog (SdkC_Source.run hashv
      (CheckpointBytes5Join.stage reserved (writerPrepared out) (toAccumulator a) proof pub) []).2=
      (AspisV8R19.MemoizedProgramLaw.eval H
      (F3_Model.checkpoint ⟨physical⟩ stored p q tr i v)).1 := by
  have caller : S2S10CallerBinding (SdkC_Source.dictionary hashv) () H proof pub stored physical := by
    refine ⟨proofBytes,publicBytes,?_⟩
    intro parts digest returned
    exact (syscall.returningValue parts digest returned).trans (p1.realization _)
  obtain ⟨after,ran,logs⟩ := F3N_SourceEffect.accepted hashv _ (.Ok (p2,a2)) [] [] rfl success
  have source := F3N_CheckpointLog.stage (SdkC_Source.dictionary hashv) () H reserved out a proof pub
    stored physical caller variant size qb canonical next p2 a2 after ran p i v q tr prepared accumulator
  exact ⟨source.1,logs.symm.trans source.2⟩

#print axioms stage
end AspisR1.F3N_SourceCheckpointLog
end
