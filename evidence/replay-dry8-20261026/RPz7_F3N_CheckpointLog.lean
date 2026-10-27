import RPz7_F3L_CheckpointNumeric
import F3_Checkpoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_CheckpointLog
open Aeneas Aeneas.Std Result
open AspisR1Stage2 CheckpointBytes5Effect CheckpointBytes5Inputs CheckpointBytes5Join
open CheckpointBytes4SavedFields
open F3K_CheckpointPreparedFields CheckpointBytes3Namespaces
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- The complete six source reads are on the numeric source body. Identifying
that numeric body with F3's discovered model remains a separate obligation. -/
theorem stage {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (H : Bytes → State) (reserved : Bool)
    (out : AspisR1PublicPreparation.verifier.Prepared) (a : verifier.Accumulator)
    (proof pub : Slice U8) (stored physical : Bytes)
    (caller : S2S10CallerBinding D hash H proof pub stored physical)
    (variant : out.variant=.S2) (size : a.weights.val.length=64)
    (qb : ∀ j : Fin 22,((writerPrepared out).queries.val[j.val]'(by have h : (writerPrepared out).queries.val.length=22:=(writerPrepared out).queries.property;omega)).val<262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields (CheckpointBytesBody.fields (writerPrepared out)
      (toAccumulator a) (by simpa only [toAccumulator,mapVec,List.length_map] using size) qb))
    (next : a.next.val=10) (p2 : verifier.Prepared) (a2 : verifier.Accumulator) (after : Log)
    (success : run D hash (CheckpointBytes5Join.stage reserved (writerPrepared out) (toAccumulator a) proof pub)
      []=ok (.Ok (p2,a2),after))
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
    observe after=(AspisV8R19.MemoizedProgramLaw.eval H
      (F3_Model.checkpoint ⟨physical⟩ stored p q tr i v)).1 := by
  have source := F3L_CheckpointNumeric.stage D hash H reserved out a proof pub stored physical caller
    variant size qb canonical next p2 a2 after success
  rw [prepared,accumulator] at source
  refine ⟨source.1,?_⟩
  rw [F3_Model.checkpoint,F3_Checkpoint.schedule]
  exact source.2

#print axioms stage
end AspisR1.F3N_CheckpointLog
end
