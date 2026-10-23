import Port3_CheckpointRows
import Port3_Constructor

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_CheckpointEndpoint
open Aeneas Aeneas.Std Result VTop_Stages
open CheckpointBytes5Effect CheckpointBytes5Inputs CheckpointBytes5Join
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConeCanonical OraclePortCompactDraft
open OraclePortCheckpointAbiC5 OraclePortCheckpointResumeC5
open RawCutTranscriptRun (ErasedPrefix)
open RecordedBinaryExperimentBin (SourceInputs)

theorem final_checkpoint_source (base : Ops) (reserved : Bool) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) :
    VTop_Checkpoint.CheckpointSourceJoin (Port3_Constructor.installed base reserved) D hash reserved := by
  constructor
  · intro semantic proof pub split p a saved _ accepted
    obtain ⟨after,success⟩ := Port3_CheckpointInstall.writer_run D p a proof pub hash saved accepted []
    exact ⟨[],after,success⟩
  · intro ck proof pub p a accepted
    exact Port3_CheckpointInstall.reader_success reserved D ck proof pub .S2 hash p a accepted

/-- Same installed calls and same returned checkpoint reach the existing
success-conditioned frozen2 checkpoint theorem. It says nothing about the
later native twelve-query block, which the model's resumedSource computes. -/
theorem checkpoint_endpoint (base : Ops) (reserved : Bool) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State)
    (wp : verifier.Prepared) (wa : verifier.Accumulator)
    (proof pub : Slice U8) (stored : Bytes) (parsed : Parsed)
    (q : Fin 22 → Fin 262144) (tr : ErasedPrefix) (i : SourceInputs) (v : LiteralOpeningView.View)
    (input : OraclePortStoredDecisionDraftC4.input parsed q tr = some i)
    (query : OraclePortSelectedDraft.queries tr = some q)
    (caller : S2S10CallerBinding (VTop_Checkpoint.digest D) hash H proof pub stored tr.statement.pubBytes)
    (provenance : S1S7S8StateProvenance (CheckpointBytes3Namespaces.toPrepared wp)
      (CheckpointBytes3Namespaces.toAccumulator wa)
      (prepared (OraclePortAcceptedContextC6.context parsed i v) i.data
        (SelectedChallengeMap.rhoOf i.rho) q)
      (OraclePortCheckpointStateC3.write (model i.data (SelectedChallengeMap.rhoOf i.rho) q)).accumulator)
    (saved : alloc.vec.Vec U8) (p : verifier.Prepared) (a : verifier.Accumulator)
    (wrote : (Port3_Constructor.installed base reserved).op8 D wp wa proof pub hash = ok saved)
    (resumed : (Port3_Constructor.installed base reserved).op18 D (VTop_Checkpoint.checkpointSlice saved)
      proof pub .S2 hash = ok (.Ok (p,a))) :
    ∃ after,
      run (VTop_Checkpoint.digest D) hash
        (stage reserved (CheckpointBytes3Namespaces.toPrepared wp)
          (CheckpointBytes3Namespaces.toAccumulator wa) proof pub) [] = ok (.Ok (p,a),after) ∧
      (observe after,some (resumedSource i.data p a)) =
        eval H (OraclePortFrozen2.checkpoint stored parsed q tr i v) := by
  obtain ⟨after,success⟩ := Port3_CheckpointRows.combined_run base reserved D hash
    wp wa proof pub saved p a wrote resumed []
  exact ⟨after,success,success_conditioned_checkpoint_stage_join (VTop_Checkpoint.digest D)
    hash H reserved _ _ proof pub stored parsed q tr i v input query caller provenance p a after success⟩

#print axioms final_checkpoint_source
#print axioms checkpoint_endpoint
end AspisR1.Port3_CheckpointEndpoint
end
