import F3_Model
import CheckpointBytes5Join
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_CheckpointSource
open Aeneas Aeneas.Std Result
open AspisR1Stage2 CheckpointBytes5Effect CheckpointBytes5Inputs CheckpointBytes5Join
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open OraclePortCompactDraft OraclePortCheckpointAbiC5 OraclePortCheckpointResumeC5
open RecordedBinaryExperimentBin (SourceInputs)

theorem stage {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (H : Bytes → State) (reserved : Bool)
    (wp : CheckpointBytes5Writer.Prepared) (wa : CheckpointBytes5Writer.Accumulator)
    (proof publicBytes : Slice U8) (stored : Bytes) (physical : F3_Model.PhysicalPublic)
    (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (i : SourceInputs) (v : LiteralOpeningView.View)
    (input : OraclePortStoredDecisionDraftC4.input parsed q tr=some i)
    (query : OraclePortSelectedDraft.queries tr=some q)
    (caller : S2S10CallerBinding D hash H proof publicBytes stored physical.bytes)
    (provenance : S1S7S8StateProvenance wp wa
      (prepared (OraclePortAcceptedContextC6.context parsed i v) i.data (SelectedChallengeMap.rhoOf i.rho) q)
      (OraclePortCheckpointStateC3.write (model i.data (SelectedChallengeMap.rhoOf i.rho) q)).accumulator)
    (p : verifier.Prepared) (a : verifier.Accumulator) (after : Log)
    (success : run D hash (CheckpointBytes5Join.stage reserved wp wa proof publicBytes) []=ok (.Ok (p,a),after)) :
    (observe after,some (resumedSource i.data p a))=
      eval H (F3_Model.checkpoint physical stored parsed q tr i v) := by
  have fields := (OraclePortStoredDecisionDraftC4.input_fields parsed q tr i input).1
  have decoded : LiteralQueryRead.decode i.queryBytes=some q := by
    simpa [OraclePortSelectedDraft.queries,fields.2.1] using query
  have unique := (LiteralQueryRead.decode_success _ _ decoded).2
  exact (successful_stage D hash H reserved wp wa proof publicBytes stored physical.bytes
    (OraclePortAcceptedContextC6.context parsed i v) i.data (SelectedChallengeMap.rhoOf i.rho) q
    caller provenance unique p a after success).trans
    (OraclePortCkptAbi5Stage.stage_observation H stored physical.bytes
      (OraclePortAcceptedContextC6.context parsed i v) i.data (SelectedChallengeMap.rhoOf i.rho) q unique)

#print axioms stage
end AspisR1.F3J_CheckpointSource
end
