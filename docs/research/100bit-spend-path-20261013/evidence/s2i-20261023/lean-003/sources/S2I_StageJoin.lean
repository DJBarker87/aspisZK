import CheckpointBytes5Decision
import MultiproofConeFrozen2Stage
import S8JoinFrozenScan

/-! Value-dependent observation composition at the actual reached checkpoint
position of dV_frozen2. The prefix and remaining verifier stages are the pinned
model stages; this is the checkpoint replacement theorem, not a frozen whole
Rust decision or two-pass AcceptedRunJoin inhabitant. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S2I.StageJoin
open Aeneas Aeneas.Std Result AspisR1Stage2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortCheckpointAbiC5 OraclePortCheckpointResumeC5
open CheckpointBytes5Effect CheckpointBytes5Inputs CheckpointBytes5Join OraclePortFrozen2
open CheckpointBytes5Decision
open RawCutTranscriptRun (ErasedPrefix ErasedMessage)
open RecordedBinaryExperimentBin (SourceInputs)
/-! Accepted batch0 substitution around the existing checkpoint decision join.
This is an ordered MODEL observation theorem. In particular the checkpoint
stage includes the writer; it is not the whole native tx2_authenticated child.
The source state provenance and concrete query/finish ports remain required. -/
theorem ordered_checkpoint_batches {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (H : Bytes → State) (reserved : Bool)
    (wp : CheckpointBytes5Writer.Prepared) (wa : CheckpointBytes5Writer.Accumulator)
    (proof public1 : Slice U8) (stored : Bytes) (parsed : Parsed)
    (q : Fin 22 → Fin 262144) (tr : ErasedPrefix) (m : ErasedMessage)
    (i : SourceInputs) (v : LiteralOpeningView.View)
    (guard : OraclePortAdmission.Guard tr)
    (parser : OraclePortStoredParserC4.parseReached stored tr = some parsed)
    (query : OraclePortSelectedDraft.queries tr = some q)
    (input : OraclePortStoredDecisionDraftC4.input parsed q tr = some i)
    (view : LiteralOpeningView.read (OraclePortStoredDecisionDraftC4.typedRows parsed q tr) = some v)
    (nodes : Nat → Nat → Slice U8) (scratch0 : MultiproofConeRef.reference.Scratch)
    (law : ∀ parts, D.digest hash parts = ok (MultiproofConePhysicalProgram.rawOracle H parts))
    (views : ∀ b k, b<2 → k<3 → MultiproofConeCanonical.bytesOf (nodes b k).val=
      slice parsed.wire (OraclePortFrozenOrder.slotStart (3*b+k))
        (32*OraclePortFrozenOrder.capacity (3*b+k)))
    (source0 : (eval H (MultiproofConeFrozen2Stage.sourceBatch parsed q nodes 0 scratch0)).2=true)
    (caller : S2S10CallerBinding D hash H proof public1 stored tr.statement.pubBytes)
    (provenance : S1S7S8StateProvenance wp wa
      (prepared (OraclePortAcceptedContextC6.context parsed i v) i.data
        (SelectedChallengeMap.rhoOf i.rho) q)
      (OraclePortCheckpointStateC3.write (model i.data (SelectedChallengeMap.rhoOf i.rho) q)).accumulator)
    (p : verifier.Prepared) (a : verifier.Accumulator) (after : Log)
    (success : run D hash (stage reserved wp wa proof public1) [] = ok (.Ok (p,a),after)) :
    let suffix := bindObservation H (observe after,some (resumedSource i.data p a))
      (fun resumed => match resumed with | none => .done false | some state => stage2 parsed q tr i state)
    ((eval H (MultiproofConeFrozen2Stage.sourceBatch parsed q nodes 0 scratch0)).1 ++ suffix.1,suffix.2) =
      eval H (dV_frozen2 stored tr m) := by
  have batches := MultiproofConeFrozen2Stage.both_batches D hash H law parsed q nodes views
  have same0 := batches.1 scratch0 source0
  have batchOk : (eval H (batch parsed q batch0)).2 = true := by
    rw [← same0]
    exact source0
  have joined := CheckpointBytes5Decision.decision_success_join D hash H reserved
    wp wa proof public1 stored parsed q tr m i v guard parser query input view batchOk
    caller provenance p a after success
  simpa only [same0] using joined


#print axioms ordered_checkpoint_batches
end AspisR1.S2I.StageJoin
end
