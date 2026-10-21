import OraclePortStoredPoolC4

/-! Same-oracle saved-packet replay with an adaptive stored-proof input.
This proves the logical resumed observation, not the physical ABI join. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortStoredPoolReplayC4
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4
open OraclePortStoredPoolC4

/-- The recorded raw prefix retains exactly the original prover log. -/
theorem prepare_original (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (H : Bytes → State) :
    let raw := (eval H (prepare D P)).2
    embed raw.stored (eval H (OraclePortCheckpoint.base (d raw.stored) raw.legacy)).2 =
      eval H (original D d P) := by
  have hv := OraclePortCheckpoint.rounds_terminal D (d (eval H P).2.stored)
    (eval H P).2.proof H 33 (FS.emptyPrefix (eval H P).2.statement)
  change eval H (verifier D d (eval H P).2) = _ at hv
  rw [original_eval,hv]
  simp only [prepare,eval_bind,OracleProgramRecording.eval_record,eval,
    OraclePortCheckpoint.base,embed,List.append_nil,List.append_assoc]

/-- Unpacking the larger carrier recovers precisely the old RunView needed
by the word builder, while retaining the full stored bytes separately. -/
theorem view_embed (stored : Bytes) (v : RawCutProverCompiler.RunView) :
    view (embed stored v) = v := rfl

/-- Exact logical accepted-resume identity; no extra distributional premise.
The matching guard remains part of resume and is discharged by acceptance. -/
theorem resume_recorded (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (H : Bytes → State) (c : Checkpoint)
    (written : write (eval H (prepare D P)).2 = some c)
    (accepted : (eval H (resume D d c)).2.2.2 = true) :
    (eval H (resume D d c)).2 =
      eval H (recorded D d (BinCompiledRunWordStability.wordsFromRun D) P) := by
  have fields := write_fields _ _ written
  have hb : embed c.stored
      (eval H (OraclePortCheckpoint.base (d c.stored) c.legacy.raw)).2 =
      eval H (original D d P) := by
    rw [fields.1,fields.2]
    exact prepare_original D d P H
  have old : (eval H (OraclePortCheckpoint.base (d c.stored) c.legacy.raw)).2 =
      view (eval H (original D d P)) := by
    rw [← hb,view_embed]
  have stored : c.stored = (eval H (original D d P)).2.1.stored := by
    rw [← hb]; rfl
  have guard : R16DecisionCheckpoint.tx2 (R16DecisionCheckpoint.resume c.legacy.saved) = true := by
    simp only [resume,OraclePortCheckpoint.resume,eval_bind,
      OracleProgramRecording.eval_record,eval,embed] at accepted
    exact (Bool.and_eq_true_iff.mp accepted).1
  rw [recorded_eval]
  simp only [resume,OraclePortCheckpoint.resume,eval_bind,
    OracleProgramRecording.eval_record,eval,List.append_nil]
  rw [old,guard,Bool.true_and]
  simp only [embed,view,enrich]
  rw [stored]
  rfl

#print axioms prepare_original
#print axioms view_embed
#print axioms resume_recorded
end AspisR1.OraclePortStoredPoolReplayC4
end
