import OracleDecisionPrereqLog

/-! Accepted-run obstruction to retaining the current M10 log constant for
independent paths. A constant oracle is permitted: M10 covers colliding runs. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionPrereqObstruction
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OracleDecisionFeasibilityCore OracleDecisionFeasibilityMerkle
open OracleDecisionPrereqPaths OracleDecisionPrereqStarts
open RawCutProverCompiler (Prover RunView)
open CanonicalCutEnrichedTranscript (Words)

theorem constant_fold {slots : List (Fin 2)} (path : BinMerkle32Path.Path slots)
    (r : State) : BinMerkle32Path.foldPath (fun _ => r) path r = r := by
  induction path with
  | nil => rfl
  | cons siblings tail ih => exact ih

theorem constant_check (o : Opening) (r : State) (hr : o.root = r) :
    (eval (fun _ => r) (checkPath o.path o.leaf o.root)).2 = true := by
  rw [eval_check, BinMerkleProgram.eval_leafProgram]
  change decide (BinMerkle32Path.foldPath (fun _ => r) o.path r = o.root) = true
  rw [constant_fold, hr]
  simp

theorem constant_all (os : List Opening) (r : State)
    (hr : ∀ o ∈ os, o.root = r) :
    (eval (fun _ => r) (checkAll os)).2 = true := by
  induction os with
  | nil => rfl
  | cons o os ih =>
    simp only [checkAll, eval_bind, eval]
    rw [constant_check o r (hr o (by simp)), ih (fun x hx => hr x (by simp [hx]))]
    rfl

theorem accepted_log_obstruction (D : LiteralByteProtocol.Decoder)
    (os : List Opening) (frames : List Bytes) (r : State)
    (words : RunView → Words) (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof)
    (hc : os.length = 66) (hd : ∀ o ∈ os, o.slots.length = 18) (hf : frames.length = 6)
    (hr : ∀ o ∈ os, o.root = r) :
    ∃ P : Prover, (eval (fun _ => r) P).1.length = 0 ∧
      (eval (fun _ => r) (annotated D (OracleDecisionPrereqPaths.decision os frames) words P)).2.2 = true ∧
      1161 < (eval (fun _ => r) (annotated D (OracleDecisionPrereqPaths.decision os frames) words P)).1.length ∧
      1375 + 115 < (eval (fun _ => r)
        (annotated D (OracleDecisionPrereqPaths.decision os frames) words P)).1.length := by
  let P : Prover := .done (pub, pf)
  have ha : (eval (fun _ => r) (original D (OracleDecisionPrereqPaths.decision os frames) P)).2.2 = true := by
    rw [original, RawCutProverCompiler.experiment_eval, OracleDecisionFeasibilityBudget.verifier_eval]
    change (eval (fun _ => r) (terminal os frames)).2 = true
    simpa only [terminal, eval_bind] using constant_all os r hr
  have hac := (OracleDecisionFeasibilityCompiler.public_and_acceptance D
    (OracleDecisionPrereqPaths.decision os frames) words P (fun _ => r)).2
  have hl := OracleDecisionPrereqLog.terminal_replay_lower D os frames words P
    (fun _ => r) hc hd hf
  refine ⟨P, rfl, ?_, by omega, by omega⟩
  exact hac.trans ha

#print axioms constant_fold
#print axioms constant_check
#print axioms constant_all
#print axioms accepted_log_obstruction
end AspisR1.OracleDecisionPrereqObstruction
end
