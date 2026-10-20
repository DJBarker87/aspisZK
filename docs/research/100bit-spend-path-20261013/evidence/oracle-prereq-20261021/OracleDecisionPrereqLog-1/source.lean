import OracleDecisionPrereqStarts

/-! Recorded log length counts both verifier executions. No M10 ledger or
endpoint is changed. The bounds below hold even on rejected runs. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionPrereqLog
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OracleDecisionFeasibilityCore OracleDecisionPrereqStarts
open RawCutProverCompiler (Prover RunView)
open CanonicalCutEnrichedTranscript (Words)

theorem compiled_length (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (words : RunView → Words) (P : Prover) (H : Bytes → State) :
    (eval H (annotated D dO words P)).1.length =
      (eval H P).1.length +
        2 * (eval H (verifier D dO (eval H P).2.1 (eval H P).2.2)).1.length := by
  rw [annotated, OracleDecisionFeasibilityCompiler.compiled_experiment_eval,
    RawCutProverCompiler.experiment_eval]
  simp only [List.length_append]
  omega

theorem bounded_compiled_length (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (words : RunView → Words) (P : Prover) (H : Bytes → State) (Q B : Nat)
    (hq : (eval H P).1.length ≤ Q)
    (hv : ∀ pub pf, (eval H (verifier D dO pub pf)).1.length ≤ B) :
    (eval H (annotated D dO words P)).1.length ≤ Q + B + B := by
  rw [compiled_length]
  have hb := hv (eval H P).2.1 (eval H P).2.2
  omega

theorem paths_log_length (D : LiteralByteProtocol.Decoder)
    (os : List OracleDecisionPrereqPaths.Opening) (frames : List Bytes)
    (words : RunView → Words) (P : Prover) (H : Bytes → State) (Q q d : Nat)
    (hq : (eval H P).1.length ≤ Q) (hc : os.length = 3*q)
    (hd : ∀ o ∈ os, o.slots.length = d) :
    (eval H (annotated D (OracleDecisionPrereqPaths.decision os frames) words P)).1.length ≤
      Q + OracleDecisionPrereqPaths.B_V q d frames.length +
        OracleDecisionPrereqPaths.B_V q d frames.length :=
  bounded_compiled_length D _ words P H Q _ hq
    (fun pub pf => OracleDecisionPrereqPaths.verifier_budget D os frames H pub pf q d hc hd)

/-- Accepted-run M10 size premise with the corrected constant; acceptance
is not needed by the proof. The old Q+1161 premise is not discharged. -/
theorem accepted_log_length (D : LiteralByteProtocol.Decoder)
    (os : List OracleDecisionPrereqPaths.Opening) (frames : List Bytes)
    (words : RunView → Words) (P : Prover) (H : Bytes → State) (Q : Nat)
    (hq : (eval H P).1.length ≤ Q) (hc : os.length = 66)
    (hd : ∀ o ∈ os, o.slots.length = 18) (hf : frames.length = 6)
    (_hacc : (eval H (annotated D (OracleDecisionPrereqPaths.decision os frames) words P)).2.2 = true) :
    (eval H (annotated D (OracleDecisionPrereqPaths.decision os frames) words P)).1.length ≤
      Q + 2750 := by
  have hb := paths_log_length D os frames words P H Q 22 18 hq hc hd
  rw [hf] at hb
  simpa [OracleDecisionPrereqPaths.B_V, Nat.add_assoc] using hb

/-- Terminal replay alone rules out offsets below 2520 at Q=0,
independently of repeated addresses and of sampler validity. -/
theorem terminal_replay_lower (D : LiteralByteProtocol.Decoder)
    (os : List OracleDecisionPrereqPaths.Opening) (frames : List Bytes)
    (words : RunView → Words) (P : Prover) (H : Bytes → State)
    (hc : os.length = 66) (hd : ∀ o ∈ os, o.slots.length = 18) (hf : frames.length = 6) :
    2520 ≤ (eval H (annotated D (OracleDecisionPrereqPaths.decision os frames) words P)).1.length := by
  rw [compiled_length, OracleDecisionFeasibilityBudget.verifier_eval, List.length_append]
  have ht := OracleDecisionPrereqPaths.frozen_terminal_count os frames H hc hd hf
  change 2520 ≤ (eval H P).1.length + 2 * (_ + (eval H (OracleDecisionPrereqPaths.terminal os frames)).1.length)
  omega

#print axioms compiled_length
#print axioms bounded_compiled_length
#print axioms paths_log_length
#print axioms accepted_log_length
#print axioms terminal_replay_lower
end AspisR1.OracleDecisionPrereqLog
end
