import OracleDecisionFeasibilityCore
import R19BudgetOriginalReads

/-! Sampler queries and terminal decision queries are separate summands. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionFeasibilityBudget
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open RawCutTranscriptRun
open RawCutProverCompiler (Public Proof Prover experiment experiment_eval)
open OracleDecisionFeasibilityCore

theorem from_eval (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (H : Bytes → State) (pub : Public) (pf : Proof) :
    ∀ n, n ≤ 33 →
      eval H (verifierFrom D dO pf n
        ((LiteralByteProtocol.protocol D).transcript H pub pf (33 - n))) =
      let final := eval H (onBytes dO
        ((LiteralByteProtocol.protocol D).transcript H pub pf 33) (pf 33))
      ((((List.range n).map fun j => (eval H
        ((LiteralByteProtocol.protocol D).chain H pub pf (33 - n + j)).toProgram).1).flatten
        ++ final.1), final.2) := by
  intro n
  induction n with
  | zero => intro _; simp [OracleDecisionFeasibilityCore.verifierFrom]
  | succ n ih =>
    intro hn
    have hi : 33 - (n + 1) + 1 = 33 - n := by omega
    simp only [OracleDecisionFeasibilityCore.verifierFrom]
    rw [eval_bind]
    dsimp only
    have hstep :
        ((LiteralByteProtocol.protocol D).transcript H pub pf (33 - (n + 1))).ext
          (pf (33 - (n + 1)))
          (eval H (LiteralByteSampler.samp (33 - (n + 1))
            ((LiteralByteProtocol.protocol D).transcript H pub pf (33 - (n + 1)))
            (pf (33 - (n + 1)))).toProgram).2 =
          (LiteralByteProtocol.protocol D).transcript H pub pf (33 - n) := by
      rw [← hi]; rfl
    rw [hstep, ih (by omega)]
    apply Prod.ext _ rfl
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map, List.flatten_cons,
      List.append_assoc, Protocol.chain]
    congr 1
    congr 1
    congr 1
    apply List.map_congr_left
    intro j _
    simp only [Function.comp]
    have hj : 33 - (n + 1) + (j + 1) = 33 - n + j := by omega
    rw [hj]

theorem verifier_eval (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (H : Bytes → State) (pub : Public) (pf : Proof) :
    eval H (verifier D dO pub pf) =
      let final := eval H (onBytes dO
        ((LiteralByteProtocol.protocol D).transcript H pub pf 33) (pf 33))
      ((((List.range 33).map fun j => (eval H
        ((LiteralByteProtocol.protocol D).chain H pub pf j).toProgram).1).flatten
        ++ final.1), final.2) := by
  exact from_eval D dO H pub pf 33 le_rfl

theorem queries (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (H : Bytes → State) (pub : Public) (pf : Proof) (B : Nat)
    (hdecision : (eval H (onBytes dO
      ((LiteralByteProtocol.protocol D).transcript H pub pf 33) (pf 33))).1.length ≤ B) :
    (eval H (verifier D dO pub pf)).1.length ≤ 561 + B := by
  rw [verifier_eval, List.length_append]
  have hb := R19BudgetOriginalReads.verifier_queries D (fun _ _ => false) H pub pf
  unfold RawCutProverCompiler.verifier at hb
  rw [FS2.verifier_eval] at hb
  exact Nat.add_le_add hb hdecision

/-- A sufficient, explicit condition for retaining the existing total envelope.
561 is the sampler bound, not the cost of an arbitrary oracle decision. -/
theorem original_reads (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (P : Prover) (Q B : Nat) (H : Bytes → State)
    (hprover : (eval H P).1.length ≤ Q)
    (hdecision : ∀ pub pf, (eval H (onBytes dO
      ((LiteralByteProtocol.protocol D).transcript H pub pf 33) (pf 33))).1.length ≤ B)
    (hbudget : 561 + B ≤ 1161) :
    firstReads emptyTable (eval H (original D dO P)).1 ≤ Q + 1161 := by
  unfold original
  rw [RawCutProverCompiler.experiment_eval]
  have hv := queries D dO H (eval H P).2.1 (eval H P).2.2 B (hdecision _ _)
  have hb := VerifierCallBudget.firstReads_le_length emptyTable
    ((eval H P).1 ++ (eval H (verifier D dO (eval H P).2.1 (eval H P).2.2)).1)
  rw [List.length_append] at hb
  omega

#print axioms from_eval
#print axioms verifier_eval
#print axioms queries
#print axioms original_reads
end AspisR1.OracleDecisionFeasibilityBudget
end
