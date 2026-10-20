import OracleDecisionMultiAccounting
import OracleDecisionMultiProfile
import OracleDecisionMultiRecovery
import OracleDecisionMultiNumeric

/-! Prerequisite composition only. No existing soundness signature is
changed and no ledger-refinement premise is claimed to be discharged. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionMultiSummary
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OracleDecisionFeasibilityCore OracleDecisionMultiTree OracleDecisionPrereqStarts
open OracleDecisionMultiAccounting OracleDecisionMultiProfile
open RawCutProverCompiler (Prover RunView)
open CanonicalCutEnrichedTranscript (Words)

/-- All three upper bounds concern the very same annotated experiment. -/
theorem prerequisites (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (cs : List Commitment) (duplicates frames : List Bytes) (words : RunView → Words)
    (P : Prover) (Q : Nat)
    (ha : Admissible cs duplicates frames) (hq : (eval H P).1.length ≤ Q) :
    firstReads emptyTable (eval H (annotated D (decision cs duplicates frames) words P)).1 ≤ Q + 1161 ∧
    DecodedFirstReadUnionBound.decoderFirstReads RecordedBinaryExperimentBin.dec emptyTable
      (eval H (annotated D (decision cs duplicates frames) words P)).1 ≤ Q + 1080 ∧
    (eval H (annotated D (decision cs duplicates frames) words P)).1.length ≤ Q + 2322 :=
  ⟨compiled_queries D H cs duplicates frames words P Q ha hq,
    safe_starts D H cs duplicates frames words P Q ha hq,
    log_length D H cs duplicates frames words P Q ha hq⟩

def shapeProof : RawCutProverCompiler.Proof := fun n =>
  if n = 0 then .initial 0 (fun _ => 0) else .payload ⟨[],by decide⟩

theorem shapeProof_valid : ∀ n < 33,
    OracleDecisionPrereqExact.Shape n (LiteralTranscript.erase (shapeProof n)) := by
  intro n _
  cases n with
  | zero => trivial
  | succ n => simp only [shapeProof, Nat.succ_ne_zero, if_false, LiteralTranscript.erase,
      OracleDecisionPrereqExact.Shape]

attribute [local irreducible] peak terminal decision verifier original annotated

/-- Accepted shared-model runs can attain 2322 recorded entries at Q=0.
This is a resource obstruction, not a claim about parsing a production proof. -/
theorem accepted_log_obstruction (D : LiteralByteProtocol.Decoder) (words : RunView → Words)
    (pub : LiteralTranscript.Public) :
    ∃ P : Prover, (eval (fun _ => (0 : State)) P).1.length = 0 ∧
      (eval (fun _ => (0 : State))
        (annotated D (decision peak [] (List.replicate 6 [])) words P)).2.2 = true ∧
      (eval (fun _ => (0 : State))
        (annotated D (decision peak [] (List.replicate 6 [])) words P)).1.length = 2322 ∧
      ¬ (eval (fun _ => (0 : State))
        (annotated D (decision peak [] (List.replicate 6 [])) words P)).1.length ≤ 1161 := by
  let P : Prover := .done (pub,shapeProof)
  have ha : (eval (fun _ => (0 : State))
      (original D (decision peak [] (List.replicate 6 [])) P)).2.2 = true := by
    rw [original, RawCutProverCompiler.experiment_eval, OracleDecisionFeasibilityBudget.verifier_eval]
    exact peak_accepts
  have hc := (OracleDecisionFeasibilityCompiler.public_and_acceptance D
    (decision peak [] (List.replicate 6 [])) words P (fun _ => (0 : State))).2
  have hl := full_profile_log D (fun _ => (0 : State)) peak [] (List.replicate 6 [])
    words pub shapeProof peak_admissible peak_counts.1 peak_counts.2.1 shapeProof_valid
  exact ⟨P,rfl,hc.trans ha,hl.1,hl.2⟩

#print axioms prerequisites
#print axioms shapeProof_valid
#print axioms accepted_log_obstruction
end AspisR1.OracleDecisionMultiSummary
end
