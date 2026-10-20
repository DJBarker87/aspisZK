import OracleDecisionMultiBuild

/-! Compiler accounting for the same shared-tree decision. This is additive
prerequisite work, not ledger instrumentation or an endpoint port. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionMultiAccounting
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OracleDecisionFeasibilityCore OracleDecisionMultiTree OracleDecisionPrereqStarts
open RawCutProverCompiler (Prover RunView)
open CanonicalCutEnrichedTranscript (Words)

theorem original_queries (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (cs : List Commitment) (duplicates frames : List Bytes) (P : Prover) (Q : Nat)
    (ha : Admissible cs duplicates frames) (hq : (eval H P).1.length ≤ Q) :
    firstReads emptyTable (eval H (original D (decision cs duplicates frames) P)).1 ≤ Q + 1161 := by
  rw [original, RawCutProverCompiler.experiment_eval]
  have hv := verifier_budget D H cs duplicates frames (eval H P).2.1 (eval H P).2.2 ha
  have hr := VerifierCallBudget.firstReads_le_length emptyTable
    ((eval H P).1 ++ (eval H (verifier D (decision cs duplicates frames)
      (eval H P).2.1 (eval H P).2.2)).1)
  rw [List.length_append] at hr
  dsimp only
  omega

theorem compiled_queries (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (cs : List Commitment) (duplicates frames : List Bytes) (words : RunView → Words)
    (P : Prover) (Q : Nat)
    (ha : Admissible cs duplicates frames) (hq : (eval H P).1.length ≤ Q) :
    firstReads emptyTable (eval H (annotated D (decision cs duplicates frames) words P)).1 ≤ Q + 1161 := by
  rw [annotated, OracleDecisionFeasibilityCompiler.firstReads_eq]
  exact original_queries D H cs duplicates frames P Q ha hq

/-- The current annotation compiler executes the full verifier twice. This
uses its exact log identity, not the number of distinct first reads. -/
theorem log_length (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (cs : List Commitment) (duplicates frames : List Bytes) (words : RunView → Words)
    (P : Prover) (Q : Nat)
    (ha : Admissible cs duplicates frames) (hq : (eval H P).1.length ≤ Q) :
    (eval H (annotated D (decision cs duplicates frames) words P)).1.length ≤ Q + 2322 := by
  have hl := OracleDecisionPrereqLog.bounded_compiled_length D
    (decision cs duplicates frames) words P H Q 1161 hq
    (fun pub pf => verifier_budget D H cs duplicates frames pub pf ha)
  omega

/-- Reindexing only. This does not prove LedgerRefinement at the shifted Q. -/
theorem ledger_size_reindex (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (cs : List Commitment) (duplicates frames : List Bytes) (words : RunView → Words)
    (P : Prover) (Q : Nat)
    (ha : Admissible cs duplicates frames) (hq : (eval H P).1.length ≤ Q) :
    (eval H (annotated D (decision cs duplicates frames) words P)).1.length ≤
      (Q + 1161) + 1161 := by
  have := log_length D H cs duplicates frames words P Q ha hq
  omega

/-- Safe starts without byte/table-specific rejection. It is not a sharp
claim and does not discharge the requested zero-terminal-start theorem. -/
theorem safe_starts (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (cs : List Commitment) (duplicates frames : List Bytes) (words : RunView → Words)
    (P : Prover) (Q : Nat)
    (ha : Admissible cs duplicates frames) (hq : (eval H P).1.length ≤ Q) :
    DecodedFirstReadUnionBound.decoderFirstReads RecordedBinaryExperimentBin.dec emptyTable
      (eval H (annotated D (decision cs duplicates frames) words P)).1 ≤ Q + 1080 := by
  have ht := closed_count H cs duplicates frames ha
  have hb := budget_bound cs duplicates frames ha
  have hs := recorded_starts D (decision cs duplicates frames) words P H Q 1046 hq
    (by
      intro pub pf T
      change DecodedFirstReadUnionBound.decoderFirstReads _ T
        (eval H (terminal cs duplicates frames)).1 ≤ 1046
      have := DecoderQueryAccounting.starts_le_queries RecordedBinaryExperimentBin.dec T
        (eval H (terminal cs duplicates frames)).1
      omega)
  omega

#print axioms original_queries
#print axioms compiled_queries
#print axioms log_length
#print axioms ledger_size_reindex
#print axioms safe_starts
end AspisR1.OracleDecisionMultiAccounting
end
