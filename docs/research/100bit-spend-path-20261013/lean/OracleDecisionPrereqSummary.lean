import OracleDecisionPrereqExact
import OracleDecisionPrereqObstruction
import OracleDecisionPrereqNumeric

/-! Prerequisite accounting bridge only. No soundness endpoint is ported. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionPrereqSummary
open FS FS2 FS2.Duplex R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OracleDecisionFeasibilityCore OracleDecisionPrereqPaths OracleDecisionPrereqStarts
open RawCutProverCompiler (Prover RunView)
open CanonicalCutEnrichedTranscript (Words)

theorem compiled_query_budget (D : LiteralByteProtocol.Decoder)
    (os : List Opening) (frames : List Bytes) (words : RunView → Words)
    (P : Prover) (H : Bytes → State) (Q q d : Nat)
    (hq : (eval H P).1.length ≤ Q) (hc : os.length = 3*q)
    (hd : ∀ o ∈ os, o.slots.length = d) :
    firstReads emptyTable
      (eval H (annotated D (OracleDecisionPrereqPaths.decision os frames) words P)).1 ≤
      Q + B_V q d frames.length := by
  rw [annotated, OracleDecisionFeasibilityCompiler.firstReads_eq]
  exact original_budget D os frames P H Q q d hq hc hd

/-- All three safe constants concern the SAME explicit oracle experiment.
No h_R19, zero-start, or log-size premise is supplied to this theorem. -/
theorem prerequisites (D : LiteralByteProtocol.Decoder)
    (os : List Opening) (frames : List Bytes) (words : RunView → Words)
    (P : Prover) (H : Bytes → State) (Q : Nat)
    (hq : (eval H P).1.length ≤ Q) (hc : os.length = 66)
    (hd : ∀ o ∈ os, o.slots.length = 18) (hf : frames.length = 6) :
    firstReads emptyTable
      (eval H (annotated D (OracleDecisionPrereqPaths.decision os frames) words P)).1 ≤ Q + 1375 ∧
    DecodedFirstReadUnionBound.decoderFirstReads RecordedBinaryExperimentBin.dec emptyTable
      (eval H (annotated D (OracleDecisionPrereqPaths.decision os frames) words P)).1 ≤ Q + 1294 ∧
    (eval H (annotated D (OracleDecisionPrereqPaths.decision os frames) words P)).1.length ≤ Q + 2750 := by
  have hb := compiled_query_budget D os frames words P H Q 22 18 hq hc hd
  have hl := OracleDecisionPrereqLog.paths_log_length D os frames words P H Q 22 18 hq hc hd
  rw [hf] at hb hl
  refine ⟨?_, frozen_starts D os frames words P H Q hq hc hd hf, ?_⟩
  · simpa [B_V, Nat.add_assoc] using hb
  · simpa [B_V, Nat.add_assoc] using hl

/-- Reuse the old extractor size-envelope shape at a shifted ledger
parameter. This does not assert the ledger refinement at that parameter. -/
theorem existing_offset_reindex (D : LiteralByteProtocol.Decoder)
    (os : List Opening) (frames : List Bytes) (words : RunView → Words)
    (P : Prover) (H : Bytes → State) (Q : Nat)
    (hq : (eval H P).1.length ≤ Q) (hc : os.length = 66)
    (hd : ∀ o ∈ os, o.slots.length = 18) (hf : frames.length = 6) :
    (eval H (annotated D (OracleDecisionPrereqPaths.decision os frames) words P)).1.length ≤
      (Q + 1589) + 1161 := by
  have hl := (prerequisites D os frames words P H Q hq hc hd hf).2.2
  omega

#print axioms compiled_query_budget
#print axioms prerequisites
#print axioms existing_offset_reindex
end AspisR1.OracleDecisionPrereqSummary
end
