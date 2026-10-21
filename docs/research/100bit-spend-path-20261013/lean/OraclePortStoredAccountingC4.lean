import OraclePortStoredExperimentC4

/-! Re-establish the conservative port envelopes for an adaptively selected
stored proof. No fixed old decision is assumed across oracle executions. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortStoredAccountingC4
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open DecodedFirstReadUnionBound
open OraclePortStoredExperimentC4

theorem distinct_bound (D : LiteralByteProtocol.Decoder) (d : Decision)
    (build : RawCutProverCompiler.RunView → CanonicalCutEnrichedTranscript.Words)
    (P : Prover) (Q : Nat) (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (hb : Budget d) (H : Bytes → State) :
    firstReads emptyTable (eval H (recorded D d build P)).1 ≤ Q+1161 := by
  rw [first_reads,original_eval]
  dsimp only
  have hv := verifier_budget D d hb H (eval H P).2
  have hp := hq H
  have bound := VerifierCallBudget.firstReads_le_length emptyTable
    ((eval H P).1 ++ (eval H (verifier D d (eval H P).2)).1)
  rw [List.length_append] at bound
  omega

theorem compiler_starts (D : LiteralByteProtocol.Decoder) (d : Decision)
    (build : RawCutProverCompiler.RunView → CanonicalCutEnrichedTranscript.Words)
    (P : Prover) (H : Bytes → State) :
    decoderFirstReads RecordedBinaryExperimentBin.dec emptyTable
      (eval H (recorded D d build P)).1 =
    decoderFirstReads RecordedBinaryExperimentBin.dec emptyTable
      (eval H (original D d P)).1 := by
  rw [recorded_eval,original_eval]
  exact decoderFirstReads_repeat_suffix _ _ _

theorem starts_bound (D : LiteralByteProtocol.Decoder) (d : Decision)
    (build : RawCutProverCompiler.RunView → CanonicalCutEnrichedTranscript.Words)
    (P : Prover) (Q : Nat) (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (hb : Budget d) (H : Bytes → State) :
    decoderFirstReads RecordedBinaryExperimentBin.dec emptyTable
      (eval H (recorded D d build P)).1 ≤ Q+1080 := by
  rw [compiler_starts,original_eval,decoderFirstReads_append]
  have hp := (DecoderQueryAccounting.starts_le_queries RecordedBinaryExperimentBin.dec
    emptyTable (eval H P).1).trans (hq H)
  have hv := OracleDecisionPrereqStarts.verifier_starts D (d (eval H P).2.stored) H
    (eval H P).2.statement (eval H P).2.proof (applyTrace emptyTable (eval H P).1)
    1046 (fun T => (DecoderQueryAccounting.starts_le_queries _ T _).trans
      (hb (eval H P).2.stored H _ _))
  change decoderFirstReads RecordedBinaryExperimentBin.dec
    (applyTrace emptyTable (eval H P).1)
    (eval H (verifier D d (eval H P).2)).1 ≤ 34+1046 at hv
  omega

#print axioms distinct_bound
#print axioms compiler_starts
#print axioms starts_bound
end AspisR1.OraclePortStoredAccountingC4
end
