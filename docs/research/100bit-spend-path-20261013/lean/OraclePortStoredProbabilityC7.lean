import OraclePortStoredConsumerC7
import OraclePortPureOutputC7
import OraclePortHeadline

/-! Stored-aware M9 consumer. Projection preserves every oracle read and
exactly the failure observable; kappa and B are inherited unchanged. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortStoredProbabilityC7
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.AdaptiveFirstReadLaw
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4
open OraclePortStoredConsumerC7 RawRecordedOracleExtractionMassBin

/-- Equality under the actual memoized probability law, for every observable.
In particular failure, collision and chain-hit events are unchanged. -/
theorem mass_projection (D : LiteralByteProtocol.Decoder) (P : Prover)
    (observe : RawCutProverCompiler.RunView → ℚ) :
    lazyMean (projected D P) emptyTable observe =
      lazyMean (annotated D dV (canon P)) emptyTable (fun v => observe (view v)) :=
  OraclePortPureOutputC7.lazyMean_map _ _ _ _

theorem first_reads (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) (H : Bytes → State) :
    firstReads emptyTable (eval H (projected D P)).1 ≤ Q+1161 := by
  rw [projected_eval]
  exact OraclePortStoredAccountingC4.distinct_bound D dV (build D) (canon P) Q
    (fun H => by rw [canon_eval]; exact hq H)
    OraclePortStoredDecisionDraftC4.decision_budget H

theorem starts (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) (H : Bytes → State) :
    DecodedFirstReadUnionBound.decoderFirstReads RecordedBinaryExperimentBin.dec emptyTable
      (eval H (projected D P)).1 ≤ Q+1080 := by
  rw [projected_eval]
  exact OraclePortStoredAccountingC4.starts_bound D dV (build D) (canon P) Q
    (fun H => by rw [canon_eval]; exact hq H)
    OraclePortStoredDecisionDraftC4.decision_budget H

theorem log_length (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) (H : Bytes → State) :
    (eval H (projected D P)).1.length ≤ Q+2322 := by
  rw [projected_eval]
  exact recorded_length D dV (build D) (canon P) Q
    (fun H => by rw [canon_eval]; exact hq H)
    OraclePortStoredDecisionDraftC4.decision_budget H

/-- The inherited binary union bound on the unchanged adaptive experiment. -/
theorem failure_bound (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
    lazyMean (projected D P) emptyTable failureMass ≤
      BinCombinedMerkleCollision.kappa (Q+1161) +
        ((Q+1080 : Nat) : ℚ)*PerAttemptEnvelope.B + 1/(2:ℚ)^126 := by
  have hc := BinCombinedMerkleCollision.mass SelectedTranscriptParams.params.iv
    (Q+1161) (projected D P) (first_reads D P Q hq)
  have hs := RawAdaptiveClassifierStartBound.shared_hit_mass_le_starts
    RawFullPublicSelection.select LiteralTableWordChoiceBin.choose (projected D P) (Q+1080)
    (starts D P Q hq)
  apply shared_oracle_failure_le_supplied_hit_bound D (projected D P) (bad Q) (clean D P Q hq)
  calc
    lazyMean (projected D P) emptyTable (fun run => indicator (bad Q run)) ≤
        lazyMean (projected D P) emptyTable (fun run =>
          indicator (RecordedBinaryExperimentBin.binaryCollision (Q+1161) run) +
          indicator (hitsChain3 RecordedBinaryExperimentBin.dec
            RawAdaptiveClassifierHitDensity.classifier emptyTable run.1)) :=
      AllAddressFiatShamir.lazyMean_mono_of_eval _ _ _ (fun _ => indicator_or_le _ _)
    _ = _ := lazyMean_add _ _ _ _
    _ ≤ _ := add_le_add hc hs

/-- The same bound stated directly on the stored carrier. -/
theorem stored_failure_bound (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
    lazyMean (annotated D dV (canon P)) emptyTable (fun v => failureMass (view v)) ≤
      BinCombinedMerkleCollision.kappa (Q+1161) +
        ((Q+1080 : Nat) : ℚ)*PerAttemptEnvelope.B + 1/(2:ℚ)^126 := by
  rw [← mass_projection]
  exact failure_bound D P Q hq

#print axioms mass_projection
#print axioms first_reads
#print axioms starts
#print axioms log_length
#print axioms failure_bound
#print axioms stored_failure_bound
end AspisR1.OraclePortStoredProbabilityC7
end
