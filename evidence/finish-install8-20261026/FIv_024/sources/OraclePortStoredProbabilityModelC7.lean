import OraclePortStoredProbabilityC7

/-! Stored-aware M9 consumer. Projection preserves every oracle read and
exactly the failure observable; kappa and B are inherited unchanged. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortStoredProbabilityModelC7
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.AdaptiveFirstReadLaw
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4
open OraclePortStoredConsumerC7 RawRecordedOracleExtractionMassBin

theorem failure_bound_of_clean (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (hmodel : CleanAcceptedModel D (projected D P) (bad Q)) :
    lazyMean (projected D P) emptyTable failureMass ≤
      BinCombinedMerkleCollision.kappa (Q+1161) +
        ((Q+1080 : Nat) : ℚ)*PerAttemptEnvelope.B + 1/(2:ℚ)^126 := by
  have hc := BinCombinedMerkleCollision.mass SelectedTranscriptParams.params.iv
    (Q+1161) (projected D P) (OraclePortStoredProbabilityC7.first_reads D P Q hq)
  have hs := RawAdaptiveClassifierStartBound.shared_hit_mass_le_starts
    RawFullPublicSelection.select LiteralTableWordChoiceBin.choose (projected D P) (Q+1080)
    (OraclePortStoredProbabilityC7.starts D P Q hq)
  apply shared_oracle_failure_le_supplied_hit_bound D (projected D P) (bad Q) hmodel
  calc
    lazyMean (projected D P) emptyTable (fun run => indicator (bad Q run)) ≤
        lazyMean (projected D P) emptyTable (fun run =>
          indicator (RecordedBinaryExperimentBin.binaryCollision (Q+1161) run) +
          indicator (hitsChain3 RecordedBinaryExperimentBin.dec
            RawAdaptiveClassifierHitDensity.classifier emptyTable run.1)) :=
      AllAddressFiatShamir.lazyMean_mono_of_eval _ _ _ (fun _ => indicator_or_le _ _)
    _ = _ := lazyMean_add _ _ _ _
    _ ≤ _ := add_le_add hc hs

#print axioms failure_bound_of_clean
end AspisR1.OraclePortStoredProbabilityModelC7
end
