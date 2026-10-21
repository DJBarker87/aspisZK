import StartChargeClean

/-! Restricted classifier mass, with the full experiment's collision budget
left unchanged. Observational transport uses the finite-support oracle law. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.StartChargeProbability
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound
open OraclePortStoredExperimentC4 OraclePortFrozenOrderConsumer
open RawRecordedOracleExtractionMassBin StartChargePrefix StartChargeClean
attribute [local irreducible] R0C.V3.hitsChain3 GenericNoHit.hitFrom LiteralClassifier.bad

/-- The restricted event is measured under the unchanged full adaptive
experiment. Its mass equals the event in the actual charged prefix. -/
theorem hit_mass (D : LiteralByteProtocol.Decoder) (P : Prover) :
    lazyMean (projected D P) emptyTable (fun run => indicator (prefixHit D P run)) =
      lazyMean (charged D P) emptyTable (fun run => indicator
        (hitsChain3 RecordedBinaryExperimentBin.dec RawAdaptiveClassifierHitDensity.classifier
          emptyTable run.1)) := by
  apply OracleProgramLawExt.lazyMean_eq_of_eval
  intro H
  unfold prefixHit
  rw [recovered_eval]

/-- Only the prover and the followed sampler prefix receive per-start mass B. -/
theorem restricted_union_bound (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
    lazyMean (projected D P) emptyTable (fun run => indicator (prefixHit D P run)) ≤
      ((Q+34 : Nat) : ℚ)*PerAttemptEnvelope.B := by
  rw [hit_mass]
  exact RawAdaptiveClassifierStartBound.shared_hit_mass_le_starts
    RawFullPublicSelection.select LiteralTableWordChoiceBin.choose (charged D P) (Q+34)
    (starts D P Q hq)

/-- The original full accepted-extractor failure event, for every Q, with
no lower bound and no new cryptographic or source-refinement premise. -/
theorem failure_bound (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
    lazyMean (projected D P) emptyTable failureMass ≤
      BinCombinedMerkleCollision.kappa (Q+1161) +
        ((Q+34 : Nat) : ℚ)*PerAttemptEnvelope.B + 1/(2:ℚ)^126 := by
  have hc := BinCombinedMerkleCollision.mass SelectedTranscriptParams.params.iv
    (Q+1161) (projected D P) (OraclePortFrozenOrderProbability.first_reads D P Q hq)
  have hs := restricted_union_bound D P Q hq
  apply shared_oracle_failure_le_supplied_hit_bound D (projected D P) (StartChargeClean.bad D P Q)
    (StartChargeClean.clean D P Q hq)
  calc
    lazyMean (projected D P) emptyTable (fun run => indicator (StartChargeClean.bad D P Q run)) ≤
        lazyMean (projected D P) emptyTable (fun run =>
          indicator (RecordedBinaryExperimentBin.binaryCollision (Q+1161) run) +
          indicator (prefixHit D P run)) :=
      AllAddressFiatShamir.lazyMean_mono_of_eval _ _ _ (fun _ => indicator_or_le _ _)
    _ = _ := lazyMean_add _ _ _ _
    _ ≤ _ := add_le_add hc hs

#print axioms hit_mass
#print axioms restricted_union_bound
#print axioms failure_bound
end AspisR1.StartChargeProbability
end
