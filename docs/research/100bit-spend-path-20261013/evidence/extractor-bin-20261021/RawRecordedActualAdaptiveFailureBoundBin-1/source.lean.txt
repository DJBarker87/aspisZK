import RawRecordedOracleExtractionMassBin
import AcceptedAdaptiveFiatShamir
import RawAdaptiveClassifierStartBound

set_option autoImplicit false
noncomputable section
namespace AspisR1.RawRecordedActualAdaptiveFailureBoundBin

open FS FS2 R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.DecodedFirstReadUnionBound
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound
open AspisR1.AcceptedAdaptiveFiatShamir
open AspisR1.RawAdaptiveLiteralDecoder
open AspisR1.RawAdaptiveClassifierHitDensity
open AspisR1.RawAdaptiveClassifierStartBound
open AspisR1.RawRecordedOracleExtractionMassBin
open AspisR1.RawCutTranscriptRun
open AspisR1.RawCutWordsFromRunExecutableBin
open AspisR1.GenericNoHit

/-- Combine the recorded-run extractor failure theorem with the causal bound
for the actual decoder-start count. `hmodel` is the explicit source/format
premise: accepted executions outside collision and decoded classifier hits
have terminal Checks and no raw classifier hit. -/
theorem actual_recorded_failure_le_collision_add_start_density_add_abort
    (decoder : LiteralByteProtocol.Decoder)
    (pubChoice : RawAdaptiveLiteralDecoder.PublicChoice)
    (words : RawLiteralDecoderDensity.WordChoice)
    (P : RawCutProverCompiler.Prover)
    (V : LiteralTranscript.Public → LiteralProtocol.Proof → Program Bytes State Bool)
    (κ : Nat → ℚ) (Qtot N : Nat)
    (inj : AcceptedAdaptiveFiatShamir.LazyInj
      (LiteralByteProtocol.protocol decoder)
      (RawAdaptiveLiteralDecoder.decode pubChoice words) P V κ Qtot)
    (hmodel : RawRecordedOracleExtractionMassBin.CleanAcceptedModel decoder
      (AcceptedAdaptiveFiatShamir.experiment P V)
      (fun run => inj.Coll run ∨ hitsChain3 (RawAdaptiveLiteralDecoder.decode pubChoice words)
        RawAdaptiveClassifierHitDensity.classifier emptyTable run.1))
    (hN : ∀ H : Bytes → State, decoderFirstReads
      (RawAdaptiveLiteralDecoder.decode pubChoice words) emptyTable
      (eval H (AcceptedAdaptiveFiatShamir.experiment P V)).1 ≤ N) :
    lazyMean (AcceptedAdaptiveFiatShamir.experiment P V) emptyTable
      RawRecordedOracleExtractionMassBin.failureMass ≤
      (κ Qtot) + (N : ℚ) * PerAttemptEnvelope.B + (1 / (2 : ℚ)^126) := by
  let exp := AcceptedAdaptiveFiatShamir.experiment P V
  let hit : RawCutProverCompiler.RunView → Prop := fun run =>
    inj.Coll run ∨ hitsChain3 (RawAdaptiveLiteralDecoder.decode pubChoice words)
      RawAdaptiveClassifierHitDensity.classifier emptyTable run.1
  have hchain : lazyMean exp emptyTable (fun run => indicator
      (hitsChain3 (RawAdaptiveLiteralDecoder.decode pubChoice words)
        RawAdaptiveClassifierHitDensity.classifier emptyTable run.1)) ≤
      (N : ℚ) * PerAttemptEnvelope.B := by
    exact RawAdaptiveClassifierStartBound.shared_hit_mass_le_starts
      pubChoice words exp N hN
  have hhit : lazyMean exp emptyTable (fun run => indicator (hit run)) ≤
      (κ Qtot) + (N : ℚ) * PerAttemptEnvelope.B := by
    have hp : ∀ H : Bytes → State,
        indicator (hit (eval H exp)) ≤
          indicator (inj.Coll (eval H exp)) +
            indicator (hitsChain3 (RawAdaptiveLiteralDecoder.decode pubChoice words)
              RawAdaptiveClassifierHitDensity.classifier emptyTable (eval H exp).1) := by
      intro H
      dsimp only [hit]
      exact indicator_or_le _ _
    calc
      lazyMean exp emptyTable (fun run => indicator (hit run)) ≤
          lazyMean exp emptyTable (fun run => indicator (inj.Coll run) +
            indicator (hitsChain3 (RawAdaptiveLiteralDecoder.decode pubChoice words)
              RawAdaptiveClassifierHitDensity.classifier emptyTable run.1)) :=
        AllAddressFiatShamir.lazyMean_mono_of_eval exp _ _ hp
      _ = lazyMean exp emptyTable (fun run => indicator (inj.Coll run)) +
          lazyMean exp emptyTable (fun run => indicator (hitsChain3
            (RawAdaptiveLiteralDecoder.decode pubChoice words)
            RawAdaptiveClassifierHitDensity.classifier emptyTable run.1)) :=
        lazyMean_add _ _ _ _
      _ ≤ κ Qtot + (N : ℚ) * PerAttemptEnvelope.B := add_le_add inj.mass hchain
  have hfailure := RawRecordedOracleExtractionMassBin.shared_oracle_failure_le_supplied_hit_bound
    decoder exp hit hmodel _ hhit
  exact hfailure

#print axioms actual_recorded_failure_le_collision_add_start_density_add_abort
end AspisR1.RawRecordedActualAdaptiveFailureBoundBin
end
