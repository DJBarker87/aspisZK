import R16CanonExtractor
import OracleProgramLawExt

/-! Exact recorded observations and deployed-transport equivalence for the
total retagging. Schedule validity remains conditional as in the reduction. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.R16CanonRecorded
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound
open RawCutProverCompiler RawCutTranscriptRun RecordedBinaryExperimentBin
open R16CanonReduction R16CanonExtractor

/-- The actual original proof returned by the experiment is the prover output. -/
theorem original_proof (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State) :
    (eval H (original D d P)).2.1.2 = (eval H P).2.2 := by
  rw [RawCutProverCompiler.experiment_eval]

/-- Keep metadata construction abstract: observations use only its erasure. -/
theorem compiled_observations (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool)
    (build : RunView → CanonicalCutEnrichedTranscript.Words)
    (P : Prover) (H : Bytes → State) :
    Same (eval H (experiment (compiled D d build (canon P)) (verifier D d)))
      (eval H (experiment (compiled D d build P) (verifier D d))) ∧
    (eval H (experiment (compiled D d build (canon P)) (verifier D d))).2.2 =
      (eval H (experiment (compiled D d build P) (verifier D d))).2.2 := by
  have he : eval H (experiment (canon P) (verifier D d)) =
      ((eval H (original D d P)).1,
       (((eval H (original D d P)).2.1.1,
         R16CanonReduction.proof (eval H (original D d P)).2.1.2),
        (eval H (original D d P)).2.2)) := by
    rw [original_canon, original_proof]
  have hv : verifier D d (eval H (original D d P)).2.1.1
      (R16CanonReduction.proof (eval H (original D d P)).2.1.2) =
      verifier D d (eval H (original D d P)).2.1.1
        (eval H (original D d P)).2.1.2 :=
    verifier_congr D d _ _ _ (erase_proof _)
  simp only [compiled_experiment_eval, he]
  rw [hv]
  constructor
  · constructor
    · rfl
    · rfl
    · intro i
      exact (CanonicalCutEnrichedTranscript.erase_enrichMessage _ _).trans
        ((erase_proof _ i).trans (CanonicalCutEnrichedTranscript.erase_enrichMessage _ _).symm)
  · trivial

theorem recorded_observations (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State) :
    Same (eval H (recorded D d (canon P))) (eval H (recorded D d P)) ∧
      (eval H (recorded D d (canon P))).2.2 = (eval H (recorded D d P)).2.2 :=
  compiled_observations D d (BinCompiledRunWordStability.wordsFromRun D) P H

theorem recorded_extract (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State)
    (coins : GSConcreteByteDecoderBank.RawCoins) :
    RawRecordedPublicSpendExtractorBin.extract (eval H (recorded D d (canon P))) coins =
      RawRecordedPublicSpendExtractorBin.extract (eval H (recorded D d P)) coins :=
  extract_congr _ _ (recorded_observations D d P H).1 coins

theorem recorded_failure (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) :
    lazyMean (recorded D d (canon P)) emptyTable RawRecordedOracleExtractionMassBin.failureMass =
      lazyMean (recorded D d P) emptyTable RawRecordedOracleExtractionMassBin.failureMass := by
  apply OracleProgramLawExt.lazyMean_eq_of_eval
  intro H
  obtain ⟨same, accepted⟩ := recorded_observations D d P H
  exact failureMass_congr _ _ same accepted

theorem deployed_transport_iff (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (deployedFailure : ℚ) :
    DeployedTransport D d (canon P) deployedFailure ↔ DeployedTransport D d P deployedFailure := by
  unfold DeployedTransport
  rw [recorded_failure]

#print axioms original_proof
#print axioms compiled_observations
#print axioms recorded_observations
#print axioms recorded_extract
#print axioms recorded_failure
#print axioms deployed_transport_iff
end AspisR1.R16CanonRecorded
end
