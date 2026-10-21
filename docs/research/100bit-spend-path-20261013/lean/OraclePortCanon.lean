import OraclePortExperiment
import R16CanonRecorded

/-! Full-program retagging congruence for effectful decisions. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortCanon
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound
open RawCutProverCompiler (Public Proof Prover RunView experiment)
open R16CanonReduction (canon proof erase_proof eval_canon)
open OracleDecisionFeasibilityCore (Decision verifier original)
open OracleDecisionFeasibilityCompiler (compiled compiled_experiment_eval)
open R16CanonExtractor

/-- Erasure congruence holds for the full verifier program, including calls. -/
theorem verifier_congr (D : LiteralByteProtocol.Decoder)
    (d : Decision) (pub : LiteralTranscript.Public)
    (pf pf' : LiteralProtocol.Proof)
    (same : ∀ i, LiteralTranscript.erase (pf' i) = LiteralTranscript.erase (pf i)) :
    verifier D d pub pf' = verifier D d pub pf := by
  have aux (n : Nat) (a b : LiteralTranscript.Prefix)
      (hp : LiteralTranscript.erasePrefix a = LiteralTranscript.erasePrefix b) :
      OracleDecisionFeasibilityCore.verifierFrom D d pf' n a =
      OracleDecisionFeasibilityCore.verifierFrom D d pf n b := by
    induction n generalizing a b with
    | zero =>
      change d (LiteralTranscript.erasePrefix a) (LiteralTranscript.erase (pf' 33)) =
        d (LiteralTranscript.erasePrefix b) (LiteralTranscript.erase (pf 33))
      rw [hp, same]
    | succ n ih =>
      change bind (LiteralByteSampler.samp (33 - (n+1)) a (pf' (33 - (n+1)))).toProgram _ =
        bind (LiteralByteSampler.samp (33 - (n+1)) b (pf (33 - (n+1)))).toProgram _
      have hs : LiteralByteSampler.samp (33 - (n+1)) a (pf' (33 - (n+1))) =
          LiteralByteSampler.samp (33 - (n+1)) b (pf (33 - (n+1))) := by
        unfold LiteralByteSampler.samp LiteralTranscript.samp
        rw [hp, same]
      rw [hs]
      congr 1
      funext c
      apply ih
      change LiteralTranscript.erasePrefix (a.ext (pf' (33 - (n+1))) c) =
        LiteralTranscript.erasePrefix (b.ext (pf (33 - (n+1))) c)
      rw [LiteralTranscript.erasePrefix_ext, LiteralTranscript.erasePrefix_ext, hp, same]
  exact aux 33 _ _ rfl

theorem original_canon (D : LiteralByteProtocol.Decoder)
    (d : Decision) (P : Prover) (H : Bytes → State) :
    eval H (original D d (canon P)) =
      ((eval H (original D d P)).1,
       (((eval H (original D d P)).2.1.1, proof (eval H P).2.2),
        (eval H (original D d P)).2.2)) := by
  unfold original
  rw [RawCutProverCompiler.experiment_eval, RawCutProverCompiler.experiment_eval, eval_canon]
  dsimp only
  rw [verifier_congr D d _ _ _ (erase_proof _)]

/-- The actual original proof returned by the experiment is the prover output. -/
theorem original_proof (D : LiteralByteProtocol.Decoder)
    (d : Decision) (P : Prover) (H : Bytes → State) :
    (eval H (original D d P)).2.1.2 = (eval H P).2.2 := by
  unfold original
  rw [RawCutProverCompiler.experiment_eval]

/-- Keep metadata construction abstract: observations use only its erasure. -/
theorem compiled_observations (D : LiteralByteProtocol.Decoder)
    (d : Decision)
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
    change eval H (original D d (canon P)) = _
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
    (d : Decision) (P : Prover) (H : Bytes → State) :
    Same (eval H (OraclePortExperiment.recorded D d (canon P))) (eval H (OraclePortExperiment.recorded D d P)) ∧
      (eval H (OraclePortExperiment.recorded D d (canon P))).2.2 = (eval H (OraclePortExperiment.recorded D d P)).2.2 :=
  compiled_observations D d (BinCompiledRunWordStability.wordsFromRun D) P H

theorem recorded_extract (D : LiteralByteProtocol.Decoder)
    (d : Decision) (P : Prover) (H : Bytes → State)
    (coins : GSConcreteByteDecoderBank.RawCoins) :
    RawRecordedPublicSpendExtractorBin.extract (eval H (OraclePortExperiment.recorded D d (canon P))) coins =
      RawRecordedPublicSpendExtractorBin.extract (eval H (OraclePortExperiment.recorded D d P)) coins :=
  extract_congr _ _ (recorded_observations D d P H).1 coins

theorem recorded_failure (D : LiteralByteProtocol.Decoder)
    (d : Decision) (P : Prover) :
    lazyMean (OraclePortExperiment.recorded D d (canon P)) emptyTable RawRecordedOracleExtractionMassBin.failureMass =
      lazyMean (OraclePortExperiment.recorded D d P) emptyTable RawRecordedOracleExtractionMassBin.failureMass := by
  apply OracleProgramLawExt.lazyMean_eq_of_eval
  intro H
  obtain ⟨same, accepted⟩ := recorded_observations D d P H
  exact failureMass_congr _ _ same accepted

#print axioms verifier_congr
#print axioms original_canon
#print axioms original_proof
#print axioms compiled_observations
#print axioms recorded_observations
#print axioms recorded_extract
#print axioms recorded_failure
end AspisR1.OraclePortCanon
end
