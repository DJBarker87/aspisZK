import AspisFormal.K1.V7Tag73ExactRestoredCleanPairSemanticNoninterference

/-!
# Exact restoration-wide K1.3 query probability

The restoration-wide classifier fails only if its canonical accepted root also
fails.  For the q16 branch, the root failure exposes the literal accepted
final-work trial.  The corrected 518-coordinate pair factorization then fixes
the residual, all four alpha blocks, fold work and final work before leaving
the successful q16 forest as the sole random fibre.

This file connects those two already-proved facts.  It does not treat the
adaptive accepted-root challenge as uniform and introduces no grinding
normalization or independence premise.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73ExactRestoredOperationalK13QueryProbability

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRestoredCleanPairFactorization
open AspisK1.V7Tag73ExactRestoredCleanPairSemanticNoninterference
open AspisK1.V7Tag73ExactRestoredOperationalK13Events
open AspisK1.V7Tag73ExactRestoredQ16ResidualFactorization
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The exact compiler-clean canonical-root q16 event is bounded by one
semantic cap-203 forest.  The proof first exposes the actual final-work trial
from source execution and then invokes the sound two-work-trial factorization.
-/
theorem exact_restored_operational_canonical_root_k13_query_probability_le
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (frontierExact : ∀
      (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (schedule : QuerySchedule),
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions)
    (semantic : ExactRestoredRootCleanK13PairSemanticInvariant transitionFuel
      configuration projection fixedInstance decoder)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (foldExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 31)
    (finalExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 34) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
            projection fixedInstance ∩
          exactTag73RestoredOperationalCanonicalRootK13QueryEvent
            transitionFuel configuration projection fixedInstance decoder) ≤
      q16SemanticOneForestRawError := by
  let clean := exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
    projection fixedInstance
  let query := exactTag73RestoredOperationalCanonicalRootK13QueryEvent
    transitionFuel configuration projection fixedInstance decoder
  have covered :
      clean ∩ query ⊆
        clean ∩
          ⋃ finalTrial : ExactCompilerExposureTrial parameters,
            exactRestoredRootK13JointTrialEvent transitionFuel configuration
              projection fixedInstance decoder finalTrial := by
    rintro sample ⟨cleanMember, queryMember⟩
    obtain ⟨trial, trialMember⟩ :=
      exact_restored_root_query_failure_has_joint_trial_witness
        transitionRoom (le_trans (by omega : 513 ≤ 518) programmedCover)
        (fun input schedule => frontierExact sample input schedule) queryMember
    exact ⟨cleanMember, Set.mem_iUnion.mpr ⟨trial, trialMember⟩⟩
  calc
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ query) ≤
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩
          ⋃ finalTrial : ExactCompilerExposureTrial parameters,
            exactRestoredRootK13JointTrialEvent transitionFuel configuration
              projection fixedInstance decoder finalTrial) :=
        measure_mono covered
    _ ≤ q16SemanticOneForestRawError :=
      exact_restored_clean_trial_union_probability_le_one_forest_of_semantic
        hiddenLaw transitionRoom programmedCover frontierExact semantic
          reference traceExists foldExposureCap finalExposureCap

end

#print axioms
  exact_restored_operational_canonical_root_k13_query_probability_le

end AspisK1.V7Tag73ExactRestoredOperationalK13QueryProbability
