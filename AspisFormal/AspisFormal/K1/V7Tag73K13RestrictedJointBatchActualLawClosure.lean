import AspisFormal.K1.V7Tag73CausalGammaPrefixCoordinates
import AspisFormal.K1.V7Tag73ExactConcreteK13K14Events
import AspisFormal.K1.V7Tag73K13IdealErrorLedger
import AspisFormal.K1.V7Tag73K15FixedActualLawAdapters

/-!
# Compiler-clean actual-law closure for the Tag-73 joint query batch

The query-batch challenge hides a nonzero polynomial of degree at most sixteen.
This module keeps the source-facing obligation deterministic: exact pre-answer
coordinates, the three values which define that polynomial, and inclusion of
the compiler-clean collision event in its root set. The finite-field
probability bound is then derived internally rather than accepted as a release
premise.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73K13RestrictedJointBatchActualLawClosure

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73JointQueryBatchSoundness
open AspisK1.V7Tag73K13IdealErrorLedger
open AspisK1.V7Tag73K15FixedActualLawAdapters
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatProbability
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact
open AspisV6QueryBatchSoundness

noncomputable section

/-- Exact pre-query-batch source data on one compiler-clean slice. The
coordinate equivalence is explicit: constructing it from the literal
query-batch scheduler is a source-alignment obligation, not a hidden
probability hypothesis. -/
structure ExactTag73RestrictedK13JointBatchSource
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (k13Source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder)
    (clean : Set (ExactCompilerSample HiddenTape parameters)) where
  coordinates : HiddenTape →
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactCompilerGammaPrefixResidual parameters × TotalGammaDuplexTape
  preQueryDiscrepancy : HiddenTape →
    ExactCompilerGammaPrefixResidual parameters →
      VariableGammaCompleteSkeleton → QM31Exact
  expected : HiddenTape → ExactCompilerGammaPrefixResidual parameters →
    VariableGammaCompleteSkeleton → QueryVector QM31Exact
  authenticated : HiddenTape → ExactCompilerGammaPrefixResidual parameters →
    VariableGammaCompleteSkeleton → QueryVector QM31Exact
  different : ∀ hidden residual skeleton,
    expected hidden residual skeleton ≠ authenticated hidden residual skeleton
  covered : ∀ hidden,
    jointEventSlice
        (clean ∩ exactTag73K13JointQueryBatchCollisionEvent transitionFuel
          configuration projection fixedInstance decoder k13Source) hidden ⊆
      (coordinates hidden) ⁻¹'
        dependentSuccessfulSubtypeEvent GammaPrefixSucceeds (fun residual ↦
          successfulGammaPrefixSkeletonDependentEvent (fun skeleton ↦
            jointQueryBatchNonzeroCollisionSet
              (preQueryDiscrepancy hidden residual skeleton)
              (expected hidden residual skeleton)
              (authenticated hidden residual skeleton)))

/-- Exact compiler-law joint-query-batch bound on the clean slice. -/
theorem exact_tag73_restricted_k13_joint_batch_probability_le
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
    (k13Source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder)
    (clean : Set (ExactCompilerSample HiddenTape parameters))
    (source : ExactTag73RestrictedK13JointBatchSource transitionFuel
      configuration projection fixedInstance decoder k13Source clean) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ exactTag73K13JointQueryBatchCollisionEvent transitionFuel
          configuration projection fixedInstance decoder k13Source) ≤
      exactJointQueryBatchIdealRawError := by
  change
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ exactTag73K13JointQueryBatchCollisionEvent transitionFuel
          configuration projection fixedInstance decoder k13Source) ≤
      (16 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal)
  apply exact_compiler_joint_law_dependent_variable_prefix_event_probability_le
    hiddenLaw parameters source.coordinates
    (fun hidden residual skeleton ↦
      jointQueryBatchNonzeroCollisionSet
        (source.preQueryDiscrepancy hidden residual skeleton)
        (source.expected hidden residual skeleton)
        (source.authenticated hidden residual skeleton)) 16
  · intro hidden residual skeleton
    exact jointQueryBatch_nonzero_collision_card_le_sixteen_of_vectors_ne
      (source.preQueryDiscrepancy hidden residual skeleton)
      (source.expected hidden residual skeleton)
      (source.authenticated hidden residual skeleton)
      (source.different hidden residual skeleton)
  · exact source.covered

#print axioms ExactTag73RestrictedK13JointBatchSource
#print axioms exact_tag73_restricted_k13_joint_batch_probability_le

end
end AspisK1.V7Tag73K13RestrictedJointBatchActualLawClosure
