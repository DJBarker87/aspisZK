import AspisFormal.K1.V7Tag73ExactConcreteK13K14Events
import AspisFormal.K1.V7Tag73K13IdealErrorLedger
import AspisFormal.K1.V7Tag73K15FixedActualLawAdapters
import AspisFormal.K1.V7Tag73QueryBatchPrefixCausalController
import AspisFormal.K1.V7Tag73RelationTailSourceComposition

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
open AspisK1.V7Tag73QueryBatchPrefixCausalController
open AspisK1.V7Tag73RelationTailSourceComposition
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatProbability
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact
open AspisV6QueryBatchSoundness

noncomputable section

/-- The degree-sixteen collision target is relevant only when the two query
vectors differ. Off that event the guarded target is empty, which makes the
source record total without asserting an impossible global inequality. -/
noncomputable def guardedJointQueryBatchTarget
    (preQueryDiscrepancy : QM31Exact)
    (expected authenticated : QueryVector QM31Exact) : Finset QM31Exact :=
  if expected ≠ authenticated then
    jointQueryBatchNonzeroCollisionSet preQueryDiscrepancy expected
      authenticated
  else ∅

/-- Exactly the algebraic data fixed before the query-batch challenge is
exposed.  The sampled `rho` is deliberately absent. -/
structure JointQueryBatchPreChallengeView where
  preQueryDiscrepancy : QM31Exact
  expected : QueryVector QM31Exact
  authenticated : QueryVector QM31Exact

noncomputable def JointQueryBatchPreChallengeView.target
    (view : JointQueryBatchPreChallengeView) : Finset QM31Exact :=
  guardedJointQueryBatchTarget view.preQueryDiscrepancy view.expected
    view.authenticated

theorem guardedJointQueryBatchTarget_card_le_sixteen
    (preQueryDiscrepancy : QM31Exact)
    (expected authenticated : QueryVector QM31Exact) :
    (guardedJointQueryBatchTarget preQueryDiscrepancy expected authenticated).card
        ≤ 16 := by
  classical
  by_cases different : expected ≠ authenticated
  · simpa [guardedJointQueryBatchTarget, different] using
      jointQueryBatch_nonzero_collision_card_le_sixteen_of_vectors_ne
        preQueryDiscrepancy expected authenticated different
  · simp [guardedJointQueryBatchTarget, different]

theorem JointQueryBatchPreChallengeView.target_card_le_sixteen
    (view : JointQueryBatchPreChallengeView) : view.target.card ≤ 16 :=
  guardedJointQueryBatchTarget_card_le_sixteen view.preQueryDiscrepancy
    view.expected view.authenticated

/-- Exact pre-query-batch source data on one compiler-clean slice. Coordinates
are fixed by the literal pre-answer query-batch scheduler controller; this
record supplies only the remaining deterministic algebraic data and event
inclusion. -/
structure ExactTag73RestrictedK13JointBatchSource
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (relationSource : ExactTag73RelationSourceEnvironment transitionFuel
      configuration projection fixedInstance decoder)
    (clean : Set (ExactCompilerSample HiddenTape parameters)) where
  view : HiddenTape →
    ExactCompilerGammaPrefixResidual parameters →
      VariableGammaCompleteSkeleton → JointQueryBatchPreChallengeView
  covered : ∀ hidden,
    jointEventSlice
        (clean ∩ exactTag73K13JointQueryBatchCollisionEvent transitionFuel
          configuration projection fixedInstance decoder
            (relationSource.toK13SourceObligations transitionFuel configuration
              projection fixedInstance decoder)) hidden ⊆
      (exactCompilerQueryBatchPrefixCoordinates parameters transitionFuel
          (exactPlainRomCursor configuration hidden).erase) ⁻¹'
        dependentSuccessfulSubtypeEvent GammaPrefixSucceeds (fun residual ↦
          successfulGammaPrefixSkeletonDependentEvent (fun skeleton ↦
            (view hidden residual skeleton).target))

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
    (relationSource : ExactTag73RelationSourceEnvironment transitionFuel
      configuration projection fixedInstance decoder)
    (clean : Set (ExactCompilerSample HiddenTape parameters))
    (source : ExactTag73RestrictedK13JointBatchSource transitionFuel
      configuration projection fixedInstance decoder relationSource clean) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ exactTag73K13JointQueryBatchCollisionEvent transitionFuel
          configuration projection fixedInstance decoder
            (relationSource.toK13SourceObligations transitionFuel configuration
              projection fixedInstance decoder)) ≤
      exactJointQueryBatchIdealRawError := by
  change
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ exactTag73K13JointQueryBatchCollisionEvent transitionFuel
          configuration projection fixedInstance decoder
            (relationSource.toK13SourceObligations transitionFuel configuration
              projection fixedInstance decoder)) ≤
      (16 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal)
  apply exact_compiler_joint_law_dependent_variable_prefix_event_probability_le
    hiddenLaw parameters
    (fun hidden ↦ exactCompilerQueryBatchPrefixCoordinates parameters
      transitionFuel (exactPlainRomCursor configuration hidden).erase)
    (fun hidden residual skeleton ↦
      (source.view hidden residual skeleton).target) 16
  · intro hidden residual skeleton
    exact (source.view hidden residual skeleton).target_card_le_sixteen
  · exact source.covered

#print axioms ExactTag73RestrictedK13JointBatchSource
#print axioms guardedJointQueryBatchTarget_card_le_sixteen
#print axioms JointQueryBatchPreChallengeView.target_card_le_sixteen
#print axioms exact_tag73_restricted_k13_joint_batch_probability_le

end
end AspisK1.V7Tag73K13RestrictedJointBatchActualLawClosure
