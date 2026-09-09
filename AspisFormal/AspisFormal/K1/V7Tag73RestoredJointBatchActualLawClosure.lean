import AspisFormal.K1.V7Tag73K13RestrictedJointBatchActualLawClosure
import AspisFormal.K1.V7Tag73RestoredQueryBatchCausalMarker

/-!
# Restoration-native actual-law closure for the Tag-73 joint query batch

The earlier joint-batch law factors the root execution at a query-batch
coordinate.  That factorization is insufficient when an adversary queried the
same SHA coordinate first.  The restoration sweep supplies a stronger causal
boundary: the verifier transition and its logical owner are selected before
either programmed fork answer is read.

This module installs the resulting waiting-controller equivalence directly in
the finite-field probability theorem.  Its source record has no probability
field; it must identify the literal restored execution with one active
pre-challenge view.  Thus the only remaining work after this leaf is the
deterministic scheduler/source alignment, not another random-oracle estimate.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73RestoredJointBatchActualLawClosure

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73JointQueryBatchSoundness
open AspisK1.V7Tag73K13IdealErrorLedger
open AspisK1.V7Tag73K13RestrictedJointBatchActualLawClosure
open AspisK1.V7Tag73K15FixedActualLawAdapters
open AspisK1.V7Tag73RestoredQueryBatchCausalMarker
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatProbability
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-! ## Exact restoration-native coordinates -/

/-- The complete compiler tape factored at the first typed block-zero
query-batch fork in the literal restoration sweep.  The marker inspects the
ready verifier transition, never a retrospective SHA-input role. -/
def exactCompilerRestoredQueryBatchCoordinates
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (hidden : HiddenTape) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactCompilerGammaPrefixResidual parameters × TotalGammaDuplexTape :=
  exactCompilerTypedRestoredQueryBatchCoordinates
    (Result := ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
      Payload Witness)
    parameters transitionFuel
    (configuration.machine.blackBox.start hidden
      configuration.machine.observation)
    configuration.machine.environment
    configuration.restorationConfiguration
    (exactPlainRomCursor configuration hidden).erase

/-! ## Source-shaped deterministic alignment -/

/-- Source data for one restoration-native joint-batch probability fibre.
`exactAt` exposes the literal sampled challenge and the complete algebraic
view; it does not assume an event inclusion or a measure inequality. -/
structure ExactTag73RestoredJointBatchCausalSource
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (clean : Set (ExactCompilerSample HiddenTape parameters)) where
  view : HiddenTape →
    ExactCompilerGammaPrefixResidual parameters →
      VariableGammaCompleteSkeleton → JointQueryBatchPreChallengeView
  exactAt : ∀ (hidden : HiddenTape)
      (answers : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length)
      (_cleanMember : (hidden, answers) ∈ clean)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance (hidden, answers))
      (k12 : ExactPrefixK12Certificate input)
      (preQueryDiscrepancy : QM31Exact)
      (_collisionFacts :
        exactTag73K13ExpectedQueryVector decoder input k12 ≠
            exactTag73K13AuthenticatedQueryVector decoder input k12 ∧
          exactOperationalChallenge input .queryBatch ∈
            jointQueryBatchNonzeroCollisionSet preQueryDiscrepancy
              (exactTag73K13ExpectedQueryVector decoder input k12)
              (exactTag73K13AuthenticatedQueryVector decoder input k12)),
    let coordinates := exactCompilerRestoredQueryBatchCoordinates
      transitionFuel configuration hidden answers
    ∃ success : GammaPrefixSucceeds coordinates.2,
      let factored := successfulGammaPrefixFactorization
        (⟨coordinates.2, success⟩ : SuccessfulGammaPrefixTape)
      exactOperationalChallenge input .queryBatch = factored.2.1 ∧
      (view hidden coordinates.1 factored.1).active = true ∧
      (view hidden coordinates.1 factored.1).preQueryDiscrepancy =
        preQueryDiscrepancy ∧
      (view hidden coordinates.1 factored.1).expected =
        exactTag73K13ExpectedQueryVector decoder input k12 ∧
      (view hidden coordinates.1 factored.1).authenticated =
        exactTag73K13AuthenticatedQueryVector decoder input k12 ∧
      exactOperationalChallenge input .queryBatch ∈
        (view hidden coordinates.1 factored.1).collisionTarget

/-! ## Deterministic cover and finite-field law -/

/-- Literal source alignment implies membership in the successful-prefix
finite bad event used by the generic conditional probability theorem. -/
theorem restored_joint_batch_event_slice_covered
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {clean : Set (ExactCompilerSample HiddenTape parameters)}
    (source : ExactTag73RestoredJointBatchCausalSource transitionFuel
      configuration projection fixedInstance decoder clean)
    (preQueryDiscrepancy : ∀ sample : ExactCompilerSample HiddenTape parameters,
      ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample → QM31Exact)
    (event : Set (ExactCompilerSample HiddenTape parameters))
    (eventExact : ∀ hidden answers,
      (hidden, answers) ∈ clean ∩ event →
      ∃ (input : ExactK12OperationalInput transitionFuel configuration
            projection fixedInstance (hidden, answers))
          (k12 : ExactPrefixK12Certificate input),
        exactTag73K13ExpectedQueryVector decoder input k12 ≠
            exactTag73K13AuthenticatedQueryVector decoder input k12 ∧
          exactOperationalChallenge input .queryBatch ∈
            jointQueryBatchNonzeroCollisionSet
              (preQueryDiscrepancy (hidden, answers) input)
              (exactTag73K13ExpectedQueryVector decoder input k12)
              (exactTag73K13AuthenticatedQueryVector decoder input k12)) :
    ∀ hidden,
      jointEventSlice (clean ∩ event) hidden ⊆
        (exactCompilerRestoredQueryBatchCoordinates transitionFuel
          configuration hidden) ⁻¹'
          dependentSuccessfulSubtypeEvent GammaPrefixSucceeds (fun residual ↦
            successfulGammaPrefixSkeletonDependentEvent (fun skeleton ↦
              (source.view hidden residual skeleton).target)) := by
  intro hidden answers member
  obtain ⟨input, k12, collisionFacts⟩ := eventExact hidden answers member
  obtain ⟨success, challengeExact, activeExact, _preExact, _expectedExact,
      _authenticatedExact, actualMember⟩ :=
    source.exactAt hidden answers member.1 input k12
      (preQueryDiscrepancy (hidden, answers) input) collisionFacts
  let coordinates := exactCompilerRestoredQueryBatchCoordinates transitionFuel
    configuration hidden answers
  change ∃ h : GammaPrefixSucceeds coordinates.2,
    (⟨coordinates.2, h⟩ : SuccessfulGammaPrefixTape) ∈
      successfulGammaPrefixSkeletonDependentEvent (fun skeleton ↦
        (source.view hidden coordinates.1 skeleton).target)
  refine ⟨success, ?_⟩
  let factored := successfulGammaPrefixFactorization
    (⟨coordinates.2, success⟩ : SuccessfulGammaPrefixTape)
  let currentView := source.view hidden coordinates.1 factored.1
  change factored.2.1 ∈ currentView.target
  have factoredMember : factored.2.1 ∈ currentView.collisionTarget := by
    rw [← challengeExact]
    exact actualMember
  exact currentView.mem_target_of_active activeExact factoredMember

/-- Exact compiler-law joint-batch bound using the typed restoration fork.
The denominator and degree-sixteen numerator are proved by the existing
successful-sampler theorem; no independence assumption is introduced. -/
theorem exact_tag73_restored_joint_batch_probability_le
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
    (clean event : Set (ExactCompilerSample HiddenTape parameters))
    (source : ExactTag73RestoredJointBatchCausalSource transitionFuel
      configuration projection fixedInstance decoder clean)
    (preQueryDiscrepancy : ∀ sample : ExactCompilerSample HiddenTape parameters,
      ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample → QM31Exact)
    (eventExact : ∀ hidden answers,
      (hidden, answers) ∈ clean ∩ event →
      ∃ (input : ExactK12OperationalInput transitionFuel configuration
            projection fixedInstance (hidden, answers))
          (k12 : ExactPrefixK12Certificate input),
        exactTag73K13ExpectedQueryVector decoder input k12 ≠
            exactTag73K13AuthenticatedQueryVector decoder input k12 ∧
          exactOperationalChallenge input .queryBatch ∈
            jointQueryBatchNonzeroCollisionSet
              (preQueryDiscrepancy (hidden, answers) input)
              (exactTag73K13ExpectedQueryVector decoder input k12)
              (exactTag73K13AuthenticatedQueryVector decoder input k12)) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ event) ≤ exactJointQueryBatchIdealRawError := by
  change
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ event) ≤
      (16 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal)
  apply exact_compiler_joint_law_dependent_variable_prefix_event_probability_le
    hiddenLaw parameters
    (fun hidden ↦ exactCompilerRestoredQueryBatchCoordinates transitionFuel
      configuration hidden)
    (fun hidden residual skeleton ↦
      (source.view hidden residual skeleton).target) 16
  · intro hidden residual skeleton
    exact (source.view hidden residual skeleton).target_card_le_sixteen
  · exact restored_joint_batch_event_slice_covered source
      preQueryDiscrepancy event eventExact

#print axioms exactCompilerRestoredQueryBatchCoordinates
#print axioms ExactTag73RestoredJointBatchCausalSource
#print axioms restored_joint_batch_event_slice_covered
#print axioms exact_tag73_restored_joint_batch_probability_le

end
end AspisK1.V7Tag73RestoredJointBatchActualLawClosure
