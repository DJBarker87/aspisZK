import AspisFormal.K1.V7Tag73K13RestrictedJointBatchActualLawClosure

/-!
# Causal source certificate for the Tag-73 joint query batch

This file replaces a conclusion-shaped collision-event inclusion by literal
pre-answer source facts.  On every clean accepted execution it exposes the
successful query-batch sampler coordinate, the returned challenge, and each
component of the degree-sixteen target view.  The existing actual-law source
record is then derived internally.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73K13JointBatchCausalSource

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
open AspisK1.V7Tag73K13RestrictedJointBatchActualLawClosure
open AspisK1.V7Tag73JointQueryBatchSoundness
open AspisK1.V7Tag73QueryBatchPrefixCausalController
open AspisK1.V7Tag73RelationTailSourceComposition
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatProbability
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Source-shaped data sufficient to derive the exact compiler collision
coverage.  No probability inequality or event inclusion is a field. -/
structure ExactTag73K13JointBatchCausalSource
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
  exactAt : ∀ (hidden : HiddenTape)
      (answers : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length)
      (_cleanMember : (hidden, answers) ∈ clean)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance (hidden, answers))
      (k12 : ExactPrefixK12Certificate input)
      (_collisionFacts :
        exactTag73K13ExpectedQueryVector decoder input k12 ≠
            exactTag73K13AuthenticatedQueryVector decoder input k12 ∧
          exactOperationalChallenge input .queryBatch ∈
            exactTag73JointQueryBatchNonzeroCollisionSet
              ((relationSource.toK13SourceObligations transitionFuel
                configuration projection fixedInstance decoder).preQueryDiscrepancy
                  (hidden, answers) input)
              (exactTag73K13ExpectedQueryVector decoder input k12)
              (exactTag73K13AuthenticatedQueryVector decoder input k12)),
    let coordinates := exactCompilerQueryBatchPrefixCoordinates parameters
      transitionFuel (exactPlainRomCursor configuration hidden).erase answers
    ∃ success : GammaPrefixSucceeds coordinates.2,
      let factored := successfulGammaPrefixFactorization
        (⟨coordinates.2, success⟩ : SuccessfulGammaPrefixTape)
      exactOperationalChallenge input .queryBatch = factored.2.1 ∧
      (view hidden coordinates.1 factored.1).active = true ∧
      (view hidden coordinates.1 factored.1).preQueryDiscrepancy =
        (relationSource.toK13SourceObligations transitionFuel configuration
          projection fixedInstance decoder).preQueryDiscrepancy
            (hidden, answers) input ∧
      (view hidden coordinates.1 factored.1).expected =
        exactTag73K13ExpectedQueryVector decoder input k12 ∧
      (view hidden coordinates.1 factored.1).authenticated =
        exactTag73K13AuthenticatedQueryVector decoder input k12 ∧
      exactOperationalChallenge input .queryBatch ∈
        (view hidden coordinates.1 factored.1).collisionTarget ∧
      (view hidden coordinates.1 factored.1).collisionTarget =
        exactTag73JointQueryBatchNonzeroCollisionSet
          ((relationSource.toK13SourceObligations transitionFuel configuration
            projection fixedInstance decoder).preQueryDiscrepancy
              (hidden, answers) input)
          (exactTag73K13ExpectedQueryVector decoder input k12)
          (exactTag73K13AuthenticatedQueryVector decoder input k12)

/-- The literal causal source equalities derive the older event-inclusion
record.  This is the only place where the exact collision event is unpacked;
the probability theorem therefore consumes source facts rather than trusting
an inclusion supplied by a caller. -/
noncomputable def ExactTag73K13JointBatchCausalSource.toRestrictedSource
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {relationSource : ExactTag73RelationSourceEnvironment transitionFuel
      configuration projection fixedInstance decoder}
    {clean : Set (ExactCompilerSample HiddenTape parameters)}
    (causal : ExactTag73K13JointBatchCausalSource transitionFuel configuration
      projection fixedInstance decoder relationSource clean) :
    ExactTag73RestrictedK13JointBatchSource transitionFuel configuration
      projection fixedInstance decoder relationSource clean where
  view := causal.view
  covered := by
    intro hidden answers member
    rcases member with ⟨cleanMember, input, k12, collisionFacts⟩
    obtain ⟨success, challengeExact, activeExact, _preExact, _expectedExact,
        _authenticatedExact, actualMember, _targetExact⟩ :=
      causal.exactAt hidden answers cleanMember input k12 collisionFacts
    let coordinates := exactCompilerQueryBatchPrefixCoordinates parameters
      transitionFuel (exactPlainRomCursor configuration hidden).erase answers
    change ∃ h : GammaPrefixSucceeds coordinates.2,
      (⟨coordinates.2, h⟩ : SuccessfulGammaPrefixTape) ∈
        successfulGammaPrefixSkeletonDependentEvent (fun skeleton ↦
          (causal.view hidden coordinates.1 skeleton).target)
    refine ⟨success, ?_⟩
    let factored := successfulGammaPrefixFactorization
      (⟨coordinates.2, success⟩ : SuccessfulGammaPrefixTape)
    let currentView := causal.view hidden coordinates.1 factored.1
    change factored.2.1 ∈ currentView.target
    have challengeMembershipEq := congrArg
      (fun value : QM31Exact ↦ value ∈ currentView.collisionTarget)
        challengeExact
    have factoredMember : factored.2.1 ∈ currentView.collisionTarget :=
      challengeMembershipEq.mp actualMember
    exact currentView.mem_target_of_active activeExact factoredMember

#print axioms ExactTag73K13JointBatchCausalSource.toRestrictedSource

end
end AspisK1.V7Tag73K13JointBatchCausalSource
