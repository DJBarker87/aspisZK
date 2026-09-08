import AspisFormal.K1.V7Tag73AdaptiveBidirectionalFoldOneFoldTrialAccounting
import AspisFormal.K1.V7Tag73CanonicalOneFoldSchedule
import AspisFormal.K1.V7Tag73ExactCleanBidirectionalFoldOneFoldFibreInvariant
import AspisFormal.K1.V7Tag73ExactCleanBidirectionalFoldOneFoldInvariantTarget
import AspisFormal.K1.V7Tag73FoldOneFoldComponentCoverage

/-!
# Corrected clean bidirectional one-fold probability closure

For each exposure-indexed fold trial, this module chooses one accepted
representative on every residual/fold fibre.  The chronological word/gamma
invariant makes that representative's exact degree-three target valid for all
other accepted tapes in the fibre.  The generic five-coordinate theorem then
pays the literal 31-bit work factor, and the exposure union cancels it.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldProbability

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveBidirectionalFoldOneFoldTrialAccounting
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73BidirectionalFoldOneFoldCoordinates
open AspisK1.V7Tag73CanonicalOneFoldSchedule
open AspisK1.V7Tag73CausalFoldOneFoldTapeBridge
open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldBadTarget
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldProjection
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldReplay
open AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldComponents
open AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldFibreInvariant
open AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldFibreTarget
open AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldInvariantTarget
open AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldTrialEvent
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactAdversaryAnchorFinalProfile
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactInternalCurveProbability
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldOneFoldComponentCoverage
open AspisK1.V7Tag73FoldOneFoldComponentMembership
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73K13IdealErrorLedger
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
open AspisK1.V7Tag73K13PreQ16TargetProbability
open AspisK1.V7Tag73PreQ16OperationalStageEvents
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Irrelevant total value for an uninhabited residual/fold fibre.  No event
member can reach this branch. -/
noncomputable def emptyFibreOneFoldContext
    (decoder : ExactDecoderInstantiation QM31Exact)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (finalEncoderExact : decoder.finalEncoder = exactFinalEncoder) :
    ExactCausalOneFoldSamplerContext where
  schedule := canonicalOneFoldSchedule 0
  encoders := exactK13Encoders decoder
  initialEncoderExact := by
    simpa [exactK13Encoders, decoderCodeEncoders] using initialEncoderExact
  finalEncoderExact := by
    simpa [exactK13Encoders, decoderCodeEncoders] using finalEncoderExact
  inverseTablesExact := canonical_one_fold_schedule_exact 0
  base :=
    { initial := fun _ => 0
      disclosedFinal := fun _ => 0 }
  strategy :=
    { candidate := fun _ _ => 0
      support := fun _ => ∅ }

def exactCleanOneFoldFibreNonempty
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (trial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (residual : ExactCompilerBidirectionalFoldOneFoldResidual parameters)
    (fold : Digest256) : Prop :=
  let router := exactCompilerBidirectionalFoldOneFoldRouter parameters
    transitionFuel trial.val (exactPlainRomCursor configuration hidden).erase
  ∃ tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length,
    (hidden, tape) ∈ exactCleanBidirectionalK13OneFoldTrialEvent transitionFuel
      configuration projection fixedInstance decoder trial ∧
    (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
      tape).1 = residual ∧
    (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
      tape).2.1 = fold

noncomputable def exactCleanOneFoldFibreContext
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (source : ExactFixedK13DecodedParsedSourceProvider transitionFuel
      configuration projection fixedInstance)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (finalEncoderExact : decoder.finalEncoder = exactFinalEncoder)
    (trial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (residual : ExactCompilerBidirectionalFoldOneFoldResidual parameters)
    (fold : Digest256)
    (skeleton : Tag73OrdinarySamplerSkeleton) :
    ExactCausalOneFoldSamplerContext := by
  classical
  exact if inhabited : exactCleanOneFoldFibreNonempty transitionFuel
      configuration projection fixedInstance decoder trial hidden residual fold
    then
      let tape := Classical.choose inhabited
      let member := (Classical.choose_spec inhabited).1
      let witness := Classical.choice member
      exactCleanBidirectionalOneFoldContextOfSource source initialEncoderExact
        finalEncoderExact (hidden, tape) witness.input witness.fold
          witness.failure.words skeleton
    else emptyFibreOneFoldContext decoder initialEncoderExact finalEncoderExact

/-- The exact clean trial family over the five deployed fold/alpha
coordinates.  Each fibre target is selected from an actual accepting member
when one exists. -/
noncomputable def exactCleanBidirectionalOneFoldExposureTrials
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (finalEncoderExact : decoder.finalEncoder = exactFinalEncoder)
    (source : ExactFixedK13DecodedParsedSourceProvider transitionFuel
      configuration projection fixedInstance) :
    ExactCompilerExposureIndexedBidirectionalFoldOneFoldTrials
      (HiddenTape := HiddenTape) parameters where
  event := exactCleanBidirectionalK13OneFoldTrialEvent transitionFuel
    configuration projection fixedInstance decoder
  router := fun trial hidden =>
    exactCompilerBidirectionalFoldOneFoldRouter parameters transitionFuel
      trial.val (exactPlainRomCursor configuration hidden).erase
  context := fun trial hidden residual fold =>
    exactCleanOneFoldFibreContext source initialEncoderExact finalEncoderExact
      trial hidden residual fold
  covered := by
    intro trial hidden
    let router := exactCompilerBidirectionalFoldOneFoldRouter parameters
      transitionFuel trial.val
      (exactPlainRomCursor configuration hidden).erase
    let coordinates :=
      exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
    let context := fun residual fold =>
      exactCleanOneFoldFibreContext source initialEncoderExact finalEncoderExact
        trial hidden residual fold
    apply foldOneFoldComponentFacts_cover_public_event coordinates context
      (jointEventSlice
        (exactCleanBidirectionalK13OneFoldTrialEvent transitionFuel
          configuration projection fixedInstance decoder trial) hidden)
    intro tape member
    change (hidden, tape) ∈
      exactCleanBidirectionalK13OneFoldTrialEvent transitionFuel configuration
        projection fixedInstance decoder trial at member
    let rightWitness := Classical.choice member
    have inhabited : exactCleanOneFoldFibreNonempty transitionFuel configuration
        projection fixedInstance decoder trial hidden (coordinates tape).1
          (coordinates tape).2.1 :=
      ⟨tape, member, rfl, rfl⟩
    let leftTape := Classical.choose inhabited
    have leftFacts := Classical.choose_spec inhabited
    let leftWitness := Classical.choice leftFacts.1
    have residualExact : (coordinates leftTape).1 = (coordinates tape).1 :=
      leftFacts.2.1
    have foldExact : (coordinates leftTape).2.1 =
        (coordinates tape).2.1 := leftFacts.2.2
    have pairFacts :=
      exact_clean_onefold_component_facts_of_pair
        (configuration := configuration) (projection := projection)
        (fixedInstance := fixedInstance) (decoder := decoder)
        transitionRoom programmedCover initialEncoderExact finalEncoderExact source
        trial hidden leftTape tape leftWitness rightWitness
        (by simpa [coordinates, router] using residualExact)
        (by simpa [coordinates, router] using foldExact)
    have contextExact :
        (fun skeleton => exactCleanOneFoldFibreContext source
          initialEncoderExact finalEncoderExact trial hidden
          (coordinates tape).1 (coordinates tape).2.1 skeleton) =
        exactCleanBidirectionalOneFoldContextOfSource source
          initialEncoderExact finalEncoderExact (hidden, leftTape)
          leftWitness.input leftWitness.fold leftWitness.failure.words := by
      funext skeleton
      simp only [exactCleanOneFoldFibreContext, dif_pos inhabited]
      rfl
    change FoldOneFoldComponentFacts (coordinates tape)
      (fun skeleton => exactCleanOneFoldFibreContext source
        initialEncoderExact finalEncoderExact trial hidden
        (coordinates tape).1 (coordinates tape).2.1 skeleton)
    rw [contextExact]
    simpa only [coordinates, router] using pairFacts

/-- The corrected chronological one-fold event outside the already-budgeted
Merkle causal target has the unchanged degree-three raw error. -/
theorem exact_clean_bidirectional_preQ16_onefold_probability_le
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
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (finalEncoderExact : decoder.finalEncoder = exactFinalEncoder)
    (source : ExactFixedK13DecodedParsedSourceProvider transitionFuel
      configuration projection fixedInstance)
    (foldExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 31) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        ((exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance \
            exactK13PreQ16MerkleTargetHitEvent configuration transitionFuel) ∩
          exactPreQ16K13OneFoldEvent transitionFuel configuration projection
            fixedInstance decoder) ≤ exactOneFoldIdealRawError := by
  let trials := exactCleanBidirectionalOneFoldExposureTrials transitionFuel
    configuration projection fixedInstance decoder transitionRoom
      programmedCover initialEncoderExact finalEncoderExact source
  have bound := trials.failure_union_probability_le
    (hiddenLaw := hiddenLaw) foldExposureCap
  change (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
      (⋃ trial, exactCleanBidirectionalK13OneFoldTrialEvent transitionFuel
        configuration projection fixedInstance decoder trial) ≤
        exactOneFoldIdealRawError at bound
  rw [← exactCleanBidirectionalK13OneFoldTrialEvent_iUnion transitionFuel
    configuration projection fixedInstance decoder] at bound
  exact bound

#print axioms emptyFibreOneFoldContext
#print axioms exactCleanOneFoldFibreContext
#print axioms exactCleanBidirectionalOneFoldExposureTrials
#print axioms exact_clean_bidirectional_preQ16_onefold_probability_le

end


end AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldProbability
