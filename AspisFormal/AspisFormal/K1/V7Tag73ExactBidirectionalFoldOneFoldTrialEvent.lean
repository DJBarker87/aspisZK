import AspisFormal.K1.V7Tag73ExactBidirectionalFoldOneFoldBadTarget
import AspisFormal.K1.V7Tag73ExactConcreteK13K14Events

/-!
# Exact exposure-indexed Tag-73 one-fold event

The deployed one-fold failure event is partitioned by the first creation of
the selected fold-work/boundary pair.  The witness retains the same accepted
input, K1.2 certificate and failure used by the operational classifier; no
probability conclusion is stored in the event.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactBidirectionalFoldOneFoldTrialEvent

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73BidirectionalFoldOneFoldCoordinates
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactBidirectionalFoldAnchor
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldReplay
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact
open AspisV6OneFoldCandidateExtraction

noncomputable section

structure ExactBidirectionalK13OneFoldTrialWitness
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (sample : ExactCompilerSample HiddenTape parameters)
    (trial : ExactCompilerExposureTrial parameters) where
  input : ExactK12OperationalInput transitionFuel configuration projection
    fixedInstance sample
  k12 : ExactPrefixK12Certificate input
  failure : OneFoldReductionFailure (exactK13ParsedProof input).schedule
    (exactK13Encoders decoder) (exactK13Transcript input k12)
  fold : ExactAcceptedFoldTrial input
  trialExact : exactAcceptedFoldPairTrial input fold = trial

def exactBidirectionalK13OneFoldTrialEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (trial : ExactCompilerExposureTrial parameters) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | Nonempty
    (ExactBidirectionalK13OneFoldTrialWitness transitionFuel configuration
      projection fixedInstance decoder sample trial)}

/-- The exposure-indexed events are an exact partition cover of the deployed
one-fold event. -/
theorem exactBidirectionalK13OneFoldTrialEvent_iUnion
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    exactTag73K13OneFoldEvent transitionFuel configuration projection
        fixedInstance decoder =
      ⋃ trial : ExactCompilerExposureTrial parameters,
        exactBidirectionalK13OneFoldTrialEvent transitionFuel configuration
          projection fixedInstance decoder trial := by
  ext sample
  constructor
  · rintro ⟨input, k12, failure⟩
    let fold := exactAcceptedFoldTrial input
    let trial := exactAcceptedFoldPairTrial input fold
    apply Set.mem_iUnion.2
    refine ⟨trial, ?_⟩
    exact ⟨⟨input, k12, failure, fold, rfl⟩⟩
  · intro member
    obtain ⟨trial, member⟩ := Set.mem_iUnion.1 member
    let witness := Classical.choice member
    exact ⟨witness.input, witness.k12, witness.failure⟩

/-- A trial witness uses exactly the fixed-trial router selected by its hidden
tape and trial index. -/
theorem ExactBidirectionalK13OneFoldTrialWitness.routerExact
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {sample : ExactCompilerSample HiddenTape parameters}
    {trial : ExactCompilerExposureTrial parameters}
    (witness : ExactBidirectionalK13OneFoldTrialWitness transitionFuel
      configuration projection fixedInstance decoder sample trial) :
    exactAcceptedFoldBidirectionalRouter witness.input witness.fold =
      exactCompilerBidirectionalFoldOneFoldRouter parameters transitionFuel
        trial.val (exactPlainRomCursor configuration sample.1).erase := by
  unfold exactAcceptedFoldBidirectionalRouter
  rw [witness.trialExact]

end


#print axioms ExactBidirectionalK13OneFoldTrialWitness
#print axioms exactBidirectionalK13OneFoldTrialEvent_iUnion
#print axioms ExactBidirectionalK13OneFoldTrialWitness.routerExact

end AspisK1.V7Tag73ExactBidirectionalFoldOneFoldTrialEvent
