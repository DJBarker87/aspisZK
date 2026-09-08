import AspisFormal.K1.V7Tag73ExactBidirectionalFoldOneFoldTrialEvent
import AspisFormal.K1.V7Tag73ExactFixedInstanceEvent
import AspisFormal.K1.V7Tag73PreQ16OperationalStageEvents

/-!
# Clean exposure-indexed Tag-73 one-fold event

The bidirectional fold/alpha trial partition is useful only on the exact
fixed-instance legal same-tape domain consumed by K1.6.  This leaf records
that restriction in the witness type itself.  In particular, later fibre
arguments may use the literal complement of `exactPlainRomTargetEvent`
without asserting an unconditional source-order invariant in the presence
of adversary-first forward queries.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldTrialEvent

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactBidirectionalFoldAnchor
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldTrialEvent
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
open AspisK1.V7Tag73K13PreQ16TargetProbability
open AspisK1.V7Tag73PreQ16OperationalStageEvents
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- One exact bidirectional one-fold witness together with membership in the
fixed-instance legal same-tape event.  The latter is the source event minus
the already bounded causal target event; it is not a new assumption or error
term. -/
structure ExactCleanBidirectionalK13OneFoldTrialWitness
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
  failure : ExactPreQ16K13StageOneFoldFailure decoder input
  fold : ExactAcceptedFoldTrial input
  trialExact : exactAcceptedFoldPairTrial input fold = trial
  legal : sample ∈ exactFixedPlainRomLegalSameTapeEvent transitionFuel
    configuration projection fixedInstance
  noMerkleTarget : sample ∉ exactK13PreQ16MerkleTargetHitEvent configuration
    transitionFuel

def exactCleanBidirectionalK13OneFoldTrialEvent
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
    (ExactCleanBidirectionalK13OneFoldTrialWitness transitionFuel configuration
      projection fixedInstance decoder sample trial)}

/-- The clean one-fold event is exactly partitioned by the same first
fold-work/boundary exposure trial as the unrestricted event. -/
theorem exactCleanBidirectionalK13OneFoldTrialEvent_iUnion
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration projection
          fixedInstance \
        exactK13PreQ16MerkleTargetHitEvent configuration transitionFuel) ∩
        exactPreQ16K13OneFoldEvent transitionFuel configuration projection
          fixedInstance decoder =
      ⋃ trial : ExactCompilerExposureTrial parameters,
        exactCleanBidirectionalK13OneFoldTrialEvent transitionFuel configuration
          projection fixedInstance decoder trial := by
  ext sample
  constructor
  · rintro ⟨⟨legal, noMerkleTarget⟩, event⟩
    obtain ⟨input, k12, failure⟩ := event
    let fold := exactAcceptedFoldTrial input
    let trial := exactAcceptedFoldPairTrial input fold
    apply Set.mem_iUnion.2
    exact ⟨trial, ⟨⟨input, k12, Classical.choice failure, fold, rfl,
      legal, noMerkleTarget⟩⟩⟩
  · intro member
    obtain ⟨trial, trialMember⟩ := Set.mem_iUnion.1 member
    let witness := Classical.choice trialMember
    refine ⟨⟨witness.legal, witness.noMerkleTarget⟩, ?_⟩
    exact ⟨witness.input, witness.k12, ⟨witness.failure⟩⟩

end


#print axioms ExactCleanBidirectionalK13OneFoldTrialWitness
#print axioms exactCleanBidirectionalK13OneFoldTrialEvent_iUnion

end AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldTrialEvent
