import AspisFormal.K1.V7Tag73K13CandidateDirectedViewFacts
import AspisFormal.K1.V7Tag73K13CandidateDirectedViewMember
import AspisFormal.K1.V7Tag73K13CandidateDirectedViewWitnessAt

/-!
# Pointwise candidate-directed K1.3 view alignment

This module proves only the `alignedAt` field consumed by the final alignment
record.  Separating the dependent function from the record constructor keeps
the elaborated term small without changing the statement.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.constructorNameAsVariable false

namespace AspisK1.V7Tag73K13CandidateDirectedViewAlignedAt

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkDigestProbability
open AspisK1.V7Tag73JointQueryBatchSoundness
open AspisK1.V7Tag73K13CandidateDirectedCoordinateSelected
open AspisK1.V7Tag73K13CandidateDirectedProbabilityClosure
open AspisK1.V7Tag73K13CandidateDirectedSourceBridge
open AspisK1.V7Tag73K13CandidateDirectedViewFunctional
open AspisK1.V7Tag73K13CandidateDirectedViewFacts
open AspisK1.V7Tag73K13CandidateDirectedViewMember
open AspisK1.V7Tag73K13CandidateDirectedViewWitness
open AspisK1.V7Tag73K13CandidateDirectedViewWitnessAt
open AspisK1.V7Tag73K13RestrictedJointBatchActualLawClosure
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The canonical view chosen from a functional 542-coordinate fibre aligns
with every accepted collision execution in that fibre. -/
theorem exactCandidateDirectedFunctionalView_alignedAt
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder}
    (functional : ExactCandidateDirectedK13ViewFunctional transitionFuel
      configuration projection fixedInstance decoder source) :
    ∀ (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (k12 : ExactPrefixK12Certificate input)
      (collisionFacts : ExactTag73K13CollisionCertificate source input k12)
      (candidate : Q16DigestSlot)
      (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
      (selected : ExactTag73CandidateDirectedCoordinateSelected input candidate
        foldTrial finalTrial),
    let coordinates := exactCandidateDirectedRegroupedCoordinates
      transitionFuel configuration candidate foldTrial finalTrial sample.1
        sample.2
    ∀ success : GammaPrefixSucceeds coordinates.2.2.2,
      let factored := successfulGammaPrefixFactorization
        ⟨coordinates.2.2.2, success⟩
      let currentView := exactCandidateDirectedFunctionalView source candidate
        foldTrial finalTrial sample.1 coordinates.1 coordinates.2.1
          coordinates.2.2.1 factored.1
      currentView.active = true ∧
        currentView.preQueryDiscrepancy =
          source.preQueryDiscrepancy sample input ∧
        currentView.expected =
          exactTag73K13ExpectedQueryVector decoder input k12 ∧
        currentView.authenticated =
          exactTag73K13AuthenticatedQueryVector decoder input k12 ∧
        exactOperationalChallenge input .queryBatch ∈
          currentView.collisionTarget := by
  intro sample input k12 collisionFacts candidate foldTrial finalTrial selected
  let different := collisionFacts.different
  dsimp only
  intro success
  let coordinates := exactCandidateDirectedRegroupedCoordinates
    transitionFuel configuration candidate foldTrial finalTrial sample.1
      sample.2
  let factored := successfulGammaPrefixFactorization
    ⟨coordinates.2.2.2, success⟩
  let witness : ExactCandidateDirectedK13ViewWitness source candidate
      foldTrial finalTrial sample.1 coordinates.1 coordinates.2.1
        coordinates.2.2.1 factored.1 :=
    exactCandidateDirectedK13ViewWitnessAt source input k12 different candidate
      foldTrial finalTrial selected success
  have viewExact := exactCandidateDirectedFunctionalView_eq functional witness
  change exactCandidateDirectedFunctionalView source candidate foldTrial
      finalTrial sample.1 coordinates.1 coordinates.2.1 coordinates.2.2.1
        factored.1 = witness.preChallengeView at viewExact
  let currentView := exactCandidateDirectedFunctionalView source candidate
    foldTrial finalTrial sample.1 coordinates.1 coordinates.2.1
      coordinates.2.2.1 factored.1
  have viewExact' : currentView = witness.view := viewExact
  have currentActive : currentView.active = true :=
    (congrArg JointQueryBatchPreChallengeView.active viewExact').trans
      witness.viewActive
  have witnessPre : witness.view.preQueryDiscrepancy =
      source.preQueryDiscrepancy sample input := by
    exact witness.viewPreQueryDiscrepancy
  have currentPre : currentView.preQueryDiscrepancy =
      source.preQueryDiscrepancy sample input :=
    (congrArg JointQueryBatchPreChallengeView.preQueryDiscrepancy
      viewExact').trans witnessPre
  have witnessExpected : witness.view.expected =
      exactTag73K13ExpectedQueryVector decoder input k12 := by
    exact witness.viewExpected
  have currentExpected : currentView.expected =
      exactTag73K13ExpectedQueryVector decoder input k12 :=
    (congrArg JointQueryBatchPreChallengeView.expected viewExact').trans
      witnessExpected
  have witnessAuthenticated : witness.view.authenticated =
      exactTag73K13AuthenticatedQueryVector decoder input k12 := by
    exact witness.viewAuthenticated
  have currentAuthenticated : currentView.authenticated =
      exactTag73K13AuthenticatedQueryVector decoder input k12 :=
    (congrArg JointQueryBatchPreChallengeView.authenticated viewExact').trans
      witnessAuthenticated
  have currentMember : exactOperationalChallenge input .queryBatch ∈
      currentView.collisionTarget :=
    exactCandidateDirectedFunctionalView_collisionMember functional input k12
      collisionFacts candidate foldTrial finalTrial selected success
  change currentView.active = true ∧
    currentView.preQueryDiscrepancy = source.preQueryDiscrepancy sample input ∧
    currentView.expected = exactTag73K13ExpectedQueryVector decoder input k12 ∧
    currentView.authenticated =
      exactTag73K13AuthenticatedQueryVector decoder input k12 ∧
    exactOperationalChallenge input .queryBatch ∈ currentView.collisionTarget
  exact ⟨currentActive, currentPre, currentExpected, currentAuthenticated,
    currentMember⟩

#print axioms exactCandidateDirectedFunctionalView_alignedAt

end
end AspisK1.V7Tag73K13CandidateDirectedViewAlignedAt
