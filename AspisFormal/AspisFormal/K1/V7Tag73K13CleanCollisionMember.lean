import AspisFormal.K1.V7Tag73K13CleanViewFunctional
import AspisFormal.K1.V7Tag73K13CandidateDirectedViewWitnessAt
import AspisFormal.K1.V7Tag73K13CandidateDirectedViewFacts

/-! # Collision membership in the compiler-clean canonical K1.3 view -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.constructorNameAsVariable false

namespace AspisK1.V7Tag73K13CleanCollisionMember

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
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73JointQueryBatchSoundness
open AspisK1.V7Tag73K13CandidateDirectedCoordinateSelected
open AspisK1.V7Tag73K13CandidateDirectedProbabilityClosure
open AspisK1.V7Tag73K13CandidateDirectedViewWitnessAt
open AspisK1.V7Tag73K13CandidateDirectedViewFacts
open AspisK1.V7Tag73K13CleanViewFunctional
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

theorem exactCleanCandidateDirectedFunctionalView_collisionMember
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
    (functional : ExactCleanCandidateDirectedK13ViewFunctional transitionFuel
      configuration projection fixedInstance decoder source)
    {sample : ExactCompilerSample HiddenTape parameters}
    (cleanMember : sample ∈ exactFixedPlainRomLegalSameTapeEvent transitionFuel
      configuration projection fixedInstance)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input)
    (collisionFacts : ExactTag73K13CollisionCertificate source input k12)
    (candidate : Q16DigestSlot)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (selected : ExactTag73CandidateDirectedCoordinateSelected input candidate
      foldTrial finalTrial)
    (success : GammaPrefixSucceeds
      (exactCandidateDirectedRegroupedCoordinates transitionFuel configuration
        candidate foldTrial finalTrial sample.1 sample.2).2.2.2) :
    let coordinates := exactCandidateDirectedRegroupedCoordinates
      transitionFuel configuration candidate foldTrial finalTrial sample.1
        sample.2
    let factored := successfulGammaPrefixFactorization
      ⟨coordinates.2.2.2, success⟩
    exactOperationalChallenge input .queryBatch ∈
      (exactCleanCandidateDirectedFunctionalView source candidate foldTrial
        finalTrial sample.1 coordinates.1 coordinates.2.1 coordinates.2.2.1
          factored.1).collisionTarget := by
  let coordinates := exactCandidateDirectedRegroupedCoordinates
    transitionFuel configuration candidate foldTrial finalTrial sample.1
      sample.2
  let factored := successfulGammaPrefixFactorization
    ⟨coordinates.2.2.2, success⟩
  let base := exactCandidateDirectedK13ViewWitnessAt source input k12
    collisionFacts.different candidate foldTrial finalTrial selected success
  let witness : ExactCleanCandidateDirectedK13ViewWitness source candidate
      foldTrial finalTrial sample.1 coordinates.1 coordinates.2.1
        coordinates.2.2.1 factored.1 :=
    { base := base, cleanMember := cleanMember }
  have viewExact := exactCleanCandidateDirectedFunctionalView_eq functional
    witness
  change exactCleanCandidateDirectedFunctionalView source candidate foldTrial
      finalTrial sample.1 coordinates.1 coordinates.2.1 coordinates.2.2.1
        factored.1 = witness.base.preChallengeView at viewExact
  have witnessTarget : witness.base.view.collisionTarget =
      exactTag73K13SourceCollisionTarget source input k12 :=
    witness.base.viewCollisionTarget
  have currentTarget :
      (exactCleanCandidateDirectedFunctionalView source candidate foldTrial
        finalTrial sample.1 coordinates.1 coordinates.2.1 coordinates.2.2.1
          factored.1).collisionTarget = collisionFacts.target :=
    (congrArg JointQueryBatchPreChallengeView.collisionTarget viewExact).trans
      (witnessTarget.trans collisionFacts.targetExact.symm)
  exact memLeftOfFinsetEq currentTarget collisionFacts.collision

#print axioms exactCleanCandidateDirectedFunctionalView_collisionMember

end
end AspisK1.V7Tag73K13CleanCollisionMember
