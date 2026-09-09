import AspisFormal.K1.V7Tag73K13CleanCausalSource
import AspisFormal.K1.V7Tag73K13CleanTargetMember
import AspisFormal.K1.V7Tag73K13CleanTrials
import AspisFormal.K1.V7Tag73K13CandidateDirectedSourceBridge

/-!
# Construct the compiler-clean K1.3 causal source

The scheduler selects the exact deployed coordinate.  Functional clean fibres
then supply the pre-fixed finite target containing the concrete collision.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

namespace AspisK1.V7Tag73K13CleanCausalSourceFromFunctional

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalFoldFinalWorkQueryBatchProbability
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13CandidateDirectedCoordinateSelected
open AspisK1.V7Tag73K13CandidateDirectedProbabilityClosure
open AspisK1.V7Tag73K13CandidateDirectedSourceBridge
open AspisK1.V7Tag73K13CleanCausalSource
open AspisK1.V7Tag73K13CleanTargetMember
open AspisK1.V7Tag73K13CleanTrials
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

noncomputable def ExactCleanCandidateDirectedK13ViewFunctional.toCausalSource
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
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 542 ≤ 2 * parameters.forkRequestCap) :
    ExactCleanCandidateDirectedK13CausalSource transitionFuel configuration
      projection fixedInstance decoder source where
  trials := exactCleanCandidateDirectedQueryBatchTrials transitionFuel
    configuration projection fixedInstance decoder source
  collisionMapped := by
    intro sample cleanMember input k12 collisionFacts
    obtain ⟨foldTrial, finalTrial, candidate, selected⟩ :=
      exact_operational_input_has_candidate_directed_coordinate transitionRoom
        programmedCover input
    obtain ⟨foldAccepted, finalAccepted, success, challengeExact⟩ :=
      exact_candidate_directed_selected_coordinate_components input selected
    refine ⟨candidate, foldTrial, finalTrial, ?_⟩
    let coordinates := exactCandidateDirectedRegroupedCoordinates
      transitionFuel configuration candidate foldTrial finalTrial sample.1
        sample.2
    let factored := successfulGammaPrefixFactorization
      ⟨coordinates.2.2.2, success⟩
    change coordinates.2 ∈ foldFinalWorkQueryBatchDependentEvent
      (fun fold work skeleton =>
        (exactCleanCandidateDirectedFunctionalView source candidate foldTrial
          finalTrial sample.1 coordinates.1 fold work skeleton).target)
    refine ⟨foldAccepted, finalAccepted, success, ?_⟩
    exact exactCleanCandidateDirectedFunctionalView_targetMember functional
      cleanMember input k12 collisionFacts candidate foldTrial finalTrial
      selected success challengeExact

#print axioms
  ExactCleanCandidateDirectedK13ViewFunctional.toCausalSource

end
end AspisK1.V7Tag73K13CleanCausalSourceFromFunctional
