import AspisFormal.K1.V7Tag73K13CandidateDirectedViewFunctional
import AspisFormal.K1.V7Tag73ExactFixedInstanceEvent

/-!
# Compiler-clean candidate-directed K1.3 view fibres

Only executions in the fixed compiler-clean event are relevant to the release
bound.  Carrying that membership in the witness prevents the causal theorem
from quantifying over manually fabricated operational-input records that were
not produced by a clean run.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

namespace AspisK1.V7Tag73K13CleanViewFunctional

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13CandidateDirectedViewFunctional
open AspisK1.V7Tag73K13RestrictedJointBatchActualLawClosure
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- One ordinary candidate-directed witness plus evidence that its exact
sample belongs to the fixed compiler-clean event. -/
structure ExactCleanCandidateDirectedK13ViewWitness
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder)
    (candidate : Q16DigestSlot)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (context : ExactCompilerFoldAlphaFinalWorkQ16QueryBatchResidual parameters ×
      (AlphaZeroDigestBlocks × Q16CandidateDigestForest))
    (fold work : Digest256)
    (skeleton : VariableGammaCompleteSkeleton) : Type where
  base : ExactCandidateDirectedK13ViewWitness source candidate foldTrial
    finalTrial hidden context fold work skeleton
  cleanMember : (hidden, base.answers) ∈
    exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration projection
      fixedInstance

def ExactCleanCandidateDirectedK13ViewFunctional
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder) : Prop :=
  ∀ candidate foldTrial finalTrial hidden context fold work skeleton
      (left right : ExactCleanCandidateDirectedK13ViewWitness source candidate
        foldTrial finalTrial hidden context fold work skeleton),
    left.base.preChallengeView = right.base.preChallengeView

/-- Canonical view of a clean fibre; an empty clean fibre receives the fixed
inactive view and is never used by a clean collision witness. -/
noncomputable def exactCleanCandidateDirectedFunctionalView
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder)
    (candidate : Q16DigestSlot)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (context : ExactCompilerFoldAlphaFinalWorkQ16QueryBatchResidual parameters ×
      (AlphaZeroDigestBlocks × Q16CandidateDigestForest))
    (fold work : Digest256)
    (skeleton : VariableGammaCompleteSkeleton) :
    JointQueryBatchPreChallengeView := by
  classical
  exact if present : Nonempty
      (ExactCleanCandidateDirectedK13ViewWitness source candidate foldTrial
        finalTrial hidden context fold work skeleton) then
    (Classical.choice present).base.preChallengeView
  else
    inactiveJointQueryBatchPreChallengeView 0 (fun _ => 0) (fun _ => 0)

theorem exactCleanCandidateDirectedFunctionalView_eq
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
    {candidate foldTrial finalTrial hidden context fold work skeleton}
    (witness : ExactCleanCandidateDirectedK13ViewWitness source candidate
      foldTrial finalTrial hidden context fold work skeleton) :
    exactCleanCandidateDirectedFunctionalView source candidate foldTrial
        finalTrial hidden context fold work skeleton =
      witness.base.preChallengeView := by
  classical
  rw [exactCleanCandidateDirectedFunctionalView, dif_pos ⟨witness⟩]
  exact functional candidate foldTrial finalTrial hidden context fold work
    skeleton (Classical.choice ⟨witness⟩) witness

#print axioms ExactCleanCandidateDirectedK13ViewFunctional
#print axioms exactCleanCandidateDirectedFunctionalView_eq

end
end AspisK1.V7Tag73K13CleanViewFunctional
