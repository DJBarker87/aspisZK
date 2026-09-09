import AspisFormal.K1.V7Tag73K13CandidateDirectedSourceBridge
import AspisFormal.K1.V7Tag73RootQueryBatchForkBridge

/-!
# Functional pre-challenge view for candidate-directed K1.3

The candidate-directed probability theorem needs one finite collision target
for each 542-coordinate fibre.  This module replaces the remaining
conclusion-shaped view-alignment structure by the exact deterministic claim:
two accepted witnesses on the same pre-query-batch coordinate fibre induce
the same algebraic view.

The construction below is generic.  It chooses a representative witness only
after proving the fibre is functional, then derives the existing source
alignment.  The remaining protocol theorem is therefore a pairwise causal
noninterference result, not an event inclusion or probability bound.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

namespace AspisK1.V7Tag73K13CandidateDirectedViewFunctional

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
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkDigestProbability
open AspisK1.V7Tag73JointQueryBatchSoundness
open AspisK1.V7Tag73K13CandidateDirectedCoordinateSelected
open AspisK1.V7Tag73K13CandidateDirectedProbabilityClosure
open AspisK1.V7Tag73K13CandidateDirectedSourceBridge
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

/-- One accepted source witness whose complete pre-query-batch information is
the supplied candidate-directed coordinate key.  The returned nonzero query
batch challenge is deliberately absent from the key. -/
structure ExactCandidateDirectedK13ViewWitness
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
  answers : FreshAnswerTape Digest256
    (exactCompilerTargetCaps parameters).length
  input : ExactK12OperationalInput transitionFuel configuration projection
    fixedInstance (hidden, answers)
  k12 : ExactPrefixK12Certificate input
  different : exactTag73K13ExpectedQueryVector decoder input k12 ≠
    exactTag73K13AuthenticatedQueryVector decoder input k12
  selected : ExactTag73CandidateDirectedCoordinateSelected input candidate
    foldTrial finalTrial
  success : GammaPrefixSucceeds
    (exactCandidateDirectedRegroupedCoordinates transitionFuel configuration
      candidate foldTrial finalTrial hidden answers).2.2.2
  contextExact :
    (exactCandidateDirectedRegroupedCoordinates transitionFuel configuration
      candidate foldTrial finalTrial hidden answers).1 = context
  foldExact :
    (exactCandidateDirectedRegroupedCoordinates transitionFuel configuration
      candidate foldTrial finalTrial hidden answers).2.1 = fold
  workExact :
    (exactCandidateDirectedRegroupedCoordinates transitionFuel configuration
      candidate foldTrial finalTrial hidden answers).2.2.1 = work
  skeletonExact :
    (successfulGammaPrefixFactorization
      ⟨(exactCandidateDirectedRegroupedCoordinates transitionFuel configuration
        candidate foldTrial finalTrial hidden answers).2.2.2, success⟩).1 =
      skeleton
  view : JointQueryBatchPreChallengeView
  viewExact : view = exactJointQueryBatchPreChallengeView decoder source input
    k12 different
  viewCollisionTarget : view.collisionTarget =
    exactTag73K13SourceCollisionTarget source input k12
  viewActive : view.active = true
  viewPreQueryDiscrepancy : view.preQueryDiscrepancy =
    source.preQueryDiscrepancy (hidden, answers) input
  viewExpected : view.expected =
    exactTag73K13ExpectedQueryVector decoder input k12
  viewAuthenticated : view.authenticated =
    exactTag73K13AuthenticatedQueryVector decoder input k12

/-- The exact algebraic target view carried by one source witness. -/
def ExactCandidateDirectedK13ViewWitness.preChallengeView
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
    {candidate : Q16DigestSlot}
    {foldTrial finalTrial : ExactCompilerExposureTrial parameters}
    {hidden : HiddenTape}
    {context : ExactCompilerFoldAlphaFinalWorkQ16QueryBatchResidual parameters ×
      (AlphaZeroDigestBlocks × Q16CandidateDigestForest)}
    {fold work : Digest256}
    {skeleton : VariableGammaCompleteSkeleton}
    (witness : ExactCandidateDirectedK13ViewWitness source candidate foldTrial
      finalTrial hidden context fold work skeleton) :
    JointQueryBatchPreChallengeView :=
  witness.view

/-- The remaining causal theorem in its minimal form: a 542-coordinate key
determines at most one active algebraic view. -/
def ExactCandidateDirectedK13ViewFunctional
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
      (left right : ExactCandidateDirectedK13ViewWitness source candidate
        foldTrial finalTrial hidden context fold work skeleton),
    left.preChallengeView = right.preChallengeView

/-- Canonical view selected from a functional fibre.  Empty fibres receive a
fixed inactive value and can never be used by the collision event. -/
noncomputable def exactCandidateDirectedFunctionalView
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
      (ExactCandidateDirectedK13ViewWitness source candidate foldTrial
        finalTrial hidden context fold work skeleton) then
    (Classical.choice present).preChallengeView
  else
    inactiveJointQueryBatchPreChallengeView 0 (fun _ => 0) (fun _ => 0)

theorem exactCandidateDirectedFunctionalView_eq
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
      configuration projection fixedInstance decoder source)
    {candidate : Q16DigestSlot}
    {foldTrial finalTrial : ExactCompilerExposureTrial parameters}
    {hidden : HiddenTape}
    {context : ExactCompilerFoldAlphaFinalWorkQ16QueryBatchResidual parameters ×
      (AlphaZeroDigestBlocks × Q16CandidateDigestForest)}
    {fold work : Digest256}
    {skeleton : VariableGammaCompleteSkeleton}
    (witness : ExactCandidateDirectedK13ViewWitness source candidate foldTrial
      finalTrial hidden context fold work skeleton) :
    exactCandidateDirectedFunctionalView source candidate foldTrial finalTrial
        hidden context fold work skeleton = witness.preChallengeView := by
  classical
  unfold exactCandidateDirectedFunctionalView
  rw [dif_pos ⟨witness⟩]
  exact functional candidate foldTrial finalTrial hidden context fold work
    skeleton (Classical.choice ⟨witness⟩) witness

#print axioms ExactCandidateDirectedK13ViewFunctional
#print axioms exactCandidateDirectedFunctionalView_eq

end
end AspisK1.V7Tag73K13CandidateDirectedViewFunctional
