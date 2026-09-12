import AspisFormal.K1.V7Tag73K13CandidateBoundaryPrefixReplay
import AspisFormal.K1.V7Tag73K13CleanViewFunctional

/-!
# K1.3 pre-challenge view from the literal query-batch prefix

The candidate-directed scheduler proves that two accepted executions in one
pre-challenge fibre reach the selected query-batch request after the same
literal source-record prefix.  This file isolates the remaining production
source obligation: the small algebraic view consumed by the collision theorem
is a deterministic projection of that prefix.

This is a data factorization, not a collision, probability, or functional-view
conclusion.  A Rust/Aeneas bridge must provide the projection and prove
`exactAtBoundary` from the translated successful caller.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace AspisK1.V7Tag73K13ViewPrefixFactorization

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13CandidateBoundaryPrefixReplay
open AspisK1.V7Tag73K13CandidateDirectedViewFunctional
open AspisK1.V7Tag73K13CleanViewFunctional
open AspisK1.V7Tag73K13RestrictedJointBatchActualLawClosure
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Production/source factorization at the exact query-batch boundary.  The
projection reads the ordered literal SHA records preceding the request.  Its
source proof must show that every accepted selected-boundary decomposition
returns precisely the maintained active K1.3 view encoded by that prefix. -/
structure ExactCandidateDirectedK13ViewPrefixFactorization
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
      projection fixedInstance decoder) where
  viewFromPrefix : Q16DigestSlot →
    ExactCompilerExposureTrial parameters →
    ExactCompilerExposureTrial parameters → HiddenTape →
    (ExactCompilerFoldAlphaFinalWorkQ16QueryBatchResidual parameters ×
      (AlphaZeroDigestBlocks × Q16CandidateDigestForest)) →
    Digest256 → Digest256 → VariableGammaCompleteSkeleton →
    List UnifiedExposureRecord → JointQueryBatchPreChallengeView
  exactAtBoundary : ∀ candidate foldTrial finalTrial hidden context fold work
      skeleton
      (witness : ExactCandidateDirectedK13ViewWitness source candidate
        foldTrial finalTrial hidden context fold work skeleton)
      (blockAdvance queryBatchDigest : Digest256)
      (prior later : List UnifiedExposureRecord) (actor : QueryActor),
    exactFixedRootRecords witness.input.package.root =
        prior ++
          (.machineFresh actor
            (bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
            queryBatchDigest : UnifiedExposureRecord) :: later →
      witness.preChallengeView =
        viewFromPrefix candidate foldTrial finalTrial hidden context fold work
          skeleton prior

/-- Literal prefix factorization proves functional fibres.  The only scheduler
input is selected-boundary prefix equality; no hash injectivity or challenge
independence premise enters this reduction. -/
theorem ExactCandidateDirectedK13ViewPrefixFactorization.toViewFunctional
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
    (factorization : ExactCandidateDirectedK13ViewPrefixFactorization
      transitionFuel configuration projection fixedInstance decoder source)
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 542 ≤ 2 * parameters.forkRequestCap) :
    ExactCandidateDirectedK13ViewFunctional transitionFuel configuration
      projection fixedInstance decoder source := by
  intro candidate foldTrial finalTrial hidden context fold work skeleton
    left right
  obtain ⟨leftBlockAdvance, leftQueryBatchDigest, rightBlockAdvance,
      rightQueryBatchDigest, leftPrior, leftLater, rightPrior, rightLater,
      leftActor, rightActor, leftRoot, rightRoot, priorExact,
      _blockAdvanceExact⟩ :=
    candidate_witness_boundary_priors_eq transitionRoom programmedCover
      left right
  have leftExact := factorization.exactAtBoundary candidate foldTrial
    finalTrial hidden context fold work skeleton left leftBlockAdvance
      leftQueryBatchDigest leftPrior leftLater leftActor leftRoot
  have rightExact := factorization.exactAtBoundary candidate foldTrial
    finalTrial hidden context fold work skeleton right rightBlockAdvance
      rightQueryBatchDigest rightPrior rightLater rightActor rightRoot
  rw [leftExact, rightExact, priorExact]

/-- The operational probability layer restricts the same fibres to its clean
event.  Full prefix functionality therefore supplies the clean functionality
without an additional source premise. -/
theorem ExactCandidateDirectedK13ViewPrefixFactorization.toCleanViewFunctional
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
    (factorization : ExactCandidateDirectedK13ViewPrefixFactorization
      transitionFuel configuration projection fixedInstance decoder source)
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 542 ≤ 2 * parameters.forkRequestCap) :
    ExactCleanCandidateDirectedK13ViewFunctional transitionFuel configuration
      projection fixedInstance decoder source := by
  have functional := factorization.toViewFunctional transitionRoom
    programmedCover
  intro candidate foldTrial finalTrial hidden context fold work skeleton
    left right
  exact functional candidate foldTrial finalTrial hidden context fold work
    skeleton left.base right.base

#print axioms ExactCandidateDirectedK13ViewPrefixFactorization.toViewFunctional
#print axioms
  ExactCandidateDirectedK13ViewPrefixFactorization.toCleanViewFunctional

end
end AspisK1.V7Tag73K13ViewPrefixFactorization
