import AspisFormal.K1.V7Tag73K13CandidateDirectedViewFacts
import AspisFormal.K1.V7Tag73K13CandidateDirectedViewFunctional
import AspisFormal.K1.V7Tag73K13PreQueryExecutionProjection
import AspisFormal.K1.V7Tag73K13PreChallengeSemanticCongruence

/-!
# Source factorization of the candidate-directed K1.3 pre-challenge data

The finite collision target may depend on exactly three algebraic values
computed before the query-batch challenge: the pre-query discrepancy and the
expected/authenticated query vectors.  This module states the narrow source
fact that those values factor through the 542-coordinate pre-answer key and
proves that it implies the functional-view theorem consumed by K1.3.

There is no event inclusion, probability inequality, or collision conclusion
in the source record below.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

namespace AspisK1.V7Tag73K13CandidateDirectedSourceFactorization

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13CandidateDirectedViewFunctional
open AspisK1.V7Tag73K13CandidateDirectedViewFacts
open AspisK1.V7Tag73K13PreQueryExecutionProjection
open AspisK1.V7Tag73K13PreChallengeSemanticCongruence
open AspisK1.V7Tag73K13RestrictedJointBatchActualLawClosure
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact
open AspisV6QueryBatchSoundness

noncomputable section

/-- The complete algebraic input to the degree-sixteen query-batch collision
polynomial, excluding the sampled challenge itself. -/
structure ExactCandidateDirectedK13PreChallengeData where
  preQueryDiscrepancy : QM31Exact
  expected : QueryVector QM31Exact
  authenticated : QueryVector QM31Exact

/-- The production/source endpoint required by the finite-fibre argument.
Every accepted witness projects to data selected solely from the fixed
candidate-directed coordinate key. -/
structure ExactCandidateDirectedK13SourceFactorization
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
  data : Q16DigestSlot →
    ExactCompilerExposureTrial parameters →
    ExactCompilerExposureTrial parameters → HiddenTape →
    (ExactCompilerFoldAlphaFinalWorkQ16QueryBatchResidual parameters ×
      (AlphaZeroDigestBlocks × Q16CandidateDigestForest)) →
    Digest256 → Digest256 → VariableGammaCompleteSkeleton →
      ExactCandidateDirectedK13PreChallengeData
  exactAt : ∀ candidate foldTrial finalTrial hidden context fold work skeleton
      (witness : ExactCandidateDirectedK13ViewWitness source candidate
        foldTrial finalTrial hidden context fold work skeleton),
    data candidate foldTrial finalTrial hidden context fold work skeleton =
      { preQueryDiscrepancy :=
          source.preQueryDiscrepancy (hidden, witness.answers) witness.input
        expected :=
          exactTag73K13ExpectedQueryVector decoder witness.input witness.k12
        authenticated :=
          exactTag73K13AuthenticatedQueryVector decoder witness.input
            witness.k12 }

/-- Minimal committed-source noninterference statement.  On one fixed
candidate-directed fibre, the literal pre-query scalar, parsed proof, and
authenticated K1.2 words agree.  The two query vectors are deliberately not
fields: their equality is derived below. -/
def ExactCandidateDirectedK13CommittedSourceInvariant
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
    source.preQueryDiscrepancy (hidden, left.answers) left.input =
        source.preQueryDiscrepancy (hidden, right.answers) right.input ∧
      exactK13ParsedProof left.input = exactK13ParsedProof right.input ∧
      left.k12.words = right.k12.words

/-- Production-facing committed-data invariant.  It retains the exact three
verifier values present at the pre-query snapshot and the two Merkle/code
vectors, rather than assuming equality of the already-combined discrepancy or
of the complete parsed proof. -/
def ExactCandidateDirectedK13CommittedExecutionInvariant
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
    exactK13PreQueryExecutionSnapshot
        (source.execution (hidden, left.answers) left.input) =
      exactK13PreQueryExecutionSnapshot
        (source.execution (hidden, right.answers) right.input) ∧
    exactTag73K13ExpectedQueryVector decoder left.input left.k12 =
      exactTag73K13ExpectedQueryVector decoder right.input right.k12 ∧
    exactTag73K13AuthenticatedQueryVector decoder left.input left.k12 =
      exactTag73K13AuthenticatedQueryVector decoder right.input right.k12

/-- Equality of the three pre-challenge components fixes the canonical active
view.  Its proof-valued fields are irrelevant by proof irrelevance. -/
theorem exactJointQueryBatchPreChallengeView_eq_of_components
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder}
    {leftSample rightSample : ExactCompilerSample HiddenTape parameters}
    {leftInput : ExactK12OperationalInput transitionFuel configuration
      projection fixedInstance leftSample}
    {rightInput : ExactK12OperationalInput transitionFuel configuration
      projection fixedInstance rightSample}
    {leftK12 : ExactPrefixK12Certificate leftInput}
    {rightK12 : ExactPrefixK12Certificate rightInput}
    {leftDifferent : exactTag73K13ExpectedQueryVector decoder leftInput leftK12 ≠
      exactTag73K13AuthenticatedQueryVector decoder leftInput leftK12}
    {rightDifferent :
      exactTag73K13ExpectedQueryVector decoder rightInput rightK12 ≠
        exactTag73K13AuthenticatedQueryVector decoder rightInput rightK12}
    (preExact : source.preQueryDiscrepancy leftSample leftInput =
      source.preQueryDiscrepancy rightSample rightInput)
    (expectedExact : exactTag73K13ExpectedQueryVector decoder leftInput leftK12 =
      exactTag73K13ExpectedQueryVector decoder rightInput rightK12)
    (authenticatedExact :
      exactTag73K13AuthenticatedQueryVector decoder leftInput leftK12 =
        exactTag73K13AuthenticatedQueryVector decoder rightInput rightK12) :
    exactJointQueryBatchPreChallengeView decoder source leftInput leftK12
        leftDifferent =
      exactJointQueryBatchPreChallengeView decoder source rightInput rightK12
        rightDifferent := by
  unfold exactJointQueryBatchPreChallengeView
  exact activeJointQueryBatchPreChallengeView_congr preExact expectedExact
    authenticatedExact

/-- A source factorization constructs the exact functional fibre required by
the candidate-directed K1.3 probability theorem. -/
theorem ExactCandidateDirectedK13SourceFactorization.toViewFunctional
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
    (factorization : ExactCandidateDirectedK13SourceFactorization transitionFuel
      configuration projection fixedInstance decoder source) :
    ExactCandidateDirectedK13ViewFunctional transitionFuel configuration
      projection fixedInstance decoder source := by
  intro candidate foldTrial finalTrial hidden context fold work skeleton
    left right
  have leftExact := factorization.exactAt candidate foldTrial finalTrial hidden
    context fold work skeleton left
  have rightExact := factorization.exactAt candidate foldTrial finalTrial hidden
    context fold work skeleton right
  have dataExact := leftExact.symm.trans rightExact
  have preExact := congrArg
    ExactCandidateDirectedK13PreChallengeData.preQueryDiscrepancy dataExact
  have expectedExact := congrArg
    ExactCandidateDirectedK13PreChallengeData.expected dataExact
  have authenticatedExact := congrArg
    ExactCandidateDirectedK13PreChallengeData.authenticated dataExact
  change left.view = right.view
  rw [left.viewExact, right.viewExact]
  exact exactJointQueryBatchPreChallengeView_eq_of_components preExact
    expectedExact authenticatedExact

/-- The minimal committed-source invariant implies the complete functional
view used by the finite-field probability theorem. -/
theorem ExactCandidateDirectedK13CommittedSourceInvariant.toViewFunctional
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
    (invariant : ExactCandidateDirectedK13CommittedSourceInvariant
      transitionFuel configuration projection fixedInstance decoder source) :
    ExactCandidateDirectedK13ViewFunctional transitionFuel configuration
      projection fixedInstance decoder source := by
  intro candidate foldTrial finalTrial hidden context fold work skeleton
    left right
  obtain ⟨preExact, proofExact, wordsExact⟩ := invariant candidate foldTrial
    finalTrial hidden context fold work skeleton left right
  have expectedExact := exactTag73K13ExpectedQueryVector_congr decoder
    left.input right.input left.k12 right.k12 proofExact
  have authenticatedExact := exactTag73K13AuthenticatedQueryVector_congr decoder
    left.input right.input left.k12 right.k12 proofExact wordsExact
  change left.view = right.view
  rw [left.viewExact, right.viewExact]
  exact exactJointQueryBatchPreChallengeView_eq_of_components preExact
    expectedExact authenticatedExact

/-- The concrete pre-query snapshot invariant implies the complete functional
view.  The discrepancy equality is derived from the pure relation evaluator. -/
theorem ExactCandidateDirectedK13CommittedExecutionInvariant.toViewFunctional
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
    (invariant : ExactCandidateDirectedK13CommittedExecutionInvariant
      transitionFuel configuration projection fixedInstance decoder source) :
    ExactCandidateDirectedK13ViewFunctional transitionFuel configuration
      projection fixedInstance decoder source := by
  intro candidate foldTrial finalTrial hidden context fold work skeleton
    left right
  obtain ⟨snapshotExact, expectedExact, authenticatedExact⟩ :=
    invariant candidate foldTrial finalTrial hidden context fold work skeleton
      left right
  have preExact :
      source.preQueryDiscrepancy (hidden, left.answers) left.input =
        source.preQueryDiscrepancy (hidden, right.answers) right.input := by
    rw [source.preQueryDiscrepancyExact, source.preQueryDiscrepancyExact]
    exact preQueryDiscrepancy_congr_of_projection_eq
      (source.execution (hidden, left.answers) left.input)
      (source.execution (hidden, right.answers) right.input) snapshotExact
  change left.view = right.view
  rw [left.viewExact, right.viewExact]
  exact exactJointQueryBatchPreChallengeView_eq_of_components preExact
    expectedExact authenticatedExact

#print axioms exactJointQueryBatchPreChallengeView_eq_of_components
#print axioms ExactCandidateDirectedK13SourceFactorization.toViewFunctional
#print axioms
  ExactCandidateDirectedK13CommittedSourceInvariant.toViewFunctional
#print axioms
  ExactCandidateDirectedK13CommittedExecutionInvariant.toViewFunctional

end
end AspisK1.V7Tag73K13CandidateDirectedSourceFactorization
