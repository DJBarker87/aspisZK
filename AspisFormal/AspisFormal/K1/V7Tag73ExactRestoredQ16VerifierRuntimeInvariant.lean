import AspisFormal.K1.V7Tag73ExactRestoredQ16AnchorPartition
import AspisFormal.K1.V7Tag73ExactDagVerifierAnchorPrefix

/-!
# Restored q16 verifier-anchor runtime invariants

On the verifier-owned chronological partition, equality of the routed residual
coordinates preserves the completed prover return and its final oracle.  This
module transports that existing DAG replay result to the restoration-wide K1.3
objects.  In particular, the restored Merkle roots and canonically decoded
`final256` message are fixed before the selected final-work/q16 coordinate.

The alpha/gamma ledger fields and the adversary-first/cache-hit partition are
deliberately not claimed here.
-/

set_option autoImplicit false
set_option maxRecDepth 10000000

namespace AspisK1.V7Tag73ExactRestoredQ16VerifierRuntimeInvariant

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73CausalFinalWorkQ16UsedForest
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactDagVerifierAnchorPrefix
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRestoredOperationalK13Classifier
open AspisK1.V7Tag73ExactRestoredQ16ResidualFactorization
open AspisK1.V7Tag73ExactRestoredQ16SemanticNoninterference
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73RestoredDerivedK13View
open AspisK1.V7Tag73RestoredNodeK13Classifier
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The fixed DAG replay applies unchanged to proof-relevant restored q16 trial
witnesses: both retain the same literal operational input and actual-trial
certificate used by the fixed theorem. -/
noncomputable def exact_restored_root_verifier_anchor_preserves_prover_runtime
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactRestoredRootK13JointTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) trial)
    (rightWitness : ExactRestoredRootK13JointTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) trial)
    (anchor : ExactFixedK13VerifierAnchor leftWitness.input trial)
    (coordinateExact :
      (exactRestoredRootK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactRestoredRootK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1) :
    (exactK12Runtime rightWitness.input).adversaryValue =
        (exactK12Runtime leftWitness.input).adversaryValue ∧
      (exactK12Runtime rightWitness.input).proverFinalOracle =
        (exactK12Runtime leftWitness.input).proverFinalOracle := by
  obtain ⟨prior, later, target, answer, rootExact, trialExact⟩ := anchor
  apply exact_dag_residual_coordinate_preserves_prover_runtime_at_verifier_anchor
    leftWitness.input trial prior later target answer rootExact trialExact
      programmedCover right rightWitness.input
  change
    ((exactCompilerExposureTrialDagRouter parameters transitionFuel trial
      (exactPlainRomCursor configuration hidden).erase).coordinateEquiv
      (finalWorkQ16NamedSlotInputTape
        (exactCompilerFinalWorkQ16InputTape parameters left))).2 =
    ((exactCompilerExposureTrialDagRouter parameters transitionFuel trial
      (exactPlainRomCursor configuration hidden).erase).coordinateEquiv
      (finalWorkQ16NamedSlotInputTape
        (exactCompilerFinalWorkQ16InputTape parameters right))).2 at coordinateExact
  exact coordinateExact

/-- The two transcript roots are prover-controlled fields, so the preceding
runtime equality fixes them without a hash-injectivity premise. -/
noncomputable def exact_restored_root_verifier_anchor_preserves_roots
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactRestoredRootK13JointTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) trial)
    (rightWitness : ExactRestoredRootK13JointTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) trial)
    (anchor : ExactFixedK13VerifierAnchor leftWitness.input trial)
    (coordinateExact :
      (exactRestoredRootK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactRestoredRootK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1) :
    restoredNodeK12Roots
        leftWitness.input.package.root.fixedRoot.base.runtime.node =
      restoredNodeK12Roots
        rightWitness.input.package.root.fixedRoot.base.runtime.node := by
  have runtimeExact :=
    (exact_restored_root_verifier_anchor_preserves_prover_runtime programmedCover
      trial hidden left right leftWitness rightWitness anchor coordinateExact).1
  have rawExact := congrArg
    (fun value => value.rawMessages) runtimeExact.symm
  change exactK12Roots leftWitness.input = exactK12Roots rightWitness.input
  simpa [exactK12Roots] using congrArg
    (fun raw =>
      ({ c1 := runtimeDigest208ToMerkleDigest raw.c1Root
         c2 := runtimeDigest208ToMerkleDigest raw.c2Root } : Roots)) rawExact

/-- Canonical fixed-field decoding is functional across equal literal prover
returns, hence the restored disclosed final vector is identical on the
verifier-owned residual fibre. -/
noncomputable def exact_restored_root_verifier_anchor_preserves_disclosed_final
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactRestoredRootK13JointTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) trial)
    (rightWitness : ExactRestoredRootK13JointTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) trial)
    (anchor : ExactFixedK13VerifierAnchor leftWitness.input trial)
    (coordinateExact :
      (exactRestoredRootK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactRestoredRootK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1) :
    (exactRestoredRootK13View leftWitness.input).disclosedFinal =
      (exactRestoredRootK13View rightWitness.input).disclosedFinal := by
  let leftNode := leftWitness.input.package.root.fixedRoot.base.runtime.node
  let rightNode := rightWitness.input.package.root.fixedRoot.base.runtime.node
  let leftData := (exact_restored_operational_k13_provider leftWitness.input).data
    leftNode (exact_restoration_accumulator_contains_root leftWitness.input)
      (exact_restoration_accumulator_root_is_done leftWitness.input)
  let rightData := (exact_restored_operational_k13_provider rightWitness.input).data
    rightNode (exact_restoration_accumulator_contains_root rightWitness.input)
      (exact_restoration_accumulator_root_is_done rightWitness.input)
  have runtimeExact :=
    (exact_restored_root_verifier_anchor_preserves_prover_runtime programmedCover
      trial hidden left right leftWitness rightWitness anchor coordinateExact).1
  have rawExact : leftNode.adversaryValue.rawMessages =
      rightNode.adversaryValue.rawMessages := by
    change (exactK12Runtime leftWitness.input).adversaryValue.rawMessages =
      (exactK12Runtime rightWitness.input).adversaryValue.rawMessages
    exact congrArg (fun value => value.rawMessages) runtimeExact.symm
  have decodedExact : leftData.decoded = rightData.decoded := by
    funext index
    have leftDecode := leftData.fixedDecode index
    have rightDecode := rightData.fixedDecode index
    rw [rawExact] at leftDecode
    exact Option.some.inj (leftDecode.symm.trans rightDecode)
  change (restoredOperationalK13View leftData).disclosedFinal =
    (restoredOperationalK13View rightData).disclosedFinal
  exact congrArg decodedFinalMessage decodedExact

#print axioms exact_restored_root_verifier_anchor_preserves_prover_runtime
#print axioms exact_restored_root_verifier_anchor_preserves_roots
#print axioms
  exact_restored_root_verifier_anchor_preserves_disclosed_final

end
end AspisK1.V7Tag73ExactRestoredQ16VerifierRuntimeInvariant
