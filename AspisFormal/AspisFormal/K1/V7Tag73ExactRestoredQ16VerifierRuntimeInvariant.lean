import AspisFormal.K1.V7Tag73ExactRestoredQ16AnchorPartition
import AspisFormal.K1.V7Tag73ExactDagVerifierAnchorPrefix
import AspisFormal.K1.V7Tag73ExactK12UntypedVerifierSuffix
import AspisFormal.K1.V7Tag73RestoredK12CanonicalWordCongruence

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
set_option linter.defProp false

namespace AspisK1.V7Tag73ExactRestoredQ16VerifierRuntimeInvariant

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73CausalFinalWorkQ16UsedForest
open AspisK1.V7Tag73CanonicalOneFoldSchedule
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactDagVerifierAnchorPrefix
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
open AspisK1.V7Tag73ExactK12UntypedVerifierSuffix
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRestoredQ16AnchorPartition
open AspisK1.V7Tag73ExactRestoredOperationalK13Classifier
open AspisK1.V7Tag73ExactRestoredQ16ResidualFactorization
open AspisK1.V7Tag73ExactRestoredQ16SemanticNoninterference
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73RestoredK12CanonicalWordCongruence
open AspisK1.V7Tag73RestoredDerivedK13View
open AspisK1.V7Tag73RestoredNodeK13Classifier
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleUntypedErasureStability
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Appending inputs outside the Merkle grammar cannot change the retained
first-occurrence Merkle log.  Deduplication may keep some of those suffix
inputs, but the subsequent typed filter removes all of them. -/
theorem retain_typed_deduplicate_append_untyped
    (pre suffix : OrderedRawQueryLog)
    (suffixUntyped : ∀ input ∈ suffix,
      parseTypedPreimage input = none) :
    retainTypedMerkleQueries (deduplicateFirst (pre ++ suffix)) =
      retainTypedMerkleQueries (deduplicateFirst pre) := by
  obtain ⟨tail, exactAppend, tailSource⟩ :=
    AspisPool.V7MerkleCompletePrefixStability.deduplicateFirst_append_decompose
      pre suffix
  rw [exactAppend]
  unfold retainTypedMerkleQueries
  rw [List.filter_append]
  have tailEmpty : tail.filter
      (fun input => decide (parseTypedPreimage input ≠ none)) = [] := by
    by_contra nonempty
    obtain ⟨input, member⟩ := List.exists_mem_of_ne_nil _ nonempty
    have filtered := List.mem_filter.mp member
    have untyped := suffixUntyped input (tailSource input filtered.1)
    simp [untyped] at filtered
  rw [tailEmpty, List.append_nil]

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

/-- The accepted-tape projection is functional.  Once the completed prover
return is fixed, the entire checked deployed tape (including all verifier-owned
challenge bytes) is fixed as well. -/
noncomputable def exact_restored_root_verifier_anchor_preserves_operational_tape
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
    exactOperationalTape leftWitness.input =
      exactOperationalTape rightWitness.input := by
  have runtimeExact :=
    (exact_restored_root_verifier_anchor_preserves_prover_runtime programmedCover
      trial hidden left right leftWitness rightWitness anchor coordinateExact).1
  have leftProjected :=
    leftWitness.input.package.root.fixedRoot.base.projectedTape
  have rightProjected :=
    rightWitness.input.package.root.fixedRoot.base.projectedTape
  change rightWitness.input.package.root.fixedRoot.base.runtime.adversaryValue =
    leftWitness.input.package.root.fixedRoot.base.runtime.adversaryValue at runtimeExact
  rw [runtimeExact] at rightProjected
  exact Option.some.inj (leftProjected.symm.trans rightProjected)

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

/-- Gamma and alpha zero are verifier-ledger values, but the root source
theorem identifies them with the corresponding checked-tape bytes.  Functional
tape reconstruction therefore fixes gamma and the complete one-fold schedule
on the verifier-owned residual fibre. -/
noncomputable def exact_restored_root_verifier_anchor_preserves_gamma_schedule
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
    (exactRestoredRootK13View leftWitness.input).gamma =
        (exactRestoredRootK13View rightWitness.input).gamma ∧
      (exactRestoredRootK13View leftWitness.input).schedule =
        (exactRestoredRootK13View rightWitness.input).schedule := by
  let leftNode := leftWitness.input.package.root.fixedRoot.base.runtime.node
  let rightNode := rightWitness.input.package.root.fixedRoot.base.runtime.node
  let leftData := (exact_restored_operational_k13_provider leftWitness.input).data
    leftNode (exact_restoration_accumulator_contains_root leftWitness.input)
      (exact_restoration_accumulator_root_is_done leftWitness.input)
  let rightData := (exact_restored_operational_k13_provider rightWitness.input).data
    rightNode (exact_restoration_accumulator_contains_root rightWitness.input)
      (exact_restoration_accumulator_root_is_done rightWitness.input)
  have tapeExact :=
    exact_restored_root_verifier_anchor_preserves_operational_tape programmedCover
      trial hidden left right leftWitness rightWitness anchor coordinateExact
  have leftExact :=
    exact_restored_root_operational_data_challenges_are_source_exact
      leftWitness.input leftData
  have rightExact :=
    exact_restored_root_operational_data_challenges_are_source_exact
      rightWitness.input rightData
  have gammaExact : leftData.gamma = rightData.gamma := by
    rw [leftExact.2.1, rightExact.2.1, tapeExact]
  have alphaExact : leftData.alphaZero = rightData.alphaZero := by
    rw [leftExact.2.2.2, rightExact.2.2.2, tapeExact]
  change (restoredOperationalK13View leftData).gamma =
      (restoredOperationalK13View rightData).gamma ∧
    (restoredOperationalK13View leftData).schedule =
      (restoredOperationalK13View rightData).schedule
  exact ⟨gammaExact, congrArg canonicalOneFoldSchedule alphaExact⟩

/-- Once the completed prover runtime is fixed, the retained first-occurrence
Merkle log is fixed too.  The two verifier executions may append different
q16/transcript calls, but the exact driver theorem proves every such suffix
input untyped. -/
noncomputable def
    exact_restored_root_verifier_anchor_preserves_typed_merkle_queries
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
    retainTypedMerkleQueries (deduplicateFirst
        (restoredNodeK12OrderedQueries
          leftWitness.input.package.root.fixedRoot.base.runtime.node)) =
      retainTypedMerkleQueries (deduplicateFirst
        (restoredNodeK12OrderedQueries
          rightWitness.input.package.root.fixedRoot.base.runtime.node)) := by
  have runtimeExact :=
    exact_restored_root_verifier_anchor_preserves_prover_runtime programmedCover
      trial hidden left right leftWitness rightWitness anchor coordinateExact
  obtain ⟨leftSuffix, leftLog, leftUntyped⟩ :=
    exact_k12_ordered_queries_eq_prover_prefix_append_untyped
      leftWitness.input
  obtain ⟨rightSuffix, rightLog, rightUntyped⟩ :=
    exact_k12_ordered_queries_eq_prover_prefix_append_untyped
      rightWitness.input
  have prefixExact : exactK12ProverPrefixQueries leftWitness.input =
      exactK12ProverPrefixQueries rightWitness.input := by
    unfold exactK12ProverPrefixQueries
    rw [runtimeExact.2]
  change retainTypedMerkleQueries
      (deduplicateFirst (exactK12OrderedQueries leftWitness.input)) =
    retainTypedMerkleQueries
      (deduplicateFirst (exactK12OrderedQueries rightWitness.input))
  rw [leftLog, rightLog, prefixExact,
    retain_typed_deduplicate_append_untyped _ _ leftUntyped,
    retain_typed_deduplicate_append_untyped _ _ rightUntyped]

/-- On typed Merkle preimages, each verifier-final hash view reduces to the
fixed prover-final oracle.  Equality of the replayed prover state therefore
gives the pointwise hash agreement needed by complete-tree extraction. -/
noncomputable def
    exact_restored_root_verifier_anchor_preserves_typed_hash_view
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
    ∀ input, parseTypedPreimage input ≠ none →
      restoredNodeK12Truncate
          leftWitness.input.package.root.fixedRoot.base.runtime.node input =
        restoredNodeK12Truncate
          rightWitness.input.package.root.fixedRoot.base.runtime.node input := by
  have runtimeExact :=
    exact_restored_root_verifier_anchor_preserves_prover_runtime programmedCover
      trial hidden left right leftWitness rightWitness anchor coordinateExact
  intro input typed
  change exactK12Truncate leftWitness.input input =
    exactK12Truncate rightWitness.input input
  calc
    exactK12Truncate leftWitness.input input =
        exactK12ProverTruncate leftWitness.input input :=
      exact_k12_truncate_eq_prover_truncate_on_typed leftWitness.input input typed
    _ = exactK12ProverTruncate rightWitness.input input := by
      unfold exactK12ProverTruncate
      rw [runtimeExact.2]
    _ = exactK12Truncate rightWitness.input input :=
      (exact_k12_truncate_eq_prover_truncate_on_typed rightWitness.input input
        typed).symm

/-- The verifier-first branch of restored K1.3 is now fully discharged.  The
committed Merkle candidate and all three pre-q16 semantic fields are invariant
across equal routed residual coordinates. -/
noncomputable def
    exact_restored_root_committed_pre_q16_invariant_on_verifier_anchors
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap) :
    ExactRestoredRootCommittedPreQ16InvariantOnVerifierAnchors transitionFuel
      configuration projection fixedInstance decoder := by
  intro trial hidden left right leftWitness rightWitness anchor coordinateExact
  have rootsExact :=
    exact_restored_root_verifier_anchor_preserves_roots programmedCover trial
      hidden left right leftWitness rightWitness anchor coordinateExact
  have typedQueriesExact :=
    exact_restored_root_verifier_anchor_preserves_typed_merkle_queries
      programmedCover trial hidden left right leftWitness rightWitness anchor
        coordinateExact
  have typedHashExact :=
    exact_restored_root_verifier_anchor_preserves_typed_hash_view
      programmedCover trial hidden left right leftWitness rightWitness anchor
        coordinateExact
  obtain ⟨candidate, leftGraph, rightGraph⟩ :=
    restored_root_common_complete_candidate_of_typed_hash_agreement
      leftWitness.input rightWitness.input leftWitness.k12 rightWitness.k12
        typedHashExact rootsExact typedQueriesExact
  have gammaSchedule :=
    exact_restored_root_verifier_anchor_preserves_gamma_schedule programmedCover
      trial hidden left right leftWitness rightWitness anchor coordinateExact
  have disclosedFinal :=
    exact_restored_root_verifier_anchor_preserves_disclosed_final programmedCover
      trial hidden left right leftWitness rightWitness anchor coordinateExact
  exact ⟨candidate, leftGraph, rightGraph, gammaSchedule.1, disclosedFinal,
    gammaSchedule.2⟩

#print axioms exact_restored_root_verifier_anchor_preserves_prover_runtime
#print axioms exact_restored_root_verifier_anchor_preserves_operational_tape
#print axioms exact_restored_root_verifier_anchor_preserves_roots
#print axioms
  exact_restored_root_verifier_anchor_preserves_disclosed_final
#print axioms
  exact_restored_root_verifier_anchor_preserves_gamma_schedule
#print axioms
  exact_restored_root_verifier_anchor_preserves_typed_merkle_queries
#print axioms
  exact_restored_root_verifier_anchor_preserves_typed_hash_view
#print axioms
  exact_restored_root_committed_pre_q16_invariant_on_verifier_anchors

end
end AspisK1.V7Tag73ExactRestoredQ16VerifierRuntimeInvariant
