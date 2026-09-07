import AspisFormal.K1.V7Tag73ExactRestoredCleanPairFactorization
import AspisFormal.K1.V7Tag73ExactRestoredQ16SemanticNoninterference
import AspisFormal.K1.V7Tag73ExactPairCoordinateProfileInvariant
import AspisFormal.K1.V7Tag73ExactRestoredQ16VerifierRuntimeInvariant

/-!
# Semantic endpoint for the sound restored K1.3 pair factorization

The probability theorem fixes the residual/alpha context and both positioned
work answers.  This file states the exact deterministic source consequence and
proves that it is sufficient for equality of the restored consistency sets.
No q16 coordinate occurs in the semantic premise.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace AspisK1.V7Tag73ExactRestoredCleanPairSemanticNoninterference

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
open AspisK1.V7Tag73ExactDagVerifierAnchorPrefix
open AspisK1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactPairCoordinateProfileInvariant
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactRestoredCleanPairFactorization
open AspisK1.V7Tag73ExactRestoredQ16ResidualFactorization
open AspisK1.V7Tag73ExactRestoredQ16SemanticNoninterference
open AspisK1.V7Tag73ExactRestoredQ16VerifierRuntimeInvariant
open AspisK1.V7Tag73ExactRestoredOperationalK13Classifier
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73FoldAlphaPreFinalPrefix
open AspisK1.V7Tag73FoldArmedPreFinalPrefix
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisK1.V7Tag73ProjectedMachineNativeRequestPrefix
open AspisK1.V7Tag73K12BudgetedSchedulerTree
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16RawENNRealProbability
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73CanonicalOneFoldSchedule
open AspisK1.V7Tag73RestoredK12CanonicalWordCongruence
open AspisK1.V7Tag73RestoredDerivedK13View
open AspisK1.V7Tag73RestoredNodeK13Classifier
open AspisK1.V7Tag73ExactK12UntypedVerifierSuffix
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleUntypedErasureStability
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- On the verifier-first final-work branch, the sound 518-coordinate fibre
replays the complete prover run.  This is the restored-witness form of the
source chronology lemma: its proof uses only the literal operational input and
the fold/final trial indices, never the fixed-root intrinsic bad set. -/
theorem exact_restored_clean_pair_verifier_anchor_preserves_prover_runtime
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactRestoredRootCleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) foldTrial
        finalTrial)
    (rightWitness : ExactRestoredRootCleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) foldTrial
        finalTrial)
    (anchor : ExactFixedK13VerifierAnchor leftWitness.joint.input finalTrial)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (contextExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).1)
    (foldExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).2.1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).2.1) :
    (exactK12Runtime rightWitness.joint.input).adversaryValue =
        (exactK12Runtime leftWitness.joint.input).adversaryValue ∧
      (exactK12Runtime rightWitness.joint.input).proverFinalOracle =
        (exactK12Runtime leftWitness.joint.input).proverFinalOracle := by
  obtain ⟨prior, later, target, answer, rootExact, trialExact⟩ := anchor
  obtain ⟨verifierPrior, _verifierLater, _verifierExact, priorExact⟩ :=
    exact_dag_verifier_root_record_has_completed_prover_prefix
      leftWitness.joint.input prior later target answer rootExact
  obtain ⟨rightRemaining, rightPrefix⟩ :=
    exact_fold_armed_coordinates_force_pre_final_tape_prefix
      leftWitness.joint.input foldTrial finalTrial prior
      ((.machineFresh .verifier target answer : UnifiedExposureRecord) :: later)
      (by simpa only [List.cons_append] using rootExact) trialExact
      programmedCover right contextExact foldExact
  rw [fold_alpha_final_work_q16_named_slot_tape_preserves_master_list]
    at rightPrefix
  have priorAnswers : prior.map UnifiedExposureRecord.answer =
      leftWitness.joint.input.package.root.full.projection.rootPrefixes.adversary.freshQueries.map
          Prod.snd ++ verifierPrior.map Prod.snd := by
    rw [priorExact, List.map_append, projected_machine_fresh_record_answers,
      projected_machine_fresh_record_answers]
  rw [priorAnswers] at rightPrefix
  have leftReplay := k12_prover_run_from_completed_prefix_append_exact
    configuration.machine hidden (freshAnswerTapeToList left)
    leftWitness.joint.input.package.root.fixedRoot.base.runtime
    leftWitness.joint.input.package.root.full.projection.rootPrefixes
    (verifierPrior.map Prod.snd ++ rightRemaining)
  have leftReplay' : k12ProverRunFromAnswerPrefix configuration.machine hidden
      (freshAnswerTapeToList right) =
        { halt := .returned
            leftWitness.joint.input.package.root.full.projection.rootPrefixes.adversaryValue
          oracle :=
            leftWitness.joint.input.package.root.full.projection.rootPrefixes.adversary.finalState
          steps :=
            leftWitness.joint.input.package.root.full.projection.rootPrefixes.adversary.steps } := by
    rw [rightPrefix]
    simpa only [List.append_assoc] using leftReplay
  let rightPrefixes :=
    rightWitness.joint.input.package.root.full.projection.rootPrefixes
  have rightReplay := k12_prover_run_from_completed_prefix_append_exact
    configuration.machine hidden (freshAnswerTapeToList right)
    rightWitness.joint.input.package.root.fixedRoot.base.runtime rightPrefixes
    rightPrefixes.adversary.remaining
  have rightAvailable : freshAnswerTapeToList right =
      rightPrefixes.adversary.freshQueries.map Prod.snd ++
        rightPrefixes.adversary.remaining := by
    simpa [rightPrefixes] using rightPrefixes.adversary.availableExact
  rw [← rightAvailable] at rightReplay
  have rawRunExact := leftReplay'.symm.trans rightReplay
  constructor
  · have haltExact := congrArg (fun run => run.halt) rawRunExact
    have valueExact :
        leftWitness.joint.input.package.root.full.projection.rootPrefixes.adversaryValue =
          rightPrefixes.adversaryValue := by
      simpa only [MachineHalt.returned.injEq] using haltExact
    have leftRuntime := congrArg (fun runtime => runtime.adversaryValue)
      leftWitness.joint.input.package.root.full.projection.rootPrefixes.runtimeExact
    have rightRuntime := congrArg (fun runtime => runtime.adversaryValue)
      rightPrefixes.runtimeExact
    simpa [rightPrefixes, exactK12Runtime, operationalRootRuntime] using
      rightRuntime.trans (valueExact.symm.trans leftRuntime.symm)
  · have oracleExact := congrArg (fun run => run.oracle) rawRunExact
    have leftRuntime := congrArg (fun runtime => runtime.proverFinalOracle)
      leftWitness.joint.input.package.root.full.projection.rootPrefixes.runtimeExact
    have rightRuntime := congrArg (fun runtime => runtime.proverFinalOracle)
      rightPrefixes.runtimeExact
    simpa [rightPrefixes, exactK12Runtime, operationalRootRuntime] using
      rightRuntime.trans (oracleExact.symm.trans leftRuntime.symm)

/-- The runtime equality above fixes the complete restored K1.2 candidate and
the verifier-derived K1.3 fields.  Verifier-only suffix queries are erased only
after the typed-Merkle filter; no equality of the q16 suffix is asserted. -/
theorem exact_restored_clean_pair_verifier_anchor_semantics_eq
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactRestoredRootCleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) foldTrial
        finalTrial)
    (rightWitness : ExactRestoredRootCleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) foldTrial
        finalTrial)
    (anchor : ExactFixedK13VerifierAnchor leftWitness.joint.input finalTrial)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (contextExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).1)
    (foldExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).2.1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).2.1) :
    leftWitness.joint.k12.words = rightWitness.joint.k12.words ∧
      (exactRestoredRootK13View leftWitness.joint.input).gamma =
        (exactRestoredRootK13View rightWitness.joint.input).gamma ∧
      (exactRestoredRootK13View leftWitness.joint.input).disclosedFinal =
        (exactRestoredRootK13View rightWitness.joint.input).disclosedFinal ∧
      (exactRestoredRootK13View leftWitness.joint.input).schedule =
        (exactRestoredRootK13View rightWitness.joint.input).schedule := by
  have runtimeExact :=
    exact_restored_clean_pair_verifier_anchor_preserves_prover_runtime
      foldTrial finalTrial hidden left right leftWitness rightWitness anchor
        programmedCover contextExact foldExact
  have tapeExact : exactOperationalTape leftWitness.joint.input =
      exactOperationalTape rightWitness.joint.input := by
    have leftProjected :=
      leftWitness.joint.input.package.root.fixedRoot.base.projectedTape
    have rightProjected :=
      rightWitness.joint.input.package.root.fixedRoot.base.projectedTape
    have runtimeAdversaryExact := runtimeExact.1
    change rightWitness.joint.input.package.root.fixedRoot.base.runtime.adversaryValue =
      leftWitness.joint.input.package.root.fixedRoot.base.runtime.adversaryValue
        at runtimeAdversaryExact
    rw [runtimeAdversaryExact] at rightProjected
    exact Option.some.inj (leftProjected.symm.trans rightProjected)
  have rootsExact : restoredNodeK12Roots
        leftWitness.joint.input.package.root.fixedRoot.base.runtime.node =
      restoredNodeK12Roots
        rightWitness.joint.input.package.root.fixedRoot.base.runtime.node := by
    have rawExact := congrArg (fun value => value.rawMessages)
      runtimeExact.1.symm
    change exactK12Roots leftWitness.joint.input =
      exactK12Roots rightWitness.joint.input
    simpa [exactK12Roots] using congrArg
      (fun raw =>
        ({ c1 := runtimeDigest208ToMerkleDigest raw.c1Root
           c2 := runtimeDigest208ToMerkleDigest raw.c2Root } : Roots)) rawExact
  have typedQueriesExact : retainTypedMerkleQueries (deduplicateFirst
        (restoredNodeK12OrderedQueries
          leftWitness.joint.input.package.root.fixedRoot.base.runtime.node)) =
      retainTypedMerkleQueries (deduplicateFirst
        (restoredNodeK12OrderedQueries
          rightWitness.joint.input.package.root.fixedRoot.base.runtime.node)) := by
    obtain ⟨leftSuffix, leftLog, leftUntyped⟩ :=
      exact_k12_ordered_queries_eq_prover_prefix_append_untyped
        leftWitness.joint.input
    obtain ⟨rightSuffix, rightLog, rightUntyped⟩ :=
      exact_k12_ordered_queries_eq_prover_prefix_append_untyped
        rightWitness.joint.input
    have prefixExact : exactK12ProverPrefixQueries leftWitness.joint.input =
        exactK12ProverPrefixQueries rightWitness.joint.input := by
      unfold exactK12ProverPrefixQueries
      rw [runtimeExact.2]
    change retainTypedMerkleQueries
        (deduplicateFirst (exactK12OrderedQueries leftWitness.joint.input)) =
      retainTypedMerkleQueries
        (deduplicateFirst (exactK12OrderedQueries rightWitness.joint.input))
    rw [leftLog, rightLog, prefixExact,
      retain_typed_deduplicate_append_untyped _ _ leftUntyped,
      retain_typed_deduplicate_append_untyped _ _ rightUntyped]
  have typedHashExact : ∀ input, parseTypedPreimage input ≠ none →
      restoredNodeK12Truncate
          leftWitness.joint.input.package.root.fixedRoot.base.runtime.node input =
        restoredNodeK12Truncate
          rightWitness.joint.input.package.root.fixedRoot.base.runtime.node input := by
    intro input typed
    change exactK12Truncate leftWitness.joint.input input =
      exactK12Truncate rightWitness.joint.input input
    calc
      exactK12Truncate leftWitness.joint.input input =
          exactK12ProverTruncate leftWitness.joint.input input :=
        exact_k12_truncate_eq_prover_truncate_on_typed
          leftWitness.joint.input input typed
      _ = exactK12ProverTruncate rightWitness.joint.input input := by
        unfold exactK12ProverTruncate
        rw [runtimeExact.2]
      _ = exactK12Truncate rightWitness.joint.input input :=
        (exact_k12_truncate_eq_prover_truncate_on_typed
          rightWitness.joint.input input typed).symm
  obtain ⟨candidate, leftGraph, rightGraph⟩ :=
    restored_root_common_complete_candidate_of_typed_hash_agreement
      leftWitness.joint.input rightWitness.joint.input leftWitness.joint.k12
        rightWitness.joint.k12 typedHashExact rootsExact typedQueriesExact
  have wordsExact : leftWitness.joint.k12.words =
      rightWitness.joint.k12.words := by
    apply extract_v7_words_success_words_eq_of_same_complete_candidate
      (restoredNodeK12Truncate
        leftWitness.joint.input.package.root.fixedRoot.base.runtime.node)
      (restoredNodeK12Truncate
        rightWitness.joint.input.package.root.fixedRoot.base.runtime.node)
      (restoredNodeK12Roots
        leftWitness.joint.input.package.root.fixedRoot.base.runtime.node)
      (restoredNodeK12Roots
        rightWitness.joint.input.package.root.fixedRoot.base.runtime.node)
      (restoredNodeK12Openings
        leftWitness.joint.input.package.root.fixedRoot.base.runtime.node)
      (restoredNodeK12Openings
        rightWitness.joint.input.package.root.fixedRoot.base.runtime.node)
      (restoredNodeK12OrderedQueries
        leftWitness.joint.input.package.root.fixedRoot.base.runtime.node)
      (restoredNodeK12OrderedQueries
        rightWitness.joint.input.package.root.fixedRoot.base.runtime.node)
      candidate
    · simpa [exactRestoredRootCompleteWords] using leftGraph
    · simpa [exactRestoredRootCompleteWords] using rightGraph
    · exact leftWitness.joint.k12.extracted
    · exact rightWitness.joint.k12.extracted
  let leftNode := leftWitness.joint.input.package.root.fixedRoot.base.runtime.node
  let rightNode := rightWitness.joint.input.package.root.fixedRoot.base.runtime.node
  let leftData :=
    (exact_restored_operational_k13_provider leftWitness.joint.input).data
      leftNode (exact_restoration_accumulator_contains_root leftWitness.joint.input)
        (exact_restoration_accumulator_root_is_done leftWitness.joint.input)
  let rightData :=
    (exact_restored_operational_k13_provider rightWitness.joint.input).data
      rightNode (exact_restoration_accumulator_contains_root rightWitness.joint.input)
        (exact_restoration_accumulator_root_is_done rightWitness.joint.input)
  have leftChallengeExact :=
    exact_restored_root_operational_data_challenges_are_source_exact
      leftWitness.joint.input leftData
  have rightChallengeExact :=
    exact_restored_root_operational_data_challenges_are_source_exact
      rightWitness.joint.input rightData
  have gammaExact : leftData.gamma = rightData.gamma := by
    rw [leftChallengeExact.2.1, rightChallengeExact.2.1, tapeExact]
  have alphaExact : leftData.alphaZero = rightData.alphaZero := by
    rw [leftChallengeExact.2.2.2, rightChallengeExact.2.2.2, tapeExact]
  have rawExact : leftNode.adversaryValue.rawMessages =
      rightNode.adversaryValue.rawMessages := by
    change (exactK12Runtime leftWitness.joint.input).adversaryValue.rawMessages =
      (exactK12Runtime rightWitness.joint.input).adversaryValue.rawMessages
    exact congrArg (fun value => value.rawMessages) runtimeExact.1.symm
  have decodedExact : leftData.decoded = rightData.decoded := by
    funext index
    have leftDecode := leftData.fixedDecode index
    have rightDecode := rightData.fixedDecode index
    rw [rawExact] at leftDecode
    exact Option.some.inj (leftDecode.symm.trans rightDecode)
  refine ⟨wordsExact, gammaExact, ?_,
    congrArg canonicalOneFoldSchedule alphaExact⟩
  change (restoredOperationalK13View leftData).disclosedFinal =
    (restoredOperationalK13View rightData).disclosedFinal
  exact congrArg decodedFinalMessage decodedExact

/-- The precise source theorem left after the 518-coordinate factorization.
The restored consistency set reads exactly these four fields. -/
def ExactRestoredRootCleanK13PairSemanticInvariant
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) : Prop :=
  ∀ (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
      (hidden : HiddenTape)
      (left right : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length)
      (leftWitness : ExactRestoredRootCleanK13PairTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, left)
          foldTrial finalTrial)
      (rightWitness : ExactRestoredRootCleanK13PairTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, right)
          foldTrial finalTrial),
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).1) →
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).2.1) →
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).2.2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).2.2.1) →
    leftWitness.joint.k12.words = rightWitness.joint.k12.words ∧
      (exactRestoredRootK13View leftWitness.joint.input).gamma =
        (exactRestoredRootK13View rightWitness.joint.input).gamma ∧
      (exactRestoredRootK13View leftWitness.joint.input).disclosedFinal =
        (exactRestoredRootK13View rightWitness.joint.input).disclosedFinal ∧
      (exactRestoredRootK13View leftWitness.joint.input).schedule =
        (exactRestoredRootK13View rightWitness.joint.input).schedule

/-- The semantic source endpoint is exactly sufficient for the pointwise bad
set invariant consumed by the probability package. -/
theorem exact_restored_clean_k13_pair_coordinate_invariant_of_semantic
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (semantic : ExactRestoredRootCleanK13PairSemanticInvariant transitionFuel
      configuration projection fixedInstance decoder) :
    ExactRestoredRootCleanK13PairCoordinateInvariant transitionFuel configuration
      projection fixedInstance decoder := by
  intro foldTrial finalTrial hidden left right leftMember rightMember
  dsimp only
  intro contextExact foldExact workExact
  change Nonempty (ExactRestoredRootCleanK13PairTrialWitness transitionFuel
    configuration projection fixedInstance decoder (hidden, left) foldTrial
      finalTrial) at leftMember
  change Nonempty (ExactRestoredRootCleanK13PairTrialWitness transitionFuel
    configuration projection fixedInstance decoder (hidden, right) foldTrial
      finalTrial) at rightMember
  let leftWitness := Classical.choice leftMember
  let rightWitness := Classical.choice rightMember
  obtain ⟨wordsExact, gammaExact, finalExact, scheduleExact⟩ :=
    semantic foldTrial finalTrial hidden left right leftWitness rightWitness
      contextExact foldExact workExact
  have intrinsicExact :=
    exact_restored_root_k13_intrinsic_bad_congr_of_semantic_fields decoder
      leftWitness.joint.input rightWitness.joint.input
      leftWitness.joint.k12.words rightWitness.joint.k12.words wordsExact
        gammaExact finalExact scheduleExact
  have badExact : leftWitness.joint.bad = rightWitness.joint.bad := by
    rw [leftWitness.joint.badExact, rightWitness.joint.badExact]
    exact intrinsicExact
  have leftPointwise :
      exactRestoredRootCleanK13PairPointwiseBad transitionFuel configuration
        projection fixedInstance decoder foldTrial finalTrial (hidden, left) =
          leftWitness.joint.bad := by
    simpa [exactRestoredRootCleanK13PairPointwiseBad, leftMember, leftWitness]
  have rightPointwise :
      exactRestoredRootCleanK13PairPointwiseBad transitionFuel configuration
        projection fixedInstance decoder foldTrial finalTrial (hidden, right) =
          rightWitness.joint.bad := by
    simpa [exactRestoredRootCleanK13PairPointwiseBad, rightMember, rightWitness]
  exact leftPointwise.trans (badExact.trans rightPointwise.symm)

/-- Release-shaped probability consequence.  Its sole protocol-specific input
is now the deterministic semantic invariant above. -/
theorem exact_restored_clean_trial_union_probability_le_one_forest_of_semantic
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (frontierExact : ∀
      (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (schedule : QuerySchedule),
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions)
    (semantic : ExactRestoredRootCleanK13PairSemanticInvariant transitionFuel
      configuration projection fixedInstance decoder)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (foldExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 31)
    (finalExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 34) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
            projection fixedInstance ∩
          ⋃ finalTrial : ExactCompilerExposureTrial parameters,
            exactRestoredRootK13JointTrialEvent transitionFuel configuration
              projection fixedInstance decoder finalTrial) ≤
      q16SemanticOneForestRawError := by
  exact exact_restored_clean_trial_union_probability_le_one_forest hiddenLaw
    transitionRoom programmedCover frontierExact
      (exact_restored_clean_k13_pair_coordinate_invariant_of_semantic semantic)
      reference traceExists foldExposureCap finalExposureCap

#print axioms ExactRestoredRootCleanK13PairSemanticInvariant
#print axioms
  exact_restored_clean_pair_verifier_anchor_preserves_prover_runtime
#print axioms exact_restored_clean_pair_verifier_anchor_semantics_eq
#print axioms exact_restored_clean_k13_pair_coordinate_invariant_of_semantic
#print axioms
  exact_restored_clean_trial_union_probability_le_one_forest_of_semantic

end

end AspisK1.V7Tag73ExactRestoredCleanPairSemanticNoninterference
