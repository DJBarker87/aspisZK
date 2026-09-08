import AspisFormal.K1.V7Tag73ExactCleanBidirectionalFoldPairPriorInvariant
import AspisFormal.K1.V7Tag73ExactRootCausalChain
import AspisFormal.K1.V7Tag73RootAbsorbInputInjectivity

/-!
# Clean bidirectional fold-root invariant

The accepted fold package now retains fuel-free C1/C2 lookup chains ending at
the selected fold digest.  This module moves those chains into the common
pre-anchor first-creation prefix and reverses them across two one-fold fibres.
The argument uses answer uniqueness and literal SHA-input prefixes, never
SHA-256 injectivity.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCleanBidirectionalFoldRootInvariant

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73BidirectionalFoldOneFoldCoordinates
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactBidirectionalFoldAnchor
open AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldTrialEvent
open AspisK1.V7Tag73ExactCleanBidirectionalFoldPairPriorInvariant
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRootCausalChain
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73PureLookupDigestChain
open AspisK1.V7Tag73RootAbsorbInputInjectivity
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Forgetting the fuel-free wrapper recovers the chronology-ready lookup
chain with the identical literal coordinates. -/
theorem pure_post_root_chain_to_exact
    {table : FixedOracleTable} {forbiddenLabel : UInt8}
    {boundaryInput : ShaInput} {initial terminal : Digest256}
    (chain : PureLookupDigestChain table boundaryInput
      (IsPurePostRootStateInput forbiddenLabel) initial terminal) :
    ExactLookupDigestChain table boundaryInput
      (IsPostRootStateInput forbiddenLabel) initial terminal := by
  induction chain with
  | boundary lookup => exact .boundary initial lookup
  | step current next input previous causalPrefix allowed lookup ih =>
      exact .step initial current next input ih
        (by simpa [HasLiteralStatePrefix] using causalPrefix)
        (by simpa [IsPurePostRootStateInput, IsPostRootStateInput] using allowed)
        lookup

/-- The strongly typed fold-pair role supplies both the selected lookup and
the literal dependence on the fold digest. -/
theorem selected_fold_anchor_lookup_and_prefix
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input)
    (target : ShaInput) (answer : Digest256)
    (role :
      (target = selectedFoldWorkInput input fold ∧ answer = fold.answer) ∨
        (target = selectedFoldBoundaryInput input fold ∧
          answer = fold.boundaryAnswer)) :
    tableLookup (exactOperationalTable input) target = some answer ∧
      HasLiteralStatePrefix fold.digest target := by
  rcases role with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨by simpa [selectedFoldWorkInput] using fold.workLookup,
      by simp [HasLiteralStatePrefix, selectedFoldWorkInput, bytes_length]⟩
  · exact ⟨by simpa [selectedFoldBoundaryInput] using fold.boundaryLookup,
      by simp [HasLiteralStatePrefix, selectedFoldBoundaryInput, bytes_length]⟩

/-- Equal residual coordinates fix both authenticated Merkle roots before the
one-fold variation. -/
theorem exact_clean_bidirectional_pair_roots_eq
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (trial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactCleanBidirectionalK13OneFoldTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) trial)
    (rightWitness : ExactCleanBidirectionalK13OneFoldTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) trial)
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap)
    (residualExact :
      let router := exactCompilerBidirectionalFoldOneFoldRouter parameters
        transitionFuel trial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
          left).1 =
        (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
          right).1) :
    (exactOperationalTape leftWitness.input).messages.c1Root =
        (exactOperationalTape rightWitness.input).messages.c1Root ∧
      (exactOperationalTape leftWitness.input).messages.c2.root =
        (exactOperationalTape rightWitness.input).messages.c2.root := by
  obtain ⟨leftPrior, leftLater, rightPrior, rightLater, leftActor, rightActor,
      leftTarget, rightTarget, leftAnswer, rightAnswer, leftRootExact,
      rightRootExact, _leftTrialExact, _rightTrialExact, leftRole, rightRole,
      priorExact⟩ :=
    exact_clean_bidirectional_pair_anchor_priors_eq trial hidden left right
      leftWitness rightWitness programmedCover residualExact
  subst rightPrior
  have foldDigestExact : leftWitness.fold.digest = rightWitness.fold.digest :=
    exact_clean_bidirectional_pair_anchor_fold_digest_eq trial hidden left right
      leftWitness rightWitness programmedCover residualExact
  obtain ⟨leftAnchorLookup, leftTerminalPrefix⟩ :=
    selected_fold_anchor_lookup_and_prefix leftWitness.input leftWitness.fold
      leftTarget leftAnswer leftRole
  obtain ⟨rightAnchorLookup, rightTerminalPrefix⟩ :=
    selected_fold_anchor_lookup_and_prefix rightWitness.input rightWitness.fold
      rightTarget rightAnswer rightRole
  have leftC1LookupChain :=
    pure_post_root_chain_to_exact leftWitness.fold.c1FoldChain
  have leftC2LookupChain :=
    pure_post_root_chain_to_exact leftWitness.fold.c2FoldChain
  have rightC1LookupChain :=
    pure_post_root_chain_to_exact rightWitness.fold.c1FoldChain
  have rightC2LookupChain :=
    pure_post_root_chain_to_exact rightWitness.fold.c2FoldChain
  have leftC1Chain := exact_lookup_digest_chain_retained_before_anchor
    transitionRoom leftWitness.input leftPrior leftLater leftActor leftRootExact
    leftC1LookupChain leftAnchorLookup leftTerminalPrefix
  have leftC2Chain := exact_lookup_digest_chain_retained_before_anchor
    transitionRoom leftWitness.input leftPrior leftLater leftActor leftRootExact
    leftC2LookupChain leftAnchorLookup leftTerminalPrefix
  have rightC1Chain := exact_lookup_digest_chain_retained_before_anchor
    transitionRoom rightWitness.input leftPrior rightLater rightActor
    rightRootExact rightC1LookupChain rightAnchorLookup rightTerminalPrefix
  have rightC2Chain := exact_lookup_digest_chain_retained_before_anchor
    transitionRoom rightWitness.input leftPrior rightLater rightActor
    rightRootExact rightC2LookupChain rightAnchorLookup rightTerminalPrefix
  rw [← foldDigestExact] at rightC1Chain rightC2Chain
  have priorAnswersNodup :
      (leftPrior.map UnifiedExposureRecord.answer).Nodup := by
    have fullNodup := exact_root_record_answers_nodup leftWitness.input
    rw [leftRootExact, List.map_append, List.map_cons] at fullNodup
    exact (List.nodup_append.mp fullNodup).1
  have leftC1DataNonempty :
      (AspisK1.V7Tag73TranscriptSchedule.Payload.c1Root
        (exactOperationalTape leftWitness.input).messages.c1Root
          leftWitness.fold.c1Salt).data ≠ [] := by
    intro empty
    have lengths := congrArg List.length empty
    simp [AspisK1.V7Tag73TranscriptSchedule.Payload.data] at lengths
  have rightC1DataNonempty :
      (AspisK1.V7Tag73TranscriptSchedule.Payload.c1Root
        (exactOperationalTape rightWitness.input).messages.c1Root
          rightWitness.fold.c1Salt).data ≠ [] := by
    intro empty
    have lengths := congrArg List.length empty
    simp [AspisK1.V7Tag73TranscriptSchedule.Payload.data] at lengths
  have c1InputExact := exact_retained_digest_chains_boundary_input_eq
    priorAnswersNodup leftC1Chain rightC1Chain
    (absorb_input_avoids_post_root_state_input c1RootLabel
      leftWitness.fold.c1BeforeDigest _ leftC1DataNonempty)
    (absorb_input_avoids_post_root_state_input c1RootLabel
      rightWitness.fold.c1BeforeDigest _ rightC1DataNonempty)
  have c2InputExact := exact_retained_digest_chains_boundary_input_eq
    priorAnswersNodup leftC2Chain rightC2Chain
    (c2_absorb_input_avoids_post_c2_state_input
      leftWitness.fold.c2BeforeDigest leftWitness.fold.c2Salt
      (exactOperationalTape leftWitness.input).messages.c2.root)
    (c2_absorb_input_avoids_post_c2_state_input
      rightWitness.fold.c2BeforeDigest rightWitness.fold.c2Salt
      (exactOperationalTape rightWitness.input).messages.c2.root)
  exact ⟨c1_root_eq_of_absorb_input_eq leftWitness.fold.c1BeforeDigest
      rightWitness.fold.c1BeforeDigest
      (exactOperationalTape leftWitness.input).messages.c1Root
      (exactOperationalTape rightWitness.input).messages.c1Root
      leftWitness.fold.c1Salt rightWitness.fold.c1Salt c1InputExact,
    c2_root_eq_of_absorb_input_eq leftWitness.fold.c2BeforeDigest
      rightWitness.fold.c2BeforeDigest
      (exactOperationalTape leftWitness.input).messages.c2.root
      (exactOperationalTape rightWitness.input).messages.c2.root
      leftWitness.fold.c2Salt rightWitness.fold.c2Salt c2InputExact⟩

#print axioms pure_post_root_chain_to_exact
#print axioms selected_fold_anchor_lookup_and_prefix
#print axioms exact_clean_bidirectional_pair_roots_eq

end

end AspisK1.V7Tag73ExactCleanBidirectionalFoldRootInvariant
