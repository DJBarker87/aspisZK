import AspisFormal.K1.V7Tag73ExactCleanBidirectionalFoldPairPriorInvariant
import AspisFormal.K1.V7Tag73ExactRootCausalChain
import AspisFormal.K1.V7Tag73RootAbsorbInputInjectivity
import AspisFormal.K1.V7Tag73K13PreQ16TargetInventory

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
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRootCausalChain
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FutureFreeCheckedRefinementBisimulation
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73PureLookupDigestChain
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73K13PreQ16MerkleWordSource
open AspisK1.V7Tag73K13PreQ16TargetInventory
open AspisK1.V7Tag73RootAbsorbInputInjectivity
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7MerkleQueryExtractor
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

/-- Both public K1.2 roots have appeared in canonical absorb inputs before
either member of the selected fold-work/boundary pair.  This is the exact
root-membership premise needed by prefix-word suffix stability. -/
theorem exact_accepted_fold_anchor_k12_roots_mem
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input)
    (prior later : List UnifiedExposureRecord)
    (actor : QueryActor) (target : ShaInput) (answer : Digest256)
    (rootExact : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh actor target answer : UnifiedExposureRecord) ::
        later)
    (role :
      (target = selectedFoldWorkInput input fold ∧ answer = fold.answer) ∨
        (target = selectedFoldBoundaryInput input fold ∧
          answer = fold.boundaryAnswer)) :
    (exactK12Roots input).c1 ∈
        prefixMerkleCandidateSet (exposurePrefixRawQueries prior) ∧
      (exactK12Roots input).c2 ∈
        prefixMerkleCandidateSet (exposurePrefixRawQueries prior) := by
  obtain ⟨anchorLookup, terminalPrefix⟩ :=
    selected_fold_anchor_lookup_and_prefix input fold target answer role
  have c1Chain := exact_lookup_digest_chain_retained_before_anchor
    transitionRoom input prior later actor rootExact
      (pure_post_root_chain_to_exact fold.c1FoldChain) anchorLookup
      terminalPrefix
  have c2Chain := exact_lookup_digest_chain_retained_before_anchor
    transitionRoom input prior later actor rootExact
      (pure_post_root_chain_to_exact fold.c2FoldChain) anchorLookup
      terminalPrefix
  have messagesExact :
      fixedTapeRawMessages (exactOperationalTape input) =
        (exactK12Runtime input).adversaryValue.rawMessages :=
    input.package.root.fixedRoot.base.rawMessagesExact
  have c1Exact :
      (exactOperationalTape input).messages.c1Root =
        (exactK12Runtime input).adversaryValue.rawMessages.c1Root := by
    simpa [fixedTapeRawMessages, rawOfMessages] using
      congrArg (fun raw => raw.c1Root) messagesExact
  have c2Exact :
      (exactOperationalTape input).messages.c2.root =
        (exactK12Runtime input).adversaryValue.rawMessages.c2Root := by
    simpa [fixedTapeRawMessages, rawOfMessages] using
      congrArg (fun raw => raw.c2Root) messagesExact
  constructor
  · change runtimeDigest208ToMerkleDigest
      (exactK12Runtime input).adversaryValue.rawMessages.c1Root ∈
        prefixMerkleCandidateSet (exposurePrefixRawQueries prior)
    rw [← c1Exact]
    exact c1_root_mem_prefixMerkleCandidateSet_of_retained prior
      fold.c1BeforeDigest (exactOperationalTape input).messages.c1Root
      fold.c1Salt fold.c1Answer fold.digest
      (IsPostRootStateInput c1RootLabel) c1Chain
  · change runtimeDigest208ToMerkleDigest
      (exactK12Runtime input).adversaryValue.rawMessages.c2Root ∈
        prefixMerkleCandidateSet (exposurePrefixRawQueries prior)
    rw [← c2Exact]
    exact c2_root_mem_prefixMerkleCandidateSet_of_retained prior
      fold.c2BeforeDigest (exactOperationalTape input).messages.c2.root
      fold.c2Salt fold.c2Answer fold.digest
      (IsPostRootStateInput c2RootLabel) c2Chain

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

/-- The transcript-level root equality above is exactly the pair consumed by
the K1.2 Merkle extractor.  This bridge is purely a source-layout projection;
it neither hashes nor assumes injectivity of SHA-256. -/
theorem exact_k12_roots_eq_of_operational_roots_eq
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {leftSample rightSample : ExactCompilerSample HiddenTape parameters}
    (left : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance leftSample)
    (right : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance rightSample)
    (rootsExact :
      (exactOperationalTape left).messages.c1Root =
          (exactOperationalTape right).messages.c1Root ∧
        (exactOperationalTape left).messages.c2.root =
          (exactOperationalTape right).messages.c2.root) :
    exactK12Roots left = exactK12Roots right := by
  change Roots.mk
      (runtimeDigest208ToMerkleDigest
        (exactK12Runtime left).adversaryValue.rawMessages.c1Root)
      (runtimeDigest208ToMerkleDigest
        (exactK12Runtime left).adversaryValue.rawMessages.c2Root) =
    Roots.mk
      (runtimeDigest208ToMerkleDigest
        (exactK12Runtime right).adversaryValue.rawMessages.c1Root)
      (runtimeDigest208ToMerkleDigest
        (exactK12Runtime right).adversaryValue.rawMessages.c2Root)
  have leftRaw := left.package.root.fixedRoot.base.rawMessagesExact
  have rightRaw := right.package.root.fixedRoot.base.rawMessagesExact
  have leftC1 :
      (exactK12Runtime left).adversaryValue.rawMessages.c1Root =
        (exactOperationalTape left).messages.c1Root := by
    change left.package.root.fixedRoot.base.runtime.adversaryValue.rawMessages.c1Root =
      left.package.root.fixedRoot.base.tape.messages.c1Root
    rw [← leftRaw]
    rfl
  have rightC1 :
      (exactK12Runtime right).adversaryValue.rawMessages.c1Root =
        (exactOperationalTape right).messages.c1Root := by
    change right.package.root.fixedRoot.base.runtime.adversaryValue.rawMessages.c1Root =
      right.package.root.fixedRoot.base.tape.messages.c1Root
    rw [← rightRaw]
    rfl
  have leftC2 :
      (exactK12Runtime left).adversaryValue.rawMessages.c2Root =
        (exactOperationalTape left).messages.c2.root := by
    change left.package.root.fixedRoot.base.runtime.adversaryValue.rawMessages.c2Root =
      left.package.root.fixedRoot.base.tape.messages.c2.root
    rw [← leftRaw]
    rfl
  have rightC2 :
      (exactK12Runtime right).adversaryValue.rawMessages.c2Root =
        (exactOperationalTape right).messages.c2.root := by
    change right.package.root.fixedRoot.base.runtime.adversaryValue.rawMessages.c2Root =
      right.package.root.fixedRoot.base.tape.messages.c2.root
    rw [← rightRaw]
    rfl
  rw [leftC1, rightC1, leftC2, rightC2, rootsExact.1, rootsExact.2]

/-- Equal residual coordinates therefore fix the exact K1.2 root pair, ready
for the chronological-word argument. -/
theorem exact_clean_bidirectional_pair_k12_roots_eq
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
    exactK12Roots leftWitness.input = exactK12Roots rightWitness.input := by
  apply exact_k12_roots_eq_of_operational_roots_eq leftWitness.input
    rightWitness.input
  exact exact_clean_bidirectional_pair_roots_eq transitionRoom trial hidden left
    right leftWitness rightWitness programmedCover residualExact

#print axioms pure_post_root_chain_to_exact
#print axioms selected_fold_anchor_lookup_and_prefix
#print axioms exact_accepted_fold_anchor_k12_roots_mem
#print axioms exact_clean_bidirectional_pair_roots_eq
#print axioms exact_k12_roots_eq_of_operational_roots_eq
#print axioms exact_clean_bidirectional_pair_k12_roots_eq

end

end AspisK1.V7Tag73ExactCleanBidirectionalFoldRootInvariant
