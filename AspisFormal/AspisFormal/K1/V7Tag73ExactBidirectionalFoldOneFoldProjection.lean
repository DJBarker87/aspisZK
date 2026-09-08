import AspisFormal.K1.V7Tag73CausalFoldOneFoldTapeBridge
import AspisFormal.K1.V7Tag73ExactBidirectionalFoldAlphaRouting
import AspisFormal.K1.V7Tag73ExactPairAlphaValueClosure
import AspisFormal.K1.V7Tag73OperationalSemanticReplay
import AspisFormal.K1.V7Tag73VariablePrefixGammaFlatRouting

/-!
# Exact accepted source projected into five one-fold coordinates

The bidirectional router and the probability equivalence now share one tape
cast.  This leaf therefore transports the literal accepted fold-work answer
and every consumed alpha-zero output into the exact five-coordinate product
used by the causal probability theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactBidirectionalFoldOneFoldProjection

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73BidirectionalFoldOneFoldCoordinates
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73CausalFoldOneFoldTapeBridge
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactBidirectionalFoldAlphaRouting
open AspisK1.V7Tag73ExactBidirectionalFoldAnchor
open AspisK1.V7Tag73ExactBidirectionalFoldRootRouting
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactPairAlphaValueClosure
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73IncrementalSamplerControl
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- A successful ordinary-prefix parse can consume no more blocks than were
supplied. This small control-flow fact is kept local to avoid re-elaborating
the larger decoder bridge. -/
theorem decoded_ordinary_prefix_blocksUsed_le_length
    (blocks : List Digest256) (decoded : OrdinaryPrefixDecode)
    (run : decodeOrdinaryPrefix blocks = some decoded) :
    decoded.blocksUsed ≤ blocks.length := by
  cases blocks with
  | nil => simp [decodeOrdinaryPrefix] at run
  | cons block rest =>
      cases limbsRun : decodeLimbs 4 (flattenedWords (block :: rest)) with
      | none => simp [decodeOrdinaryPrefix, limbsRun] at run
      | some limbs =>
          by_cases valid :
              0 < blocksNeededForWords limbs.wordsUsed ∧
                blocksNeededForWords limbs.wordsUsed ≤ 4 ∧
                blocksNeededForWords limbs.wordsUsed ≤ (block :: rest).length
          · simp [decodeOrdinaryPrefix, limbsRun, valid] at run
            rcases run with ⟨_, decodedEq⟩
            subst decoded
            exact valid.2.2
          · simp [decodeOrdinaryPrefix, limbsRun] at run
            exact False.elim (valid run.1)

/-- The selected accepted fold-work digest is exactly the first component of
the five-coordinate probability tuple. -/
theorem exact_accepted_fold_work_is_probability_coordinate
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input) :
    let trial := exactAcceptedFoldPairTrial input fold
    (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters
      (exactCompilerBidirectionalFoldOneFoldRouter parameters transitionFuel
        trial.val (exactPlainRomCursor configuration sample.1).erase)
      sample.2).2.1 = fold.answer := by
  let trial := exactAcceptedFoldPairTrial input fold
  let router := exactCompilerBidirectionalFoldOneFoldRouter parameters
    transitionFuel trial.val (exactPlainRomCursor configuration sample.1).erase
  dsimp only
  have routed := exact_accepted_fold_work_is_bidirectionally_routed
    programmedCover input fold
  have named := coordinate_eq_of_causalRoutedAnswer?_eq_some router
    (bidirectionalFoldNamedSlotInputTape parameters sample.2) none
    (Finset.mem_univ none) fold.answer (by simpa [router, trial] using routed)
  rw [bidirectional_fold_coordinate_eq_named_slot]
  simpa [router, trial] using named

/-- Every alpha block actually consumed by the deployed bounded decoder is
the corresponding named component of the probability tuple. -/
theorem exact_accepted_fold_alpha_output_is_probability_coordinate
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input)
    (index : Nat) (inOutputs : index < fold.alphaOutputs.length) :
    let trial := exactAcceptedFoldPairTrial input fold
    let coordinates :=
      exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters
        (exactCompilerBidirectionalFoldOneFoldRouter parameters transitionFuel
          trial.val (exactPlainRomCursor configuration sample.1).erase)
        sample.2
    ∃ block : Fin 4, block.val = index ∧
      coordinates.2.2 block = fold.alphaOutputs[index] := by
  let trial := exactAcceptedFoldPairTrial input fold
  let router := exactCompilerBidirectionalFoldOneFoldRouter parameters
    transitionFuel trial.val (exactPlainRomCursor configuration sample.1).erase
  obtain ⟨block, blockExact, routed⟩ :=
    exact_accepted_fold_alpha_outputs_are_bidirectionally_routed
      transitionRoom programmedCover input fold index inOutputs
  have named := coordinate_eq_of_causalRoutedAnswer?_eq_some router
    (bidirectionalFoldNamedSlotInputTape parameters sample.2) (some block)
    (Finset.mem_univ (some block)) fold.alphaOutputs[index]
    (by simpa [router, trial] using routed)
  refine ⟨block, blockExact, ?_⟩
  rw [bidirectional_alpha_coordinate_eq_named_slot]
  simpa [router, trial] using named

/-- The deployed decoder run extends from its actually consumed accepted
prefix to the full four named probability coordinates.  The returned value
bytes are unchanged; only the unread suffix is replaced. -/
theorem exact_accepted_fold_probability_coordinate_alpha_full_decode
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input) :
    let trial := exactAcceptedFoldPairTrial input fold
    let coordinates :=
      exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters
        (exactCompilerBidirectionalFoldOneFoldRouter parameters transitionFuel
          trial.val (exactPlainRomCursor configuration sample.1).erase)
        sample.2
    ∃ decoded : OrdinaryPrefixDecode,
      decodeOrdinaryPrefix (List.ofFn coordinates.2.2) = some decoded ∧
        decoded.value =
          (exactOperationalTape input).messages.challengeValue (.alpha 0) := by
  let trial := exactAcceptedFoldPairTrial input fold
  let coordinates :=
    exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters
      (exactCompilerBidirectionalFoldOneFoldRouter parameters transitionFuel
        trial.val (exactPlainRomCursor configuration sample.1).erase)
      sample.2
  dsimp only
  have ordinaryExact : decodeOrdinaryExact fold.alphaOutputs =
      some ((exactOperationalTape input).messages.challengeValue (.alpha 0)) := by
    simpa [decodeChallengeParameter, samplerMode] using fold.alphaAccepted
  obtain ⟨decoded, decodedRun, noRemaining, decodedValue⟩ :=
    decodeOrdinaryExact_witness fold.alphaOutputs
      ((exactOperationalTape input).messages.challengeValue (.alpha 0))
      ordinaryExact
  have usedLe : decoded.blocksUsed ≤ fold.alphaOutputs.length :=
    decoded_ordinary_prefix_blocksUsed_le_length fold.alphaOutputs decoded
      decodedRun
  have sourceLeUsed : fold.alphaOutputs.length ≤ decoded.blocksUsed := by
    have remainingDrop := decodeOrdinaryPrefix_remaining_eq_drop
      fold.alphaOutputs decoded decodedRun
    rw [noRemaining] at remainingDrop
    have lengths := congrArg List.length remainingDrop
    simp only [List.length_nil, List.length_drop] at lengths
    omega
  have lengthExact : decoded.blocksUsed = fold.alphaOutputs.length :=
    Nat.le_antisymm usedLe sourceLeUsed
  have within : fold.alphaOutputs.length ≤ 4 := by
    rw [fold.alphaOutputsLength]
    simpa [samplerMode, samplerBlockCap] using
      ((exactOperationalTape input).messages.challengeUse
        (.alpha 0)).withinDeployedCap
  have everySlot : ∀ (block : Fin 4)
      (consumed : block.val < fold.alphaOutputs.length),
      coordinates.2.2 block = fold.alphaOutputs[block.val]'consumed := by
    intro block consumed
    obtain ⟨routedBlock, routedValue, coordinateExact⟩ :=
      exact_accepted_fold_alpha_output_is_probability_coordinate
        transitionRoom programmedCover input fold block.val consumed
    have blockExact : routedBlock = block := Fin.ext routedValue
    cases blockExact
    exact coordinateExact
  have consumedPrefix := alpha_blocks_eq_full_tape_take_of_every_slot
    coordinates.2.2 fold.alphaOutputs within everySlot
  have targetLong : decoded.blocksUsed ≤
      (List.ofFn coordinates.2.2).length := by
    simp only [List.length_ofFn]
    omega
  have prefixExact :
      (List.ofFn coordinates.2.2).take decoded.blocksUsed =
        fold.alphaOutputs.take decoded.blocksUsed := by
    calc
      (List.ofFn coordinates.2.2).take decoded.blocksUsed =
          (List.ofFn coordinates.2.2).take fold.alphaOutputs.length := by
            rw [lengthExact]
      _ = fold.alphaOutputs := consumedPrefix.symm
      _ = fold.alphaOutputs.take decoded.blocksUsed := by
            rw [lengthExact]
            exact List.take_length.symm
  have fullRun := decodeOrdinaryPrefix_of_matching_consumed_prefix
    fold.alphaOutputs (List.ofFn coordinates.2.2) decoded decodedRun targetLong
    prefixExact
  exact ⟨{ decoded with remainingBlocks :=
    (List.ofFn coordinates.2.2).drop decoded.blocksUsed }, fullRun, decodedValue⟩

/-- The full four-block alpha component selected by the probability
equivalence is in the successful bounded-sampler subtype. Only the consumed
prefix is constrained by the accepted execution; unread named coordinates
remain arbitrary, exactly as required by the conditioning argument. -/
theorem exact_accepted_fold_probability_coordinate_alpha_succeeds
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input) :
    let trial := exactAcceptedFoldPairTrial input fold
    let coordinates :=
      exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters
        (exactCompilerBidirectionalFoldOneFoldRouter parameters transitionFuel
          trial.val (exactPlainRomCursor configuration sample.1).erase)
        sample.2
    foldAlphaTotalSucceeds coordinates.2 := by
  let trial := exactAcceptedFoldPairTrial input fold
  let coordinates :=
    exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters
      (exactCompilerBidirectionalFoldOneFoldRouter parameters transitionFuel
        trial.val (exactPlainRomCursor configuration sample.1).erase)
      sample.2
  dsimp only
  obtain ⟨decoded, fullRun, _valueExact⟩ :=
    exact_accepted_fold_probability_coordinate_alpha_full_decode
      transitionRoom programmedCover input fold
  unfold foldAlphaTotalSucceeds
  apply (fourGammaBlocksRawEquiv_success_iff coordinates.2.2).mp
  rw [fullRun]
  rfl

/-- The successful raw alpha coordinate returns the exact mathematical value
decoded by the deployed accepted transcript. -/
theorem exact_accepted_fold_probability_coordinate_alpha_value
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input) :
    let trial := exactAcceptedFoldPairTrial input fold
    let coordinates :=
      exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters
        (exactCompilerBidirectionalFoldOneFoldRouter parameters transitionFuel
          trial.val (exactPlainRomCursor configuration sample.1).erase)
        sample.2
    let succeeds : foldAlphaTotalSucceeds coordinates.2 :=
      exact_accepted_fold_probability_coordinate_alpha_succeeds
        transitionRoom programmedCover input fold
    successfulOrdinaryExactValue
        ⟨fourGammaBlocksRawEquiv coordinates.2.2, succeeds⟩ =
      exactOperationalChallenge input (.alpha 0) := by
  let trial := exactAcceptedFoldPairTrial input fold
  let coordinates :=
    exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters
      (exactCompilerBidirectionalFoldOneFoldRouter parameters transitionFuel
        trial.val (exactPlainRomCursor configuration sample.1).erase)
      sample.2
  let succeeds : foldAlphaTotalSucceeds coordinates.2 :=
    exact_accepted_fold_probability_coordinate_alpha_succeeds
      transitionRoom programmedCover input fold
  let raw : SuccessfulTag73RawStream :=
    ⟨fourGammaBlocksRawEquiv coordinates.2.2, succeeds⟩
  dsimp only
  obtain ⟨decoded, fullRun, decodedValue⟩ :=
    exact_accepted_fold_probability_coordinate_alpha_full_decode
      transitionRoom programmedCover input fold
  have canonical := successfulRawOrdinaryDecode_of_run coordinates.2.2 decoded
    fullRun
  have rawExact : raw =
      successfulRawOfOrdinaryRun coordinates.2.2 decoded fullRun := by
    apply Subtype.ext
    rfl
  have encoded : encodeTagQM31ExactLE (successfulOrdinaryExactValue raw) =
      (exactOperationalTape input).messages.challengeValue (.alpha 0) := by
    calc
      encodeTagQM31ExactLE (successfulOrdinaryExactValue raw) =
          (successfulRawOrdinaryDecode raw).value :=
        (successfulRawOrdinaryDecode_value_eq_exact_encoding raw).symm
      _ = decoded.value := by
        rw [rawExact]
        exact congrArg OrdinaryPrefixDecode.value canonical
      _ = _ := decodedValue
  have decodedRaw :
      decodeTagQM31ExactLE
          ((exactOperationalTape input).messages.challengeValue (.alpha 0)) =
        some (successfulOrdinaryExactValue raw) := by
    rw [← encoded]
    exact decodeTagQM31ExactLE_encodeTagQM31ExactLE _
  have valueExact : successfulOrdinaryExactValue raw = fold.alphaExactValue :=
    Option.some.inj (decodedRaw.symm.trans fold.alphaExactDecode)
  calc
    successfulOrdinaryExactValue raw = fold.alphaExactValue := valueExact
    _ = exactOperationalChallenge input (.alpha 0) := by
      simpa [exactOperationalChallenge] using fold.alphaOperational.symm

#print axioms exact_accepted_fold_work_is_probability_coordinate
#print axioms exact_accepted_fold_alpha_output_is_probability_coordinate
#print axioms exact_accepted_fold_probability_coordinate_alpha_full_decode
#print axioms exact_accepted_fold_probability_coordinate_alpha_succeeds
#print axioms exact_accepted_fold_probability_coordinate_alpha_value

end
end AspisK1.V7Tag73ExactBidirectionalFoldOneFoldProjection
