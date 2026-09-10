import NestedCircleRouting
import AspisFormal.K1.V7Tag73SamplerDecoderExact

/-! Exact consumed-prefix locality for the literal ordinary decoder, the
first prerequisite for chronological nested-circle controller refinement.

The first three lemmas narrowly reuse V7 VariablePrefixGammaSampler at
26a9cd4718aae9f9de7ef1c3394fb74a229085d5; the unread-prefix lemma reuses
VariablePrefixGammaFlatRouting at the same pin. Their full import closures
are deliberately not imported. Only already-pinned decoder/control modules
are needed.

This leaf does not yet identify the full block-by-block controller with the
nested source run, and makes no mass, independence, or Fiat--Shamir claim.
In particular, nested consumption is not the final record's blocksUsed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.NestedCircleSourceRefinement
noncomputable section
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SamplerDecoderExact
open AspisK1.V7Tag73IncrementalSamplerControl
open AspisV8.NestedCircleRouting

theorem decodeLimbs_take_wordsUsed
    (count : Nat) (words : List Nat) (decoded : FourLimbDecode)
    (run : decodeLimbs count words = some decoded) :
    decodeLimbs count (words.take decoded.wordsUsed) =
      some { decoded with restWords := [] } := by
  induction count generalizing words decoded with
  | zero =>
      simp only [decodeLimbs, Option.some.injEq] at run
      subst decoded
      rfl
  | succ count ih =>
      cases firstRun : decodeLimb 8 words with
      | none => simp [decodeLimbs, firstRun] at run
      | some first =>
          cases tailRun : decodeLimbs count first.restWords with
          | none => simp [decodeLimbs, firstRun, tailRun] at run
          | some tail =>
              have decodedEq :
                  { limbs := first.value :: tail.limbs
                    restWords := tail.restWords
                    wordsUsed := first.attemptsUsed + tail.wordsUsed } =
                    decoded := by
                apply Option.some.inj
                simpa [decodeLimbs, firstRun, tailRun] using run
              subst decoded
              obtain ⟨rejected, accepted, rest, wordsEq, rejectedLt,
                  prefixRejected, acceptedCanonical, valueEq, restEq,
                  attemptsEq⟩ :=
                decodeLimb_success_first_accepted 8 words first firstRun
              have trimmedTail := ih first.restWords tail tailRun
              have restTakeEq :
                  first.restWords.take tail.wordsUsed =
                    rest.take tail.wordsUsed := by rw [restEq]
              have takeEq :
                  words.take (first.attemptsUsed + tail.wordsUsed) =
                    rejected ++ accepted :: rest.take tail.wordsUsed := by
                rw [wordsEq, attemptsEq]
                simp [List.take_add, Nat.add_assoc]
              let extraFuel := 8 - (rejected.length + 1)
              have fuelEq : rejected.length + 1 + extraFuel = 8 := by
                dsimp [extraFuel]
                omega
              have firstTrimmed := decodeLimb_of_first_accepted rejected
                accepted (rest.take tail.wordsUsed) extraFuel
                prefixRejected acceptedCanonical
              rw [fuelEq] at firstTrimmed
              rw [takeEq]
              simp [decodeLimbs, firstTrimmed]
              rw [← restTakeEq, trimmedTail]
              simp [valueEq, attemptsEq]

/-- Flattening fixed-size digest blocks commutes with taking a block prefix.
Each block contributes exactly eight chronological little-endian words. -/
theorem flattenedWords_take_blocks (blocks : List Digest256) (count : Nat) :
    flattenedWords (blocks.take count) =
      (flattenedWords blocks).take (8 * count) := by
  induction blocks generalizing count with
  | nil => simp [flattenedWords]
  | cons block rest ih =>
      cases count with
      | zero => simp [flattenedWords]
      | succ count =>
          simp only [List.take_succ_cons, flattenedWords, List.flatMap_cons]
          change blockWords block ++ flattenedWords (rest.take count) =
            (blockWords block ++ flattenedWords rest).take (8 * (count + 1))
          rw [ih]
          calc
            blockWords block ++ (flattenedWords rest).take (8 * count) =
                (blockWords block ++ flattenedWords rest).take
                  ((blockWords block).length + 8 * count) :=
              (List.take_length_add_append (l₁ := blockWords block)
                (l₂ := flattenedWords rest) (8 * count)).symm
            _ = (blockWords block ++ flattenedWords rest).take
                  (8 * (count + 1)) := by
              rw [blockWords_length]
              have arithmetic : 8 + 8 * count = 8 * (count + 1) := by
                omega
              rw [arithmetic]

/-- One ordinary attempt can be rerun on exactly its consumed block prefix.
Unused words in the final consumed block remain present, while every later
block is observationally irrelevant and removed. -/
theorem decodeOrdinaryPrefix_take_blocksUsed
    (blocks : List Digest256) (decoded : OrdinaryPrefixDecode)
    (run : decodeOrdinaryPrefix blocks = some decoded) :
    decodeOrdinaryPrefix (blocks.take decoded.blocksUsed) =
      some { decoded with remainingBlocks := [] } := by
  cases blocks with
  | nil => simp [decodeOrdinaryPrefix] at run
  | cons block rest =>
      cases limbsRun : decodeLimbs 4
          (flattenedWords (block :: rest)) with
      | none => simp [decodeOrdinaryPrefix, limbsRun] at run
      | some limbs =>
          by_cases valid :
              0 < blocksNeededForWords limbs.wordsUsed ∧
                blocksNeededForWords limbs.wordsUsed ≤ 4 ∧
                blocksNeededForWords limbs.wordsUsed ≤ (block :: rest).length
          · have decodedEq :
                { value := encodeQm31Limbs limbs.limbs
                  limbs := limbs.limbs
                  wordsUsed := limbs.wordsUsed
                  blocksUsed := blocksNeededForWords limbs.wordsUsed
                  remainingBlocks := (block :: rest).drop
                    (blocksNeededForWords limbs.wordsUsed) } = decoded := by
              have simplified := run
              simp [decodeOrdinaryPrefix, limbsRun, valid] at simplified
              exact simplified.2
            subst decoded
            let used := blocksNeededForWords limbs.wordsUsed
            let fullWords := flattenedWords (block :: rest)
            let consumedWords := flattenedWords ((block :: rest).take used)
            have wordsFit : limbs.wordsUsed ≤ 8 * used := by
              have division := Nat.div_add_mod (limbs.wordsUsed + 7) 8
              have remainder : (limbs.wordsUsed + 7) % 8 < 8 :=
                Nat.mod_lt _ (by norm_num)
              dsimp [used, blocksNeededForWords]
              omega
            have consumedWordLength : consumedWords.length = 8 * used := by
              dsimp [consumedWords]
              rw [flattenedWords_length, List.length_take_of_le valid.2.2]
            have consumedTake :
                consumedWords.take limbs.wordsUsed =
                  fullWords.take limbs.wordsUsed := by
              dsimp [consumedWords, fullWords]
              rw [flattenedWords_take_blocks, List.take_take]
              simp [Nat.min_eq_left wordsFit]
            have trimmed := decodeLimbs_take_wordsUsed 4 fullWords limbs
              limbsRun
            have extended := decodeLimbs_append_of_some 4
              (fullWords.take limbs.wordsUsed)
              (consumedWords.drop limbs.wordsUsed)
              { limbs with restWords := [] } trimmed
            have reconstructed :
                fullWords.take limbs.wordsUsed ++
                    consumedWords.drop limbs.wordsUsed = consumedWords := by
              rw [← consumedTake]
              exact List.take_append_drop limbs.wordsUsed consumedWords
            rw [reconstructed] at extended
            have consumedNonempty : (block :: rest).take used ≠ [] := by
              intro empty
              have lengthZero := congrArg List.length empty
              rw [List.length_take_of_le valid.2.2] at lengthZero
              dsimp [used] at lengthZero
              omega
            have consumedLength : ((block :: rest).take used).length = used :=
              List.length_take_of_le valid.2.2
            dsimp [consumedWords] at extended
            simp only [appendFourLimbRest, List.nil_append] at extended
            cases consumed : (block :: rest).take used with
            | nil => exact False.elim (consumedNonempty consumed)
            | cons head tail =>
                rw [consumed] at extended consumedLength
                simp [decodeOrdinaryPrefix, extended, consumedLength,
                  used, valid]
          · simp [decodeOrdinaryPrefix, limbsRun] at run
            exact False.elim (valid run.1)


/-- Replace only unread whole blocks. The source fixes every returned
stopping field before those blocks are examined. -/
theorem decodeOrdinaryPrefix_of_matching_consumed_prefix
    (source target : List Digest256) (decoded : OrdinaryPrefixDecode)
    (run : decodeOrdinaryPrefix source = some decoded)
    (prefixEq : target.take decoded.blocksUsed =
      source.take decoded.blocksUsed) :
    decodeOrdinaryPrefix target =
      some { decoded with remainingBlocks := target.drop decoded.blocksUsed } := by
  have trimmed := decodeOrdinaryPrefix_take_blocksUsed source decoded run
  have extended := decodeOrdinaryPrefix_append_of_some
    (source.take decoded.blocksUsed) (target.drop decoded.blocksUsed)
    { decoded with remainingBlocks := [] } trimmed
  have targetSplit : target.take decoded.blocksUsed ++
      target.drop decoded.blocksUsed = target :=
    List.take_append_drop decoded.blocksUsed target
  rw [← prefixEq] at extended
  rw [← targetSplit]
  simpa [appendOrdinaryRemaining] using extended

/-- The consumed block cut is the first possible successful block cut.
This is derived from source extension stability and its returned bound, not
assumed from an expected trace. Option-none here deliberately does not yet
classify short input versus the controller's hard failure. -/
theorem ordinary_strict_prefix_none (blocks : List Digest256)
    (decoded : OrdinaryPrefixDecode)
    (run : decodeOrdinaryPrefix blocks = some decoded)
    (count : Nat) (short : count < decoded.blocksUsed) :
    decodeOrdinaryPrefix (blocks.take count) = none := by
  cases earlyRun : decodeOrdinaryPrefix (blocks.take count) with
  | none => rfl
  | some early =>
      have extended := decodeOrdinaryPrefix_append_of_some
        (blocks.take count) (blocks.drop count) early earlyRun
      rw [List.take_append_drop] at extended
      have same : appendOrdinaryRemaining early (blocks.drop count) = decoded :=
        Option.some.inj (extended.symm.trans run)
      have earlyBounds := ordinary_source_tail (blocks.take count) early earlyRun
      have countBound : early.blocksUsed ≤ count := by
        have takeBound : (blocks.take count).length ≤ count := by simp
        exact earlyBounds.2.2.1.trans takeBound
      have usedProjection := congrArg OrdinaryPrefixDecode.blocksUsed same
      have usedEq : early.blocksUsed = decoded.blocksUsed := by
        simpa only [appendOrdinaryRemaining] using usedProjection
      omega

/-- A source-supplied successful call gives a literal first-hit cut, with
all later blocks returned unchanged and no extra whole block consumed. -/
theorem ordinary_first_hit_cut (blocks : List Digest256)
    (decoded : OrdinaryPrefixDecode)
    (run : decodeOrdinaryPrefix blocks = some decoded) :
    0 < decoded.blocksUsed ∧ decoded.blocksUsed ≤ 4 ∧
    blocks = blocks.take decoded.blocksUsed ++ decoded.remainingBlocks ∧
    decodeOrdinaryPrefix (blocks.take decoded.blocksUsed) =
      some { decoded with remainingBlocks := [] } ∧
    ∀ count < decoded.blocksUsed,
      decodeOrdinaryPrefix (blocks.take count) = none := by
  obtain ⟨positive, cap, available, tail⟩ :=
    ordinary_source_tail blocks decoded run
  refine ⟨positive, cap, ?_, decodeOrdinaryPrefix_take_blocksUsed blocks decoded run,
    fun count short => ordinary_strict_prefix_none blocks decoded run count short⟩
  rw [tail, List.take_append_drop]

#print axioms decodeLimbs_take_wordsUsed
#print axioms flattenedWords_take_blocks
#print axioms decodeOrdinaryPrefix_take_blocksUsed
#print axioms decodeOrdinaryPrefix_of_matching_consumed_prefix
#print axioms ordinary_strict_prefix_none
#print axioms ordinary_first_hit_cut
end
end AspisV8.NestedCircleSourceRefinement
