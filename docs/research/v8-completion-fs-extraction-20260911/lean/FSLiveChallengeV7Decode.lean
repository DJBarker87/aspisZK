import FSLiveChallengeTrace
import FSV7FourBlockWordBridge

/-!
# Successful live challenge trace decodes through the V7 ordinary decoder

This leaf identifies the words actually consumed by the live, lazy
`FSBoundedTranscript.challenge` with the V7 bounded-retry decoder content.
It is deterministic: no freshness, independence, or probability premise is
introduced.  The total trace/erasure theorems in `FSLiveChallengeTrace`
continue to cover failure and early stopping.
-/

set_option autoImplicit false

namespace AspisV8Completion.FSLiveChallengeV7Decode

open AspisV8Completion.FSLiveChallengeTrace
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73IncrementalSamplerControl

abbrev Tape := AspisV8Completion.FSBoundedTranscript.Tape

def drawDelta (before after : TraceStream) : List Nat :=
  after.drawn.drop before.drawn.length

theorem drawDelta_next_cons (tape : Tape) (s after : TraceStream)
    (pref : (nextWord tape s).2.drawn <+: after.drawn) :
    drawDelta s after =
      (nextWord tape s).1 :: drawDelta (nextWord tape s).2 after := by
  rcases pref with ⟨suffix, hsuffix⟩
  simp only [drawDelta]
  rw [← hsuffix, nextWord_drawn]
  simp [List.append_assoc]

theorem drawDelta_trans (before middle after : TraceStream)
    (first : before.drawn <+: middle.drawn)
    (second : middle.drawn <+: after.drawn) :
    drawDelta before after =
      drawDelta before middle ++ drawDelta middle after := by
  rcases first with ⟨left, hleft⟩
  rcases second with ⟨right, hright⟩
  simp only [drawDelta]
  rw [← hright, ← hleft]
  simp [List.append_assoc]

/-- A successful traced limb is exactly the V7 decoder on the words consumed
by that limb.  The unread suffix is empty because `drawDelta` is the exact
consumed slice, and the attempt count is the live draw-counter difference. -/
theorem decodeLimb_drawDelta (tape : Tape) : ∀ fuel s value,
    Canonical s →
    (limb tape fuel s).1 = some value →
      decodeLimb fuel (drawDelta s (limb tape fuel s).2) =
        some { value := value
               restWords := []
               attemptsUsed := (limb tape fuel s).2.draws - s.draws } := by
  intro fuel
  induction fuel with
  | zero =>
      intro s value canonical success
      simp [limb] at success
  | succ fuel ih =>
      intro s value canonical success
      simp only [limb] at success ⊢
      by_cases rejected : (nextWord tape s).1 = 2147483647
      · rw [if_pos rejected] at success ⊢
        have tail := ih (nextWord tape s).2 value
          (nextWord_canonical tape s canonical) success
        have pref := limb_drawn_prefix tape fuel (nextWord tape s).2
        rw [drawDelta_next_cons tape s _ pref]
        simp only [decodeLimb]
        have maskedRejected : maskedM31 (nextWord tape s).1 = m31Prime := by
          rw [rejected]
          decide
        rw [maskedRejected, if_pos]
        rw [tail]
        have mono := limb_draws_mono tape fuel (nextWord tape s).2
        have stepDraws := nextWord_draws tape s
        have attemptsEq :
            (limb tape fuel (nextWord tape s).2).2.draws -
                (nextWord tape s).2.draws + 1 =
              (limb tape fuel (nextWord tape s).2).2.draws - s.draws := by
          omega
        simp [attemptsEq]
        rfl
      · rw [if_neg rejected] at success ⊢
        cases success
        have pref : (nextWord tape s).2.drawn <+:
            (nextWord tape s).2.drawn := List.prefix_refl _
        rw [drawDelta_next_cons tape s _ pref]
        have canonicalValue : maskedM31 (nextWord tape s).1 =
            (nextWord tape s).1 := by
          exact Nat.mod_eq_of_lt (nextWord_value_lt tape s canonical)
        have notPrime : (nextWord tape s).1 ≠ m31Prime := by
          simpa [m31Prime] using rejected
        simp [drawDelta, decodeLimb, canonicalValue, notPrime,
          nextWord_draws]

/-- Four successful traced limbs are exactly the V7 sequential decoder on
their consumed word slice, including the live order and draw count. -/
theorem decodeLimbs_drawDelta (tape : Tape) : ∀ count s values,
    Canonical s →
    (limbs tape count s).1 = some values →
      decodeLimbs count (drawDelta s (limbs tape count s).2) =
        some { limbs := values
               restWords := []
               wordsUsed := (limbs tape count s).2.draws - s.draws } := by
  intro count
  induction count with
  | zero =>
      intro s values canonical success
      simp only [limbs, Option.some.injEq] at success
      subst values
      change decodeLimbs 0 (s.drawn.drop s.drawn.length) =
        some (FourLimbDecode.mk [] [] (s.draws - s.draws))
      simp [decodeLimbs]
  | succ count ih =>
      intro s values canonical success
      simp only [limbs] at success ⊢
      cases firstResult : (limb tape 8 s).1 with
      | none => simp [firstResult] at success
      | some firstValue =>
          cases tailResult : (limbs tape count (limb tape 8 s).2).1 with
          | none => simp [firstResult, tailResult] at success
          | some tailValues =>
              simp [firstResult, tailResult] at success
              subst values
              let middle := (limb tape 8 s).2
              let after := (limbs tape count middle).2
              have firstDecoded := decodeLimb_drawDelta tape 8 s firstValue
                canonical firstResult
              have tailDecoded := ih middle tailValues
                (limb_canonical tape 8 s canonical) (by simpa [middle] using tailResult)
              have firstPrefix := limb_drawn_prefix tape 8 s
              have secondPrefix := limbs_drawn_prefix tape count middle
              have delta := drawDelta_trans s middle after firstPrefix secondPrefix
              change decodeLimbs (count + 1) (drawDelta s after) = _
              rw [delta]
              have firstExtended := decodeLimb_append_of_some 8
                (drawDelta s middle) (drawDelta middle after)
                { value := firstValue
                  restWords := []
                  attemptsUsed := middle.draws - s.draws } firstDecoded
              simp only [appendLimbRest, List.nil_append] at firstExtended
              simp only [decodeLimbs, firstExtended]
              change decodeLimbs count (drawDelta middle after) =
                some { limbs := tailValues
                       restWords := []
                       wordsUsed := after.draws - middle.draws } at tailDecoded
              change Option.bind (decodeLimbs count (drawDelta middle after))
                (fun rest => some (FourLimbDecode.mk
                  (firstValue :: rest.limbs) rest.restWords
                  (middle.draws - s.draws + rest.wordsUsed))) = _
              rw [tailDecoded]
              have sToMiddle : s.draws ≤ middle.draws := by
                simpa [middle] using limb_draws_mono tape 8 s
              have middleToAfter : middle.draws ≤ after.draws := by
                simpa [after] using limbs_draws_mono tape count middle
              have drawsEq :
                  middle.draws - s.draws + (after.draws - middle.draws) =
                    after.draws - s.draws := by omega
              simp [drawsEq]
              change after.draws - s.draws = after.draws - s.draws
              rfl

/-- On a successful live challenge, the V7 decoder consumes exactly the
recorded lazy blocks, returns the identical four limbs, counts the identical
word draws, and retains precisely the unread words of the final block. -/
theorem challenge_decodeLimbs (tape : Tape)
    (start : AspisV8Completion.FSBoundedTranscript.Transcript)
    (values : List Nat)
    (success : (challenge tape start).result = some values) :
    decodeLimbs 4 ((challenge tape start).blocks.flatMap
        AspisV8Completion.FSBoundedTranscript.words) =
      some { limbs := values
             restWords := (challenge tape start).remaining
             wordsUsed := (challenge tape start).draws } := by
  let initial : TraceStream :=
    ⟨⟨(AspisV8Completion.FSBoundedTranscript.squeeze tape start).2,
        AspisV8Completion.FSBoundedTranscript.words
          (AspisV8Completion.FSBoundedTranscript.squeeze tape start).1⟩,
      [(AspisV8Completion.FSBoundedTranscript.squeeze tape start).1], 0, []⟩
  let run := limbs tape 4 initial
  have initialCanonical : Canonical initial := by
    intro word member
    exact words_canonical _ word member
  have runSuccess : run.1 = some values := by
    simpa [challenge, initial, run] using success
  have consumed := decodeLimbs_drawDelta tape 4 initial values
    initialCanonical runSuccess
  have deltaEq : drawDelta initial run.2 = run.2.drawn := by
    simp [drawDelta, initial]
  rw [deltaEq] at consumed
  have extended := decodeLimbs_append_of_some 4 run.2.drawn
    run.2.current.remaining
    { limbs := values
      restWords := []
      wordsUsed := run.2.draws }
    (by simpa [initial] using consumed)
  simp only [appendFourLimbRest, List.nil_append] at extended
  have content := (challenge_content tape start).1
  change run.2.blocks.flatMap
      AspisV8Completion.FSBoundedTranscript.words =
        run.2.drawn ++ run.2.current.remaining at content
  change decodeLimbs 4 (run.2.blocks.flatMap
      AspisV8Completion.FSBoundedTranscript.words) = _
  rw [content]
  exact extended

theorem current_flattenedWords_eq_masked (blocks : List
    AspisV8Completion.FSBoundedTranscript.Block) :
    blocks.flatMap AspisV8Completion.FSBoundedTranscript.words =
      (flattenedWords blocks).map maskedM31 := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
      simp [flattenedWords,
        AspisV8Completion.FSV7FourBlockWordBridge.current_words_eq_masked_blockWords,
        ih]

theorem challenge_decodeLimbs_raw_exists (tape : Tape)
    (start : AspisV8Completion.FSBoundedTranscript.Transcript)
    (values : List Nat)
    (success : (challenge tape start).result = some values) :
    ∃ restWords, decodeLimbs 4
        (flattenedWords (challenge tape start).blocks) =
      some { limbs := values
             restWords := restWords
             wordsUsed := (challenge tape start).draws } := by
  have maskedRun := challenge_decodeLimbs tape start values success
  have wordsEq :
      (challenge tape start).blocks.flatMap
          AspisV8Completion.FSBoundedTranscript.words =
        (flattenedWords (challenge tape start).blocks).map maskedM31 :=
    current_flattenedWords_eq_masked _
  rw [wordsEq, AspisV8Completion.FSV7FourBlockWordBridge.decodeLimbs_map_maskedM31]
      at maskedRun
  cases rawRun : decodeLimbs 4 (flattenedWords (challenge tape start).blocks) with
  | none => simp [rawRun] at maskedRun
  | some decoded =>
      rw [rawRun] at maskedRun
      simp only [Option.map_some, Option.some.injEq] at maskedRun
      refine ⟨decoded.restWords, ?_⟩
      have limbsEq : decoded.limbs = values := by
        exact congrArg FourLimbDecode.limbs maskedRun
      have wordsUsedEq : decoded.wordsUsed = (challenge tape start).draws := by
        exact congrArg FourLimbDecode.wordsUsed maskedRun
      rw [← limbsEq, ← wordsUsedEq]

/-- Successful live sampling routes through the deployed V7 ordinary prefix
decoder with the same limbs, exact `draws`, and exact one-to-four early-stop
block count.  It does not claim those blocks are fresh or random. -/
theorem challenge_decodeOrdinaryPrefix (tape : Tape)
    (start : AspisV8Completion.FSBoundedTranscript.Transcript)
    (values : List Nat)
    (success : (challenge tape start).result = some values) :
    decodeOrdinaryPrefix (challenge tape start).blocks =
      some { value := encodeQm31Limbs values
             limbs := values
             wordsUsed := (challenge tape start).draws
             blocksUsed := (challenge tape start).blocks.length
             remainingBlocks := [] } := by
  obtain ⟨restWords, decoded⟩ :=
    challenge_decodeLimbs_raw_exists tape start values success
  obtain ⟨positive, cap⟩ := challenge_blocks_bounds tape start
  obtain ⟨balance, remaining⟩ := challenge_balance tape start
  have blocksUsed :
      blocksNeededForWords (challenge tape start).draws =
        (challenge tape start).blocks.length := by
    unfold blocksNeededForWords
    omega
  cases blocksEq : (challenge tape start).blocks with
  | nil => simp [blocksEq] at positive
  | cons first rest =>
      rw [blocksEq] at decoded
      have lengthEq : (challenge tape start).blocks.length =
          (first :: rest).length := congrArg List.length blocksEq
      have valid :
          0 < blocksNeededForWords (challenge tape start).draws ∧
            blocksNeededForWords (challenge tape start).draws ≤ 4 ∧
            blocksNeededForWords (challenge tape start).draws ≤
              (first :: rest).length := by
        rw [blocksUsed]
        exact ⟨by omega, ⟨by omega, by omega⟩⟩
      have restLt : rest.length < 4 := by
        have consCap : (first :: rest).length ≤ 4 := by omega
        simpa using consCap
      simp [decodeOrdinaryPrefix, blocksEq, decoded, valid, blocksUsed] <;>
        omega

#print axioms decodeLimb_drawDelta
#print axioms decodeLimbs_drawDelta
#print axioms challenge_decodeLimbs
#print axioms challenge_decodeOrdinaryPrefix

end AspisV8Completion.FSLiveChallengeV7Decode
