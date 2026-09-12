import FSBoundedTranscript
import AspisFormal.K1.V7Tag73VariablePrefixGammaFlatRouting

/-!
# Current transcript words are the V7 four-block raw words after masking

This is a deterministic representation bridge.  It does not assert that four
blocks are fresh or uniform, nor that a complete `FSBoundedTranscript.challenge`
uses a caller-supplied four-block family.  Those are separate chronological
oracle/sampler obligations.
-/

set_option autoImplicit false

namespace AspisV8Completion.FSV7FourBlockWordBridge

namespace Current
open AspisV8Completion.FSBoundedTranscript

/-- The chronological current word stream for exactly four blocks. -/
def fourBlockWords
    (blocks : AspisK1.V7Tag73VariablePrefixGammaFactorization.FourGammaBlocks) :
    List Nat :=
  (List.ofFn blocks).flatMap words

end Current

open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73EightRetryDecoderBridge
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting

/-- One current transcript block exposes exactly the deployed V7 little-endian
words after the source's `0x7fffffff` mask. -/
theorem current_words_eq_masked_blockWords
    (block : AspisV8Completion.FSBoundedTranscript.Block) :
    AspisV8Completion.FSBoundedTranscript.words block =
      (blockWords block).map maskedM31 := by
  apply List.ext_getElem
  · simp [AspisV8Completion.FSBoundedTranscript.words, blockWords]
  · intro index leftBound rightBound
    have indexBound : index < 8 := by
      simpa [AspisV8Completion.FSBoundedTranscript.words] using leftBound
    interval_cases index <;> rfl

/-- Concatenating the current words of four chronological blocks is identical
to masking the V7 deployed decoder's flattened raw-word list. -/
theorem current_fourBlockWords_eq_masked_flattenedWords
    (blocks : FourGammaBlocks) :
    Current.fourBlockWords blocks =
      (flattenedWords (List.ofFn blocks)).map maskedM31 := by
  simp [Current.fourBlockWords, flattenedWords,
    current_words_eq_masked_blockWords]

/-- The same current four-block stream routed through the already proved V7
raw-stream equivalence.  No distributional premise occurs in this theorem. -/
theorem current_fourBlockWords_eq_masked_fourGammaBlocksRawEquiv
    (blocks : FourGammaBlocks) :
    Current.fourBlockWords blocks =
      (rawWordsToNat (fourGammaBlocksRawEquiv blocks).1).map maskedM31 := by
  rw [current_fourBlockWords_eq_masked_flattenedWords]
  rw [flattenedWords_fourGammaBlocksRawEquiv]

@[simp] theorem maskedM31_idempotent (word : Nat) :
    maskedM31 (maskedM31 word) = maskedM31 word := by
  simp [maskedM31, m31MaskModulus]

def maskLimbRemainder (decoded : LimbDecode) : LimbDecode :=
  { decoded with restWords := decoded.restWords.map maskedM31 }

def maskFourLimbRemainder (decoded : FourLimbDecode) : FourLimbDecode :=
  { decoded with restWords := decoded.restWords.map maskedM31 }

/-- Pre-masking words changes only the retained unread suffix.  It does not
change rejection, accepted limb values, or the exact number of attempts. -/
theorem decodeLimb_map_maskedM31 (fuel : Nat) (input : List Nat) :
    decodeLimb fuel (input.map maskedM31) =
      (decodeLimb fuel input).map maskLimbRemainder := by
  induction fuel generalizing input with
  | zero => rfl
  | succ fuel ih =>
      cases input with
      | nil => rfl
      | cons word rest =>
          by_cases rejected : maskedM31 word = m31Prime
          · simp only [List.map_cons, decodeLimb, rejected,
              if_pos, ih]
            cases decodeLimb fuel rest <;> rfl
          · simp [decodeLimb, rejected, maskLimbRemainder]

/-- The same commute for all four sequential limbs.  In particular, the
current transcript representation and the V7 deployed decoder return the
same limb vector and `wordsUsed`; only the explicitly retained suffix is
masked. -/
theorem decodeLimbs_map_maskedM31 (count : Nat) (input : List Nat) :
    decodeLimbs count (input.map maskedM31) =
      (decodeLimbs count input).map maskFourLimbRemainder := by
  induction count generalizing input with
  | zero => simp [decodeLimbs, maskFourLimbRemainder]
  | succ count ih =>
      simp only [decodeLimbs, decodeLimb_map_maskedM31]
      cases firstRun : decodeLimb 8 input with
      | none => rfl
      | some first =>
          rw [Option.map_some]
          simp [maskLimbRemainder, maskFourLimbRemainder, ih]
          cases tailRun : decodeLimbs count first.restWords <;>
            simp [maskFourLimbRemainder]

/-- Exact decoder bridge for the current four-block word representation.
This retains the successful run's real `wordsUsed` and masked unread words;
it does not assert that the live transcript necessarily consumes all four
blocks. -/
theorem decodeLimbs_current_fourBlockWords
    (blocks : FourGammaBlocks) :
    decodeLimbs 4 (Current.fourBlockWords blocks) =
      (tag73RawRun (fourGammaBlocksRawEquiv blocks)).map
        (fun result => maskFourLimbRemainder
          (limbsDecodeOfRawSuccess
            (fourGammaBlocksRawEquiv blocks).1 result)) := by
  rw [current_fourBlockWords_eq_masked_fourGammaBlocksRawEquiv]
  rw [decodeLimbs_map_maskedM31]
  rw [decodeFourLimbs_rawWordsToNat]
  simp [tag73RawRun, tag73LimbRetryLimit, tag73LimbCount,
    Option.map_map, Function.comp_def]

#print axioms current_words_eq_masked_blockWords
#print axioms current_fourBlockWords_eq_masked_flattenedWords
#print axioms current_fourBlockWords_eq_masked_fourGammaBlocksRawEquiv
#print axioms maskedM31_idempotent
#print axioms decodeLimb_map_maskedM31
#print axioms decodeLimbs_map_maskedM31
#print axioms decodeLimbs_current_fourBlockWords

end AspisV8Completion.FSV7FourBlockWordBridge
