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

#print axioms current_words_eq_masked_blockWords
#print axioms current_fourBlockWords_eq_masked_flattenedWords
#print axioms current_fourBlockWords_eq_masked_fourGammaBlocksRawEquiv

end AspisV8Completion.FSV7FourBlockWordBridge
