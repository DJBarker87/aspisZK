import AspisV8R19.R623PackedDecoderExecution
import AspisV8R19.R624DecoderInnerExecution
import Mathlib.Tactic

set_option autoImplicit false
namespace AspisV8R19.R633PackedBlockResult
open Aeneas Aeneas.Std Result
open R623PackedDecoderExecution R624DecoderInnerExecution

/-- Actual 31-byte block execution: no assumed read, cast, update, or
iterator success. The sole bound ensures all eight destinations exist. -/
theorem block_result {N : Usize} (block : Usize) (b : Array U8 31#usize)
    (out : Array U32 N) (invalid : U32)
    (hblock : 8 * (block.val + 1) ≤ N.val) :
    decodeBlock block (Array.to_slice b) out invalid =
      .ok (blockOutput8 block (blockValues b) out,
        (blockWords (blockValues b)).foldl sourceInvalid invalid) := by
  rw [block_execution, wordRun_eight_result block (blockValues b) hblock out invalid]

/-- The exact source rejection accumulator accepts iff its incoming state
was accepted and each of the eight extracted/masked values is canonical.
This retains rejection of the value P; no canonicality premise is supplied. -/
theorem block_mask_accepted {N : Usize} (block : Usize)
    (b : Array U8 31#usize) (out : Array U32 N) (invalid : U32)
    (hblock : 8 * (block.val + 1) ≤ N.val) :
    R486ParserCanonicalMask.accepted
      ((blockWords (blockValues b)).foldl sourceInvalid invalid).bv ↔
      R486ParserCanonicalMask.accepted invalid.bv ∧
      ∀ value ∈ blockWords (blockValues b), value.val < 2147483647 := by
  have h := blockAcc_eight_canonical_iff block (blockValues b) hblock out invalid
  rw [blockAcc_eight_mask] at h
  exact h

#print axioms block_result
#print axioms block_mask_accepted
end AspisV8R19.R633PackedBlockResult
