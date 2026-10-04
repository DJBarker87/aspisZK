import AspisV8R19.R640DecoderExactWords
import AspisV8R19.R642SourceScalarWrapper
import AspisV8R19.R643PackedRadixValues
import Mathlib.Tactic
set_option autoImplicit false
namespace AspisV8R19.R644AcceptedRadixSerialization
open Aeneas Aeneas.Std Result
open R623PackedDecoderExecution R624DecoderInnerExecution
open R640DecoderExactWords R643PackedRadixValues

/-- Mathematical digits, without silently replacing the forbidden digit P. -/
def radixChunks : (bs : List (Slice U8)) →
    (∀ b ∈ bs, b.val.length = 31) → List Nat
  | [], _ => []
  | b :: bs, h =>
      let ba : Array U8 31#usize := ⟨b.val, by simpa using h b (by simp)⟩
      List.ofFn (radixDigit ba) ++
        radixChunks bs (by intro c hc; exact h c (by simp [hc]))

theorem block_radix_values (b : Array U8 31#usize) :
    (blockWords (blockValues b)).map (fun v : U32 => v.val) = List.ofFn (radixDigit b) := by
  apply List.ext_getElem
  · simp [blockWords]
  · intro i hi hj
    have hi8 : i < 8 := by simpa [blockWords] using hi
    let j : Fin 8 := ⟨i,hi8⟩
    have hb := R642SourceScalarWrapper.block_word_matches_maskedLow32 b j
    have hv := masked_source_radix b j
    have he : ((blockWords (blockValues b))[i]!).val = radixDigit b j := by
      change ((blockWords (blockValues b))[i]!).bv.toNat = _
      rw [hb]
      exact hv
    rw [getElem!_pos (by simpa only [List.length_map] using hi)] at he
    simpa only [List.getElem_map, List.getElem_ofFn] using he

theorem words_radix_values (bs : List (Slice U8))
    (hc : ∀ b ∈ bs, b.val.length = 31) :
    (wordsOfChunks bs hc).map (fun v : U32 => v.val) = radixChunks bs hc := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [wordsOfChunks, radixChunks, List.map_append]
    rw [block_radix_values, ih]

/-- The full actually accepted selected decoder returns the mathematical
base-2^31 little-endian digits, for every accepted input and initial array. -/
theorem accepted_radix_serialization {N : Usize} (hN : N.val ≤ 104)
    (bytes : Slice U8) (out out1 : Array U32 N)
    (hexec : AspisR614SelectedCombineBeta.query_arithmetic.r55_decode_into bytes out =
      .ok (core.result.Result.Ok (),out1)) :
    ∃ ce : core.slice.iter.ChunksExact U8,
      ∃ hc : ∀ b ∈ ce.chunks, b.val.length = 31,
      core.slice.Slice.chunks_exact bytes 31#usize = .ok ce ∧
      out1.val.map (fun v : U32 => v.val) = radixChunks ce.chunks hc ∧
      (∀ v ∈ out1.val, v.val < 2147483647) := by
  obtain ⟨ce,hc,hce,hw⟩ := decoder_accepted_exact_words hN bytes out out1 hexec
  refine ⟨ce,hc,hce,?_,R635DecoderWholeCanonical.decoder_accepted_canonical
    hN bytes out out1 hexec⟩
  rw [hw, words_radix_values]

#print axioms block_radix_values
#print axioms words_radix_values
#print axioms accepted_radix_serialization
end AspisV8R19.R644AcceptedRadixSerialization
