import ExtractedPrefixSemanticLow
import ExtractedPrefixChunkOrder

/-! Ordered actual chunks supply the unchanged 28-coefficient decoder. -/
set_option autoImplicit false
namespace AspisR1.ExtractedPrefixCoefficients
open Aeneas Aeneas.Std
open ExtractedRecordByteValue ExtractedPrefixStrictPayload
open ExtractedPrefixSemanticLow SemanticCoefficientCodec
open RetainedFieldByteCodec

theorem decode_low (raw : List U8) (hlen : raw.length = 32)
    (hstrict : ∀ chunk ∈ (List.toChunksExact 32 (by decide) raw).1,
      StrictLowChunk chunk) :
    ∃ lo : QM31Limbs,
      decodeLow (raw.map rawByte) = some (lowValue lo) ∧
      encodeLow (lowValue lo) = raw.map rawByte := by
  apply strict_chunk_decodeLow
  apply hstrict
  have hm := ExtractedPrefixChunkOrder.slice_mem 32 (by decide) raw 0 (by omega)
  simpa only [Nat.mul_zero, List.drop_zero,
    List.take_of_length_le (by omega : raw.length ≤ 32)] using hm

/-- Every slot is the canonical low value of the original bytes at offset
32*i. The coefficient encoder recovers the entire payload in that order. -/
theorem decode_coefficients (raw : List U8) (hlen : raw.length = 896)
    (hstrict : ∀ chunk ∈ (List.toChunksExact 32 (by decide) raw).1,
      StrictLowChunk chunk) :
    ∃ limbs : Fin 28 → QM31Limbs,
      decodeCoefficients (raw.map rawByte) = some (fun i => lowValue (limbs i)) ∧
      encodeCoefficients (fun i => lowValue (limbs i)) = raw.map rawByte ∧
      ∀ i : Fin 28,
        encodeLow (lowValue (limbs i)) =
          ((raw.drop (32 * i.val)).take 32).map rawByte := by
  have hslot : ∀ i : Fin 28, ∃ lo : QM31Limbs,
      decodeLow (((raw.drop (32 * i.val)).take 32).map rawByte) = some (lowValue lo) ∧
      encodeLow (lowValue lo) = ((raw.drop (32 * i.val)).take 32).map rawByte := by
    intro i
    apply strict_chunk_decodeLow
    apply hstrict
    apply ExtractedPrefixChunkOrder.slice_mem
    omega
  classical
  choose limbs hd he using hslot
  have hdecode : decodeCoefficients (raw.map rawByte) =
      some (fun i => lowValue (limbs i)) := by
    apply (decodeCoefficients_eq_some_iff _ _).mpr
    refine ⟨by simpa only [List.length_map] using hlen, ?_⟩
    intro i
    simpa only [List.map_take, List.map_drop] using hd i
  exact ⟨limbs, hdecode, encodeCoefficients_of_decode _ _ hdecode, he⟩

#print axioms decode_low
#print axioms decode_coefficients
end AspisR1.ExtractedPrefixCoefficients
