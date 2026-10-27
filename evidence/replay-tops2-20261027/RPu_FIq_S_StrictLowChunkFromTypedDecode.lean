import StrictLowChunkCodec

set_option autoImplicit false
namespace AspisR1.StrictLowChunkFromTypedDecode
open Aeneas Aeneas.Std
open AspisR1.ExtractedRecordByteValue
open AspisR1.ExtractedRecordStrictLow
open AspisR1.ExtractedPrefixStrictPayload
open AspisR1.ExtractedPrefixSemanticLow
open AspisR1.RetainedFieldByteCodec
open AspisR1.RetainedExactLimbCodec
open AspisR1.WideExactLimbCodec
open AspisR1.StrictWideByteCodec
open AspisR1.SemanticCoefficientCodec

theorem lowValue_surjective (value : LowWide) :
    ∃ limbs : QM31Limbs, lowValue limbs = value := by
  let limbs := qm31ExactLimbEquiv.symm value.val.re
  refine ⟨limbs, ?_⟩
  apply Subtype.ext
  apply QuadraticAlgebra.ext
  · change qm31ExactLimbEquiv limbs = value.val.re
    exact qm31ExactLimbEquiv.apply_symm_apply value.val.re
  · exact (pair_high_zero limbs).trans value.property.symm

/-- The retained typed decoder already supplies the same strict low-chunk
property consumed by the actual parser bridge. This is an inverse of the
existing strict-chunk decoder theorem, on the exact same input bytes. -/
theorem strictLowChunk_of_decodeLow (raw : List U8) (value : LowWide)
    (h : decodeLow (raw.map rawByte) = some value) : StrictLowChunk raw := by
  obtain ⟨limbs, rfl⟩ := lowValue_surjective value
  have he := encodeLow_of_decode (raw.map rawByte) (lowValue limbs) h
  have hbytes : List.ofFn (encodeWideLE (limbs, fun _ => zeroLimb)) = raw.map rawByte := by
    change List.ofFn (encodeWideLE
      (pairExactEquiv.symm (pairExactEquiv (limbs, fun _ => zeroLimb)))) = _ at he
    simpa only [Equiv.symm_apply_apply] using he
  exact ⟨encodeWideLE (limbs, fun _ => zeroLimb), hbytes, limbs,
    decodeWideLE_encodeWideLE _, hbytes⟩

theorem typed_coefficients_strict (raw : List U8) (typed : Coefficients)
    (h : decodeCoefficients (raw.map rawByte) = some typed) :
    raw.length = 896 ∧ ∀ j : Fin 28,
      StrictLowChunk ((raw.drop (32*j.val)).take 32) := by
  obtain ⟨hlen, hslots⟩ := (decodeCoefficients_eq_some_iff _ _).mp h
  refine ⟨by simpa only [List.length_map] using hlen, ?_⟩
  intro j
  apply strictLowChunk_of_decodeLow _ (typed j)
  simpa only [List.map_drop, List.map_take] using hslots j

#print axioms lowValue_surjective
#print axioms strictLowChunk_of_decodeLow
#print axioms typed_coefficients_strict
end AspisR1.StrictLowChunkFromTypedDecode
