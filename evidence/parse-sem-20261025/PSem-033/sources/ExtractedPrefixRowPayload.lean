import ExtractedPrefixCoefficients
import ExtractedPrefixFrameAgreement
import R1SemanticRecordCodec

/-! Actual successful semantic record parsing supplies the unchanged typed
payload decoder. The byte map and row position are explicit. -/
set_option autoImplicit false
namespace AspisR1.ExtractedPrefixRowPayload
open Aeneas Aeneas.Std Result
open ExtractedRecordByteValue SemanticCoefficientCodec
open SemanticRecordCodec

theorem parse_record_decode (i : Fin 25) (row : U8) (hrow : row.val = i.val)
    (frame payload : Slice U8)
    (h : AspisR1PrefixAggregateParser.r1_wire.parse_record row frame =
      ok (core.result.Result.Ok payload)) :
    ∃ value : RowPayload i,
      decode i (frame.val.map rawByte) = some value ∧
      encode value = frame.val.map rawByte := by
  obtain ⟨tag, size, ht, hlen, hf, _⟩ :=
    ExtractedPrefixFrameAgreement.parse_record_frame_success row frame payload h
  suffices hd : ∃ value : RowPayload i,
      decode i (frame.val.map rawByte) = some value by
    obtain ⟨value, hv⟩ := hd
    exact ⟨value, hv, encode_of_decode i _ value hv⟩
  by_cases h2 : i.val = 2
  · have ht' : (1#u8, 32#usize) = (tag, size) := by
      apply Option.some.inj
      simpa only [ExtractedRowShape.table, hrow, if_pos h2] using ht
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ht'.symm
    change payload.val.length = 32 at hlen
    change RecordFrameCodec.parse 1 32 (frame.val.map rawByte) =
      some (payload.val.map rawByte) at hf
    refine ⟨⟨.c2Root (FS2.Duplex.stateOfBytes
      (payload.val.map rawByte)), h2⟩, ?_⟩
    simp only [decode, dif_pos h2, hf, Option.bind_some, decodeState,
      List.length_map, dif_pos hlen, Option.map_some]
  · by_cases h14 : i.val = 14
    · have ht' : (3#u8, 32#usize) = (tag, size) := by
        apply Option.some.inj
        simpa only [ExtractedRowShape.table, hrow, if_neg h2, if_pos h14] using ht
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj ht'.symm
      change payload.val.length = 32 at hlen
      change RecordFrameCodec.parse 3 32 (frame.val.map rawByte) =
        some (payload.val.map rawByte) at hf
      obtain ⟨_, _, hs⟩ :=
        ExtractedPrefixStrictPayload.parse_record_strict_payload row frame payload
          (by omega) h
      obtain ⟨lo, hd, _⟩ := ExtractedPrefixCoefficients.decode_low payload.val hlen hs
      refine ⟨⟨.maskSum (ExtractedPrefixSemanticLow.lowValue lo), h14⟩, ?_⟩
      simp only [decode, dif_neg h2, dif_pos h14, hf, Option.bind_some,
        hd, Option.map_some]
    · by_cases hp : 15 ≤ i.val
      · have h25 : i.val ≠ 25 := by omega
        have h26 : i.val ≠ 26 := by omega
        have h13 : ¬ i.val ≤ 13 := by omega
        have h24 : 15 ≤ i.val ∧ i.val ≤ 24 := by omega
        have ht' : (2#u8, 896#usize) = (tag, size) := by
          apply Option.some.inj
          simpa only [ExtractedRowShape.table, hrow, if_neg h2, if_neg h14,
            if_neg h25, if_neg h26, if_neg h13, if_pos h24] using ht
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj ht'.symm
        change payload.val.length = 896 at hlen
        change RecordFrameCodec.parse 2 896 (frame.val.map rawByte) =
          some (payload.val.map rawByte) at hf
        obtain ⟨_, _, hs⟩ :=
          ExtractedPrefixStrictPayload.parse_record_strict_payload row frame payload
            (by omega) h
        obtain ⟨limbs, hd, _, _⟩ :=
          ExtractedPrefixCoefficients.decode_coefficients payload.val hlen hs
        refine ⟨⟨.polynomial (fun j => ExtractedPrefixSemanticLow.lowValue (limbs j)), hp⟩, ?_⟩
        simp only [decode, dif_neg h2, dif_neg h14, dif_pos hp, hf,
          Option.bind_some, hd, Option.map_some]
      · have h25 : i.val ≠ 25 := by omega
        have h26 : i.val ≠ 26 := by omega
        have h13 : i.val ≤ 13 := by omega
        have ht' : (0#u8, 0#usize) = (tag, size) := by
          apply Option.some.inj
          simpa only [ExtractedRowShape.table, hrow, if_neg h2, if_neg h14,
            if_neg h25, if_neg h26, if_pos h13] using ht
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj ht'.symm
        change RecordFrameCodec.parse 0 0 (frame.val.map rawByte) =
          some (payload.val.map rawByte) at hf
        refine ⟨⟨.empty, by simp only [validRow]; omega⟩, ?_⟩
        simp only [decode, dif_neg h2, dif_neg h14, dif_neg hp, hf, Option.map_some]

#print axioms parse_record_decode
end AspisR1.ExtractedPrefixRowPayload
