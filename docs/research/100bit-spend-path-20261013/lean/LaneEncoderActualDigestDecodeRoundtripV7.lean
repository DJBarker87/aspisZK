import LaneEncoderActualDigestDecoderSuccess
import LaneEncoderActualDigestChunkFieldParserV4
import LaneEncoderDigestChunks
import LaneEncoderM31FieldBytes
import AspisR1PairForestLaneEncoderTailSourceCut.Funs
import AspisR1TerminalDecoder.Funs
import Aeneas.Std
set_option autoImplicit false
namespace AspisR1PairForestLaneEncoderTailActualDigestDecodeRoundtrip
open Aeneas Aeneas.Std Result

private theorem index_usize_ok {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (hi : i.val < n.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

theorem actual_decode_digest_after_successful_encode
    (digest : Array AspisR1PairForestLaneEncoderTailSourceCut.M31 8#usize)
    (encoded : Array U8 32#usize)
    (hencode : AspisR1PairForestLaneEncoderTailSourceCut.encode_digest_canonical digest = .ok encoded)
    (hcanonical : ∀ i : Usize, i.val < 8 → ∀ value : AspisR1PairForestLaneEncoderTailSourceCut.M31,
      Array.index_usize digest i = .ok value → value.val < 2147483647) :
    AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical encoded =
      .ok (.Ok digest) := by
  have hproj := AspisR1PairForestLaneEncoderTailActualDigestChunks.successful_digest_chunks digest encoded hencode
  rcases hproj.chunk0 with ⟨value0, fieldBytes0, hindex0, hfield0, hwindow0⟩
  have hcanon0 : value0.val < 2147483647 := hcanonical 0#usize (by decide) value0 hindex0
  have hparser0 : AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes
      (AspisR1PairForestLaneEncoderTailChunkArrayEquality.makeChunk encoded 0 (by omega)) = .ok (some value0) := by
    exact AspisR1PairForestLaneEncoderTailActualDigestChunkFieldParser.actual_m31_parser_accepts_encoded_field_window
      encoded 0 (by omega) value0 fieldBytes0 hfield0 hwindow0 hcanon0
  have hsourceParser0 : AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes
      (Array.make 4#usize [encoded.val[0]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega), encoded.val[1]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega), encoded.val[2]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega), encoded.val[3]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega)]) = .ok (some value0) := by
    simpa only [AspisR1PairForestLaneEncoderTailChunkArrayEquality.makeChunk] using hparser0
  rcases hproj.chunk1 with ⟨value1, fieldBytes1, hindex1, hfield1, hwindow1⟩
  have hcanon1 : value1.val < 2147483647 := hcanonical 1#usize (by decide) value1 hindex1
  have hparser1 : AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes
      (AspisR1PairForestLaneEncoderTailChunkArrayEquality.makeChunk encoded 4 (by omega)) = .ok (some value1) := by
    exact AspisR1PairForestLaneEncoderTailActualDigestChunkFieldParser.actual_m31_parser_accepts_encoded_field_window
      encoded 4 (by omega) value1 fieldBytes1 hfield1 hwindow1 hcanon1
  have hsourceParser1 : AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes
      (Array.make 4#usize [encoded.val[4]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega), encoded.val[5]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega), encoded.val[6]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega), encoded.val[7]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega)]) = .ok (some value1) := by
    simpa only [AspisR1PairForestLaneEncoderTailChunkArrayEquality.makeChunk] using hparser1
  rcases hproj.chunk2 with ⟨value2, fieldBytes2, hindex2, hfield2, hwindow2⟩
  have hcanon2 : value2.val < 2147483647 := hcanonical 2#usize (by decide) value2 hindex2
  have hparser2 : AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes
      (AspisR1PairForestLaneEncoderTailChunkArrayEquality.makeChunk encoded 8 (by omega)) = .ok (some value2) := by
    exact AspisR1PairForestLaneEncoderTailActualDigestChunkFieldParser.actual_m31_parser_accepts_encoded_field_window
      encoded 8 (by omega) value2 fieldBytes2 hfield2 hwindow2 hcanon2
  have hsourceParser2 : AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes
      (Array.make 4#usize [encoded.val[8]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega), encoded.val[9]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega), encoded.val[10]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega), encoded.val[11]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega)]) = .ok (some value2) := by
    simpa only [AspisR1PairForestLaneEncoderTailChunkArrayEquality.makeChunk] using hparser2
  rcases hproj.chunk3 with ⟨value3, fieldBytes3, hindex3, hfield3, hwindow3⟩
  have hcanon3 : value3.val < 2147483647 := hcanonical 3#usize (by decide) value3 hindex3
  have hparser3 : AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes
      (AspisR1PairForestLaneEncoderTailChunkArrayEquality.makeChunk encoded 12 (by omega)) = .ok (some value3) := by
    exact AspisR1PairForestLaneEncoderTailActualDigestChunkFieldParser.actual_m31_parser_accepts_encoded_field_window
      encoded 12 (by omega) value3 fieldBytes3 hfield3 hwindow3 hcanon3
  have hsourceParser3 : AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes
      (Array.make 4#usize [encoded.val[12]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega), encoded.val[13]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega), encoded.val[14]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega), encoded.val[15]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega)]) = .ok (some value3) := by
    simpa only [AspisR1PairForestLaneEncoderTailChunkArrayEquality.makeChunk] using hparser3
  rcases hproj.chunk4 with ⟨value4, fieldBytes4, hindex4, hfield4, hwindow4⟩
  have hcanon4 : value4.val < 2147483647 := hcanonical 4#usize (by decide) value4 hindex4
  have hparser4 : AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes
      (AspisR1PairForestLaneEncoderTailChunkArrayEquality.makeChunk encoded 16 (by omega)) = .ok (some value4) := by
    exact AspisR1PairForestLaneEncoderTailActualDigestChunkFieldParser.actual_m31_parser_accepts_encoded_field_window
      encoded 16 (by omega) value4 fieldBytes4 hfield4 hwindow4 hcanon4
  have hsourceParser4 : AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes
      (Array.make 4#usize [encoded.val[16]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega), encoded.val[17]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega), encoded.val[18]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega), encoded.val[19]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega)]) = .ok (some value4) := by
    simpa only [AspisR1PairForestLaneEncoderTailChunkArrayEquality.makeChunk] using hparser4
  rcases hproj.chunk5 with ⟨value5, fieldBytes5, hindex5, hfield5, hwindow5⟩
  have hcanon5 : value5.val < 2147483647 := hcanonical 5#usize (by decide) value5 hindex5
  have hparser5 : AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes
      (AspisR1PairForestLaneEncoderTailChunkArrayEquality.makeChunk encoded 20 (by omega)) = .ok (some value5) := by
    exact AspisR1PairForestLaneEncoderTailActualDigestChunkFieldParser.actual_m31_parser_accepts_encoded_field_window
      encoded 20 (by omega) value5 fieldBytes5 hfield5 hwindow5 hcanon5
  have hsourceParser5 : AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes
      (Array.make 4#usize [encoded.val[20]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega), encoded.val[21]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega), encoded.val[22]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega), encoded.val[23]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega)]) = .ok (some value5) := by
    simpa only [AspisR1PairForestLaneEncoderTailChunkArrayEquality.makeChunk] using hparser5
  rcases hproj.chunk6 with ⟨value6, fieldBytes6, hindex6, hfield6, hwindow6⟩
  have hcanon6 : value6.val < 2147483647 := hcanonical 6#usize (by decide) value6 hindex6
  have hparser6 : AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes
      (AspisR1PairForestLaneEncoderTailChunkArrayEquality.makeChunk encoded 24 (by omega)) = .ok (some value6) := by
    exact AspisR1PairForestLaneEncoderTailActualDigestChunkFieldParser.actual_m31_parser_accepts_encoded_field_window
      encoded 24 (by omega) value6 fieldBytes6 hfield6 hwindow6 hcanon6
  have hsourceParser6 : AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes
      (Array.make 4#usize [encoded.val[24]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega), encoded.val[25]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega), encoded.val[26]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega), encoded.val[27]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega)]) = .ok (some value6) := by
    simpa only [AspisR1PairForestLaneEncoderTailChunkArrayEquality.makeChunk] using hparser6
  rcases hproj.chunk7 with ⟨value7, fieldBytes7, hindex7, hfield7, hwindow7⟩
  have hcanon7 : value7.val < 2147483647 := hcanonical 7#usize (by decide) value7 hindex7
  have hparser7 : AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes
      (AspisR1PairForestLaneEncoderTailChunkArrayEquality.makeChunk encoded 28 (by omega)) = .ok (some value7) := by
    exact AspisR1PairForestLaneEncoderTailActualDigestChunkFieldParser.actual_m31_parser_accepts_encoded_field_window
      encoded 28 (by omega) value7 fieldBytes7 hfield7 hwindow7 hcanon7
  have hsourceParser7 : AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes
      (Array.make 4#usize [encoded.val[28]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega), encoded.val[29]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega), encoded.val[30]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega), encoded.val[31]'(by have h := encoded.property; change encoded.val.length = 32 at h; omega)]) = .ok (some value7) := by
    simpa only [AspisR1PairForestLaneEncoderTailChunkArrayEquality.makeChunk] using hparser7
  have hdecoded := AspisR1PairForestLaneEncoderTailActualDigestDecoderSuccess.successful_decode_digest_of_chunks
    encoded value0 value1 value2 value3 value4 value5 value6 value7
    hsourceParser0 hsourceParser1 hsourceParser2 hsourceParser3 hsourceParser4 hsourceParser5 hsourceParser6 hsourceParser7
  have hval0 : value0 = digest.val[0]'(by have h := digest.property; change digest.val.length = 8 at h; omega) := by
    have hidx := index_usize_ok digest 0#usize (by decide)
    exact Result.ok.inj (hindex0.symm.trans hidx)
  have hval1 : value1 = digest.val[1]'(by have h := digest.property; change digest.val.length = 8 at h; omega) := by
    have hidx := index_usize_ok digest 1#usize (by decide)
    exact Result.ok.inj (hindex1.symm.trans hidx)
  have hval2 : value2 = digest.val[2]'(by have h := digest.property; change digest.val.length = 8 at h; omega) := by
    have hidx := index_usize_ok digest 2#usize (by decide)
    exact Result.ok.inj (hindex2.symm.trans hidx)
  have hval3 : value3 = digest.val[3]'(by have h := digest.property; change digest.val.length = 8 at h; omega) := by
    have hidx := index_usize_ok digest 3#usize (by decide)
    exact Result.ok.inj (hindex3.symm.trans hidx)
  have hval4 : value4 = digest.val[4]'(by have h := digest.property; change digest.val.length = 8 at h; omega) := by
    have hidx := index_usize_ok digest 4#usize (by decide)
    exact Result.ok.inj (hindex4.symm.trans hidx)
  have hval5 : value5 = digest.val[5]'(by have h := digest.property; change digest.val.length = 8 at h; omega) := by
    have hidx := index_usize_ok digest 5#usize (by decide)
    exact Result.ok.inj (hindex5.symm.trans hidx)
  have hval6 : value6 = digest.val[6]'(by have h := digest.property; change digest.val.length = 8 at h; omega) := by
    have hidx := index_usize_ok digest 6#usize (by decide)
    exact Result.ok.inj (hindex6.symm.trans hidx)
  have hval7 : value7 = digest.val[7]'(by have h := digest.property; change digest.val.length = 8 at h; omega) := by
    have hidx := index_usize_ok digest 7#usize (by decide)
    exact Result.ok.inj (hindex7.symm.trans hidx)
  have harray : Array.make 8#usize [value0,value1,value2,value3,value4,value5,value6,value7] = digest := by
    apply Subtype.ext
    apply List.ext_getElem
    · simp [Array.make, digest.property]
    · intro i hi hj
      have hlen : digest.val.length = 8 := by have h := digest.property; change digest.val.length = 8 at h; exact h
      have hcase : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [Array.make] using hval0
      · simpa [Array.make] using hval1
      · simpa [Array.make] using hval2
      · simpa [Array.make] using hval3
      · simpa [Array.make] using hval4
      · simpa [Array.make] using hval5
      · simpa [Array.make] using hval6
      · simpa [Array.make] using hval7
  rw [hdecoded, harray]

#print axioms actual_decode_digest_after_successful_encode
end AspisR1PairForestLaneEncoderTailActualDigestDecodeRoundtrip
