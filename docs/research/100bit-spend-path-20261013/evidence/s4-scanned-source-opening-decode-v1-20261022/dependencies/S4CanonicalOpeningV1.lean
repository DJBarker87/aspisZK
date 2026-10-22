import S4CanonicalM31V1
import S4CanonicalQM31V1
import R1MixedLeafDecoder
set_option autoImplicit false
namespace AspisR1.S4CanonicalOpeningV1
open OraclePortCompactDraft AspisV8R19.DuplexFrames
open AspisR1.S4CanonicalBlocksV1 AspisR1.S4CanonicalM31V1 AspisR1.S4CanonicalQM31V1
open AspisR1.ExactLeafFieldCodec AspisR1.MixedLeafDecoder AspisR1.MixedLeafEncoding

theorem canonical_fixed_decode {A : Type} (d : Bytes → Option A) (units n : Nat)
    (bs : Bytes) (hlen : bs.length = (4*units)*n) (hc : canonical bs)
    (hd : ∀ xs, xs.length = 4*units → canonical xs → ∃ x, d xs = some x) :
    ∃ values, FixedWidthDecoder.decode d (4*units) n bs = some values := by
  apply decode_exists d (4*units) n canonical bs hlen hc
  · intro xs m hm hp
    exact canonical_split_blocks units xs hp
  · exact hd

theorem c1_slot_decode_exists (bs : Bytes) (hlen : bs.length = 120)
    (hc : canonical bs) : ∃ x, decodeC1Slot bs = some x := by
  obtain ⟨hp, ht⟩ := canonical_split_blocks 26 bs hc
  have hpl : (bs.take 104).length = 4*1*26 := by simp [List.length_take, hlen]
  have htl : (bs.drop 104).length = 16 := by simp [List.length_drop, hlen]
  obtain ⟨words, hw⟩ := canonical_fixed_decode decodeM31 1 26 (bs.take 104) hpl hp
    canonical_m31_decode_exists
  obtain ⟨tail, htail⟩ := canonical_qm31_decode_exists (bs.drop 104) htl ht
  exact ⟨(words,tail), by simp [decodeC1Slot, hw, htail]⟩

theorem c2_slot_decode_exists (bs : Bytes) (hlen : bs.length = 32)
    (hc : canonical bs) : ∃ x, decodeC2Slot bs = some x := by
  exact canonical_fixed_decode decodeQM31 4 2 bs hlen hc canonical_qm31_decode_exists

theorem c1_decode_exists (bs : Bytes) (hlen : bs.length = 480)
    (hc : canonical bs) : ∃ x, decodeC1 bs = some x := by
  exact canonical_fixed_decode decodeC1Slot 30 4 bs hlen hc c1_slot_decode_exists

theorem c2_decode_exists (bs : Bytes) (hlen : bs.length = 128)
    (hc : canonical bs) : ∃ x, decodeC2 bs = some x := by
  exact canonical_fixed_decode decodeC2Slot 8 4 bs hlen hc c2_slot_decode_exists

/-- Strict-scan canonicality supplies decoded C1/C2 values and their literal
encoded byte identity; no independently successful decode is assumed. -/
theorem canonical_opening_decode_exists (bs : Bytes) (hlen : bs.length = 608)
    (hc : canonical bs) :
    ∃ c1 c2, decodeC1 (bs.take 480) = some c1 ∧
      decodeC2 (bs.drop 480) = some c2 ∧
      bs = encodeC1 c1 ++ encodeC2 c2 := by
  obtain ⟨hp,ht⟩ := canonical_split_blocks 120 bs hc
  obtain ⟨c1,hc1⟩ := c1_decode_exists (bs.take 480) (by simp [List.length_take,hlen]) hp
  obtain ⟨c2,hc2⟩ := c2_decode_exists (bs.drop 480) (by simp [List.length_drop,hlen]) ht
  refine ⟨c1,c2,hc1,hc2,?_⟩
  rw [encodeC1_of_decode _ _ hc1, encodeC2_of_decode _ _ hc2]
  exact (List.take_append_drop 480 bs).symm
#print axioms canonical_fixed_decode
#print axioms c1_slot_decode_exists
#print axioms c2_slot_decode_exists
#print axioms c1_decode_exists
#print axioms c2_decode_exists
#print axioms canonical_opening_decode_exists
end AspisR1.S4CanonicalOpeningV1
