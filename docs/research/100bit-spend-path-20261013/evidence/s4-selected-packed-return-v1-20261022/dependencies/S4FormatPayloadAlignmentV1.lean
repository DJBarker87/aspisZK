import OraclePortPackedChoiceC4
import ExtractedRecordByteValue
import MultiproofConeCanonical

set_option autoImplicit false
namespace AspisR1S4FormatPayloadAlignmentV1
open Aeneas Aeneas.Std Result
open AspisR1.OraclePortCompactDraft
open AspisR1.OraclePortSelectedDraft (opening)
open AspisR1.MultiproofConeCanonical (bytesOf)

/-- The two serialized payload partitions are exactly the source opening's
first 480 and following 128 bytes. This is framing only, not authentication. -/
theorem payload_partitions
    (proof : Slice U8) (hlen : proof.val.length = 57607)
    (p : Parsed) (hwire : p.wire = bytesOf proof.val)
    (pos : Nat) (hpos : pos < 22)
    (q : Slice U8) (a : Array U8 608#usize)
    (hread : q.val = proof.val.slice (10055 + pos*832) (10055 + pos*832 + 832))
    (ha : a.val = q.val.slice 0 (608#usize)) :
    AspisR1.OraclePortPackedChoiceC4.payload p 0 pos =
        (a.val.map AspisR1.ExtractedRecordByteValue.rawByte).take 480 ∧
    AspisR1.OraclePortPackedChoiceC4.payload p 1 pos =
        (a.val.map AspisR1.ExtractedRecordByteValue.rawByte).drop 480 := by
  have hmap : bytesOf a.val = a.val.map AspisR1.ExtractedRecordByteValue.rawByte := by
    apply List.map_congr_left
    intro b _
    apply Fin.ext
    rfl
  have hqbytes : bytesOf q.val =
      slice (bytesOf proof.val) (10055 + pos*832) 832 := by
    simp [bytesOf, hread, List.slice, slice]
  have hopen : opening p pos = bytesOf q.val := by
    unfold opening
    rw [hwire, hqbytes]
  have habe : bytesOf a.val = (bytesOf q.val).take 608 := by
    simp [bytesOf, ha, List.slice, slice]
  have hprefix : (bytesOf q.val).take 480 = (bytesOf a.val).take 480 := by
    rw [habe]
    simp only [List.take_take]
    congr 1
  have htail : slice (bytesOf q.val) 480 128 =
      (bytesOf a.val).drop 480 := by
    rw [habe]
    simp [slice, List.drop_take]
  constructor
  · change (opening p pos).take 480 = _
    rw [hopen, ← hmap]
    exact hprefix
  · change slice (opening p pos) 480 128 = _
    rw [hopen, ← hmap]
    exact htail

#print axioms payload_partitions
end AspisR1S4FormatPayloadAlignmentV1
