import R1MixedLeafSlices
import ExtractedRecordByteValue

set_option autoImplicit false

namespace AspisR1S4C1M31SourceSliceV1

open AspisR1.MixedLeafEncoding
open AspisR1.MixedLeafSlices
open AspisR1.ExactLeafFieldCodec
open AspisR1.ExtractedRecordByteValue

abbrev C1 := AspisR1.MixedLeafEncoding.C1
abbrev C2 := AspisR1.MixedLeafEncoding.C2

theorem source_slice_bytes4 {a : Aeneas.Std.Array Aeneas.Std.U8 608#usize}
    (c1 : C1) (c2 : C2)
    (hbytes : a.val.map rawByte = encodeC1 c1 ++ encodeC2 c2)
    (start : Nat) :
    (a.val.slice start (start + 4)).map rawByte =
      ((encodeC1 c1 ++ encodeC2 c2).drop start).take 4 := by
  simp [List.slice, List.map_take, List.map_drop, hbytes]

theorem c1_m31_lane_window (c1 : C1) (c2 : C2)
    (slot : Fin 4) (term : Fin 26) :
    ((encodeC1 c1 ++ encodeC2 c2).drop
      (120 * slot.val + 4 * term.val)).take 4 =
        encodeM31 ((c1 slot).1 term) := by
  let base := 120 * slot.val
  have hbound : base ≤ (encodeC1 c1).length := by
    rw [encodeC1_length]
    dsimp [base]
    omega
  have hslot := c1_slot_slice c1 slot
  have hslotLength := encodeC1Slot_length (c1 slot)
  have hsplit : (encodeC1 c1).drop base =
      encodeC1Slot (c1 slot) ++ (encodeC1 c1).drop (base + 120) := by
    have h := (List.take_append_drop 120 ((encodeC1 c1).drop base)).symm
    rw [hslot] at h
    simpa [List.drop_drop, base, Nat.add_assoc] using h
  have hterm : 4 * term.val ≤ (encodeC1Slot (c1 slot)).length := by
    rw [hslotLength]
    have ht := term.isLt
    omega
  have hdrop : (encodeC1 c1 ++ encodeC2 c2).drop (base + 4 * term.val) =
      (encodeC1Slot (c1 slot)).drop (4 * term.val) ++
        ((encodeC1 c1).drop (base + 120) ++ encodeC2 c2) := by
    rw [← List.drop_drop, List.drop_append_of_le_length hbound, hsplit,
      List.append_assoc, List.drop_append_of_le_length hterm]
  have hremain : 4 ≤
      ((encodeC1Slot (c1 slot)).drop (4 * term.val)).length := by
    rw [List.length_drop, hslotLength]
    have ht := term.isLt
    omega
  rw [hdrop, List.take_append_of_le_length hremain]
  have hlane : ((encodeC1Slot (c1 slot)).drop (4 * term.val)).take 4 =
      encodeM31 ((c1 slot).1 term) := by
    simpa using c1Slot_m31_slice (c1 slot) term
  exact hlane

theorem c1_m31_source_slice {a : Aeneas.Std.Array Aeneas.Std.U8 608#usize}
    (c1 : C1) (c2 : C2) (slot : Fin 4) (term : Fin 26)
    (hbytes : a.val.map rawByte = encodeC1 c1 ++ encodeC2 c2) :
    (a.val.slice (120 * slot.val + 4 * term.val)
      (120 * slot.val + 4 * term.val + 4)).map rawByte =
        encodeM31 ((c1 slot).1 term) := by
  calc
    _ = ((encodeC1 c1 ++ encodeC2 c2).drop
      (120 * slot.val + 4 * term.val)).take 4 :=
        source_slice_bytes4 c1 c2 hbytes _
    _ = encodeM31 ((c1 slot).1 term) := c1_m31_lane_window c1 c2 slot term

end AspisR1S4C1M31SourceSliceV1
