import R1MixedLeafSlices
import R1MixedLeafDecoder
import R1ExactBaseProjection
import ExtractedRecordByteValue
import AspisV8R17.QM31WordTower

set_option autoImplicit false
namespace AspisR1FastDotsTailSlotByteProjectionsV1

open AspisR1.MixedLeafEncoding
open AspisR1.ExactLeafFieldCodec
open AspisR1.RetainedFieldByteCodec
open AspisR1.ExtractedRecordByteValue
open AspisR1.MixedLeafSlices

abbrev C1 := AspisR1.MixedLeafEncoding.C1
abbrev C2 := AspisR1.MixedLeafEncoding.C2

/-- The C1 quadratic tail is exactly the 16-byte window at the end of the
selected 120-byte slot. -/
theorem c1_tail_window (c1 : C1) (c2 : C2) (slot : Fin 4) :
    ((encodeC1 c1 ++ encodeC2 c2).drop (120 * slot.val + 104)).take 16 =
      encodeQM31 ((c1 slot).2) := by
  let base := 120 * slot.val
  have hbound : base ≤ (encodeC1 c1).length := by
    rw [encodeC1_length]
    dsimp [base]
    have hs := slot.isLt
    omega
  have hslot := c1_slot_slice c1 slot
  have hslotLength := encodeC1Slot_length (c1 slot)
  have hsplit : (encodeC1 c1).drop base =
      encodeC1Slot (c1 slot) ++ (encodeC1 c1).drop (base + 120) := by
    have h := (List.take_append_drop 120 ((encodeC1 c1).drop base)).symm
    rw [hslot] at h
    simpa [List.drop_drop, base, Nat.add_assoc] using h
  have h104 : 104 ≤ (encodeC1Slot (c1 slot)).length := by
    rw [hslotLength]
    omega
  have hdrop : (encodeC1 c1 ++ encodeC2 c2).drop (base + 104) =
      (encodeC1Slot (c1 slot)).drop 104 ++ ((encodeC1 c1).drop (base + 120) ++ encodeC2 c2) := by
    rw [← List.drop_drop]
    rw [List.drop_append_of_le_length hbound]
    rw [hsplit, List.append_assoc, List.drop_append_of_le_length h104, c1Slot_drop_words]
  have hprefix : ((encodeC1Slot (c1 slot)).drop 104).length = 16 := by
    rw [List.length_drop, hslotLength]
  have hqLen : (encodeQM31 (c1 slot).2).length = 16 := by
    rw [← c1Slot_drop_words, hprefix]
  rw [hdrop, c1Slot_drop_words, List.take_append_of_le_length (by rw [hqLen]),
    List.take_of_length_le (by rw [hqLen])]

/-- One C2 QM31 lane is exactly its 16-byte window in the selected 32-byte
slot after the 480-byte C1 prefix. -/
theorem c2_lane_window (c1 : C1) (c2 : C2) (slot : Fin 4) (term : Fin 2) :
    ((encodeC1 c1 ++ encodeC2 c2).drop (480 + 32 * slot.val + 16 * term.val)).take 16 =
      encodeQM31 ((c2 slot) term) := by
  let base := 32 * slot.val
  have hslotLength := encodeC2Slot_length (c2 slot)
  have hslot := c2_slot_slice c2 slot
  have hsplit : (encodeC2 c2).drop base =
      encodeC2Slot (c2 slot) ++ (encodeC2 c2).drop (base + 32) := by
    have h := (List.take_append_drop 32 ((encodeC2 c2).drop base)).symm
    rw [hslot] at h
    simpa [List.drop_drop, base, Nat.add_assoc] using h
  have hdropC1 : (encodeC1 c1 ++ encodeC2 c2).drop 480 = encodeC2 c2 := by
    rw [List.drop_append_of_le_length (by rw [encodeC1_length]), List.drop_of_length_le (by rw [encodeC1_length])]
    simp
  have hadd : 480 + base + 16 * term.val = 480 + (base + 16 * term.val) := by omega
  have hdrop : (encodeC1 c1 ++ encodeC2 c2).drop
      (480 + base + 16 * term.val) =
      (encodeC2Slot (c2 slot)).drop (16 * term.val) ++
        (encodeC2 c2).drop (base + 32) := by
    rw [hadd, ← List.drop_drop, hdropC1, ← List.drop_drop, hsplit,
      List.drop_append_of_le_length (by rw [hslotLength]; have ht := term.isLt; omega)]
  have hremain : 16 ≤ ((encodeC2Slot (c2 slot)).drop (16 * term.val)).length := by
    rw [List.length_drop, hslotLength]
    have ht := term.isLt
    omega
  have hwindow : ((encodeC2Slot (c2 slot)).drop (16 * term.val)).take 16 =
      encodeQM31 ((c2 slot) term) := by
    change (((List.ofFn (c2 slot)).flatMap encodeQM31).drop (16 * term.val)).take 16 = _
    exact AspisR1.FixedWidthSlice.ofFn_flatMap_slice 2 encodeQM31 16
      (fun _ => encodeQM31_length _) (c2 slot) term
  rw [hdrop, List.take_append_of_le_length hremain, hwindow]

/-- A source slice inherits its exact bytes from the common 608-byte opening
encoding equation. -/
theorem source_slice_bytes {a : Aeneas.Std.Array Aeneas.Std.U8 608#usize}
    (c1 : C1) (c2 : C2) (hbytes : a.val.map rawByte = encodeC1 c1 ++ encodeC2 c2)
    (start : Nat) :
    (a.val.slice start (start + 16)).map rawByte =
      ((encodeC1 c1 ++ encodeC2 c2).drop start).take 16 := by
  simp [List.slice, List.map_take, List.map_drop, hbytes]

theorem c1_tail_source_slice {a : Aeneas.Std.Array Aeneas.Std.U8 608#usize}
    (c1 : C1) (c2 : C2) (slot : Fin 4)
    (hbytes : a.val.map rawByte = encodeC1 c1 ++ encodeC2 c2) :
    (a.val.slice (120 * slot.val + 104) (120 * slot.val + 120)).map rawByte =
      encodeQM31 ((c1 slot).2) := by
  calc
    _ = ((encodeC1 c1 ++ encodeC2 c2).drop (120 * slot.val + 104)).take 16 :=
      source_slice_bytes c1 c2 hbytes _
    _ = encodeQM31 ((c1 slot).2) := c1_tail_window c1 c2 slot

theorem c2_lane_source_slice {a : Aeneas.Std.Array Aeneas.Std.U8 608#usize}
    (c1 : C1) (c2 : C2) (slot : Fin 4) (term : Fin 2)
    (hbytes : a.val.map rawByte = encodeC1 c1 ++ encodeC2 c2) :
    (a.val.slice (480 + 32 * slot.val + 16 * term.val)
      (480 + 32 * slot.val + 16 * term.val + 16)).map rawByte =
      encodeQM31 ((c2 slot) term) := by
  calc
    _ = ((encodeC1 c1 ++ encodeC2 c2).drop
      (480 + 32 * slot.val + 16 * term.val)).take 16 :=
      source_slice_bytes c1 c2 hbytes _
    _ = encodeQM31 ((c2 slot) term) := c2_lane_window c1 c2 slot term

end AspisR1FastDotsTailSlotByteProjectionsV1
