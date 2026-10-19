import R1FixedWidthSlice
import R1MixedLeafEncoding

/-! Fixed-offset slices for the current slot-major mixed leaf encodings. -/
set_option autoImplicit false

namespace AspisR1.MixedLeafSlices

open AspisR1.ExactLeafFieldCodec
open AspisR1.MixedLeafEncoding

theorem c1Slot_take_words (x : C1Slot) :
    (encodeC1Slot x).take 104 = (List.ofFn x.1).flatMap encodeM31 := by
  have hlen : ((List.ofFn x.1).flatMap encodeM31).length = 104 := by
    simp [List.length_flatMap, List.length_ofFn, encodeM31_length]
  rw [encodeC1Slot, List.take_append_of_le_length (by rw [hlen])]
  exact List.take_of_length_le (by rw [hlen])

theorem c1Slot_drop_words (x : C1Slot) :
    (encodeC1Slot x).drop 104 = encodeQM31 x.2 := by
  have hlen : ((List.ofFn x.1).flatMap encodeM31).length = 104 := by
    simp [List.length_flatMap, List.length_ofFn, encodeM31_length]
  rw [encodeC1Slot, List.drop_append_of_le_length (by rw [hlen]),
    List.drop_of_length_le (by rw [hlen])]
  simp

theorem c1Slot_m31_slice (x : C1Slot) (i : Fin 26) :
    ((encodeC1Slot x).drop (4 * i.val)).take 4 = encodeM31 (x.1 i) := by
  have hlen : ((List.ofFn x.1).flatMap encodeM31).length = 104 := by
    simp [List.length_flatMap, List.length_ofFn, encodeM31_length]
  have hidx : 4 * i.val ≤ ((List.ofFn x.1).flatMap encodeM31).length := by
    rw [hlen]
    omega
  have hremain : 4 ≤ (((List.ofFn x.1).flatMap encodeM31).drop (4 * i.val)).length := by
    simp only [List.length_drop]
    rw [hlen]
    omega
  rw [encodeC1Slot, List.drop_append_of_le_length hidx,
    List.take_append_of_le_length hremain]
  exact AspisR1.FixedWidthSlice.ofFn_flatMap_slice 26 encodeM31 4
    (fun _ => encodeM31_length _) x.1 i

theorem c1_slot_slice (slots : C1) (s : Fin 4) :
    ((encodeC1 slots).drop (120 * s.val)).take 120 = encodeC1Slot (slots s) := by
  exact AspisR1.FixedWidthSlice.ofFn_flatMap_slice 4 encodeC1Slot 120
    (fun _ => encodeC1Slot_length _) slots s

theorem c2_slot_slice (slots : C2) (s : Fin 4) :
    ((encodeC2 slots).drop (32 * s.val)).take 32 = encodeC2Slot (slots s) := by
  exact AspisR1.FixedWidthSlice.ofFn_flatMap_slice 4 encodeC2Slot 32
    (fun _ => encodeC2Slot_length _) slots s

#print axioms c1Slot_take_words
#print axioms c1Slot_drop_words
#print axioms c1Slot_m31_slice
#print axioms c1_slot_slice
#print axioms c2_slot_slice

end AspisR1.MixedLeafSlices
