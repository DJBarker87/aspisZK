import R1FixedWidthEncoding
import R1ExactLeafFieldCodec

/-! Fixed-width, slot-major encodings for the current mixed C1/C2 leaves.
These are list-encoding facts only; they do not state parser or source
correspondence results. -/
set_option autoImplicit false

namespace AspisR1.MixedLeafEncoding

open AspisR1.ExactLeafFieldCodec

abbrev C1Slot := (Fin 26 → M31Exact) × QM31Exact
abbrev C2Slot := Fin 2 → QM31Exact
abbrev C1 := Fin 4 → C1Slot
abbrev C2 := Fin 4 → C2Slot

def encodeC1Slot (x : C1Slot) : List Byte :=
  (List.ofFn x.1).flatMap encodeM31 ++ encodeQM31 x.2

def encodeC2Slot (x : C2Slot) : List Byte :=
  (List.ofFn x).flatMap encodeQM31

def encodeC1 (slots : C1) : List Byte :=
  (List.ofFn slots).flatMap encodeC1Slot

def encodeC2 (slots : C2) : List Byte :=
  (List.ofFn slots).flatMap encodeC2Slot

theorem encodeC1Slot_length (x : C1Slot) : (encodeC1Slot x).length = 120 := by
  simp [encodeC1Slot, List.length_flatMap, List.length_ofFn,
    encodeM31_length, encodeQM31_length]

theorem encodeC2Slot_length (x : C2Slot) : (encodeC2Slot x).length = 32 := by
  simp [encodeC2Slot, List.length_flatMap, List.length_ofFn, encodeQM31_length]

theorem encodeC1_length (slots : C1) : (encodeC1 slots).length = 480 := by
  simp [encodeC1, List.length_flatMap, List.length_ofFn, encodeC1Slot_length]

theorem encodeC2_length (slots : C2) : (encodeC2 slots).length = 128 := by
  simp [encodeC2, List.length_flatMap, List.length_ofFn, encodeC2Slot_length]

theorem encodeC1Slot_injective : Function.Injective encodeC1Slot := by
  intro x y hxy
  have hheadLen : ((List.ofFn x.1).flatMap encodeM31).length =
      ((List.ofFn y.1).flatMap encodeM31).length := by
    simp [List.length_flatMap, List.length_ofFn, encodeM31_length]
  have hparts := List.append_inj hxy hheadLen
  rcases hparts with ⟨hwords, htail⟩
  have hcoeff : x.1 = y.1 :=
    AspisR1.FixedWidthEncoding.ofFn_flatMap_injective encodeM31 4 26
      (by decide) (fun _ => encodeM31_length _) encodeM31_injective hwords
  have hqm : x.2 = y.2 := encodeQM31_injective htail
  exact Prod.ext hcoeff hqm

theorem encodeC2Slot_injective : Function.Injective encodeC2Slot := by
  intro x y hxy
  exact AspisR1.FixedWidthEncoding.ofFn_flatMap_injective encodeQM31 16 2
    (by decide) (fun _ => encodeQM31_length _) encodeQM31_injective hxy

theorem encodeC1_injective : Function.Injective encodeC1 := by
  intro x y hxy
  exact AspisR1.FixedWidthEncoding.ofFn_flatMap_injective encodeC1Slot 120 4
    (by decide) (fun _ => encodeC1Slot_length _) encodeC1Slot_injective hxy

theorem encodeC2_injective : Function.Injective encodeC2 := by
  intro x y hxy
  exact AspisR1.FixedWidthEncoding.ofFn_flatMap_injective encodeC2Slot 32 4
    (by decide) (fun _ => encodeC2Slot_length _) encodeC2Slot_injective hxy

#print axioms encodeC1Slot_length
#print axioms encodeC2Slot_length
#print axioms encodeC1_length
#print axioms encodeC2_length
#print axioms encodeC1Slot_injective
#print axioms encodeC2Slot_injective
#print axioms encodeC1_injective
#print axioms encodeC2_injective

end AspisR1.MixedLeafEncoding
