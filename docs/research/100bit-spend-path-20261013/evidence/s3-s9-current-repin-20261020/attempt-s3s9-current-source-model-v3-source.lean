import S2LibraFactoredIdentity
import R22ControlBounds

/-! Source-shaped current S3/S9 fragments.  This module is intentionally a
candidate source model: these statements do not assert that Rust `Weights`
was emitted or refined by an accepted extractor. -/
set_option autoImplicit false
namespace AspisR1.S3S9CurrentSourceModel

/-- `Variant::row` for S2, expanded from TAU = [3,4,2,0,1].  The summands
occupy pairwise-disjoint two-bit fields for every j < 1024. -/
def s2Row (j : Nat) : Nat :=
  (j % 4) * 64 + ((j / 4) % 4) * 256 +
  ((j / 16) % 4) * 16 + ((j / 64) % 4) +
  ((j / 256) % 4) * 4

def inactiveGroups : List Nat :=
  [0,1,2,3,4,5,5,6,4,5,5,5,7,7,7,7,7,7,7,4,4,5,5,6,4,5,5,5,7,7,7,4,
   7,7,7,7,4,5,5,5,4,5,5,5,8,9,10,8,11,2,2,10,4,5,5,6,4,5,5,6,7,7,7,7]

def inactiveMasks : List Nat :=
  [32769,49217,49280,16448,32767,16383,49151,65535,49152,57344,49216,33024]

def activeRowMasks : List Nat :=
  [6144,6144,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,
   6145,6145,6145,6145,6145,6145,6145,6145,6145,6144,4097,2048,6145,2049,2048,6145,
   2049,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,
   6145,6145,6145,6145,6145,4097,6145,6145,4097,26214,26214,26214,26214,26214,26214,1749]

def bitAt (mask bit : Nat) : Nat := (mask / 2^bit) % 2

def sourceInactive (row : Nat) : Nat :=
  1 - bitAt (activeRowMasks.getD (row / 16) 0) (row % 16)

def groupedInactive (j s : Nat) : Nat :=
  bitAt (inactiveMasks.getD (inactiveGroups.getD j 0) 0) s

/-- All 1024 cells of the current S3 lookup classify the same inactive bits as
`Variant::row` followed by `COPY_ACTIVE_ROW_MASKS`. -/
theorem s3_table_matches_source (j : Fin 64) (s : Fin 16) :
    groupedInactive j.val s.val = sourceInactive (s2Row (16*j.val+s.val)) := by
  fin_cases j <;> fin_cases s <;> decide

theorem group_table_bound (j : Fin 64) :
    inactiveGroups.getD j.val 0 < 12 := by
  fin_cases j <;> decide

/-- Every grouped lookup has in-range group and challenge indices; the
coefficient-to-source row is bounded by the R22 digit range. -/
theorem s3_group_ranges (j : Fin 64) (s : Fin 16) :
    inactiveGroups.getD j.val 0 < 12 ∧ s.val < 16 ∧ 16*j.val+s.val < 1024 := by
  have h := AspisR1.R22ControlBounds.weights_digits j.val s.val j.isLt s.isLt
  exact ⟨group_table_bound j, s.isLt, h⟩

open AspisR1.S2LibraFactoredIdentity

/-- The indexed reference and factored S9 weights are the exact current
source-shaped terms. `source_scaled_eq` proves all four outputs, including
zero extra challenges, for arbitrary coefficient/challenge arrays. -/
theorem s9_source_weights_equal {E : Type} [CommSemiring E]
    (p0 p1 : Fin 4 → E) (quarter q0 q1 : E) (j : Fin 4) :
    original (scaled p0 quarter) (scaled p1 quarter) q0 q1 j =
      factored (scaled p0 quarter) (scaled p1 quarter) q0 q1 j :=
  source_scaled_eq p0 p1 quarter q0 q1 j

/-- The old 56-cell loop's index split is within the R22 range owner. -/
theorem s9_index_ranges (index : Nat) (h : index < 56) :
    index / 28 < 2 ∧ index % 28 < 28 :=
  AspisR1.R22ControlBounds.libra_indices index h

#print axioms s3_table_matches_source
#print axioms s3_group_ranges
#print axioms s9_source_weights_equal
#print axioms s9_index_ranges
end AspisR1.S3S9CurrentSourceModel
