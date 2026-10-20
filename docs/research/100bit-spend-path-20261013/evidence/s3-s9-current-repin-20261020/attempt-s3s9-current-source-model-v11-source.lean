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

theorem group_table_bound (j : Fin 64) :
    inactiveGroups.getD j.val 0 < 12 := by
  fin_cases j <;> decide

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

def oldS9Low {E : Type} [CommSemiring E]
    (p0 p1 : Fin 4 → E) (quarter : E) (s : Fin 16) : E :=
  p0 (AspisR1.S2LibraFactoredIdentity.perm ⟨s.val % 4, Nat.mod_lt _ (by decide)⟩) *
    p1 (AspisR1.S2LibraFactoredIdentity.perm ⟨s.val / 4, by omega⟩) * quarter^2

def oldS9Weight {E : Type} [CommSemiring E]
    (p0 p1 : Fin 4 → E) (quarter q0 q1 : E) (j : Fin 4) : E :=
  ∑ s : Fin 16,
    let index := 16*j.val+s.val
    if index < 56 then
      oldS9Low p0 p1 quarter s *
        (if index < 28 then q0^(index%28) else q1^(index%28))
    else 0

theorem old_s9_weight_eq_reference {E : Type} [CommSemiring E]
    (p0 p1 : Fin 4 → E) (quarter q0 q1 : E) (j : Fin 4) :
    oldS9Weight p0 p1 quarter q0 q1 j =
      AspisR1.S2LibraFactoredIdentity.original
        (AspisR1.S2LibraFactoredIdentity.scaled p0 quarter)
        (AspisR1.S2LibraFactoredIdentity.scaled p1 quarter) q0 q1 j := by
  unfold oldS9Weight AspisR1.S2LibraFactoredIdentity.original
  apply Finset.sum_congr rfl
  intro s hs
  dsimp [oldS9Low]
  rw [AspisR1.S2LibraFactoredIdentity.low_scaled]
  simp [pow_two]

theorem old_s9_weight_eq_factored {E : Type} [CommSemiring E]
    (p0 p1 : Fin 4 → E) (quarter q0 q1 : E) (j : Fin 4) :
    oldS9Weight p0 p1 quarter q0 q1 j =
      AspisR1.S2LibraFactoredIdentity.factored
        (AspisR1.S2LibraFactoredIdentity.scaled p0 quarter)
        (AspisR1.S2LibraFactoredIdentity.scaled p1 quarter) q0 q1 j := by
  rw [old_s9_weight_eq_reference]
  exact AspisR1.S2LibraFactoredIdentity.source_scaled_eq p0 p1 quarter q0 q1 j

def groupedInactive (j s : Nat) : Nat :=
  bitAt (inactiveMasks.getD (inactiveGroups.getD j 0) 0) s

def groupAt (j : Fin 64) : Fin 12 :=
  ⟨inactiveGroups.getD j.val 0, group_table_bound j⟩

def inactiveAtSource (j : Fin 64) (s : Fin 16) : Bool :=
  decide (sourceInactive (s2Row (16*j.val+s.val)) = 1)

def inactiveAtGroup (g : Fin 12) (s : Fin 16) : Bool :=
  decide (bitAt (inactiveMasks.getD g.val 0) s.val = 1)

def ungroupedPair {E : Type} [CommSemiring E]
    (coeff : Fin 64 → E) (low : Fin 16 → E) (inactive : Fin 64 → Fin 16 → Bool) : E :=
  ∑ j : Fin 64, ∑ s : Fin 16,
    if inactive j s then coeff j * low s else 0

def groupedPair {E : Type} [CommSemiring E]
    (coeff : Fin 64 → E) (low : Fin 16 → E)
    (group : Fin 64 → Fin 12) (mask : Fin 12 → Fin 16 → Bool) : E :=
  ∑ g : Fin 12,
    (∑ j : Fin 64, if group j = g then coeff j else 0) *
    (∑ s : Fin 16, if mask g s then low s else 0)

theorem grouped_pair_eq_ungrouped_of_classification
    {E : Type} [CommSemiring E]
    (coeff : Fin 64 → E) (low : Fin 16 → E)
    (group : Fin 64 → Fin 12) (mask : Fin 12 → Fin 16 → Bool)
    (inactive : Fin 64 → Fin 16 → Bool)
    (hclass : ∀ j s, inactive j s = mask (group j) s) :
    groupedPair coeff low group mask = ungroupedPair coeff low inactive := by
  classical
  unfold groupedPair ungroupedPair
  calc
    (∑ g : Fin 12,
      (∑ j : Fin 64, if group j = g then coeff j else 0) *
      (∑ s : Fin 16, if mask g s then low s else 0))
      = ∑ j : Fin 64, ∑ g : Fin 12, ∑ s : Fin 16,
          (if group j = g then coeff j else 0) *
          (if mask g s then low s else 0) := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          calc
            _ = ∑ g : Fin 12, ∑ j : Fin 64, ∑ s : Fin 16,
                  (if group j = g then coeff j else 0) *
                  (if mask g s then low s else 0) := by
                    apply Finset.sum_congr rfl
                    intro g hg
                    exact Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
                      (f := fun s j =>
                        (if group j = g then coeff j else 0) *
                        (if mask g s then low s else 0))
            _ = ∑ j : Fin 64, ∑ g : Fin 12, ∑ s : Fin 16,
                  (if group j = g then coeff j else 0) *
                  (if mask g s then low s else 0) := by
                    exact Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
                      (f := fun g j =>
                        ∑ s : Fin 16,
                          (if group j = g then coeff j else 0) *
                          (if mask g s then low s else 0))
    _ = ∑ j : Fin 64, ∑ s : Fin 16, ∑ g : Fin 12,
          (if group j = g then coeff j else 0) *
          (if mask g s then low s else 0) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
            (f := fun g s =>
              (if group j = g then coeff j else 0) *
              (if mask g s then low s else 0))
    _ = ∑ j : Fin 64, ∑ s : Fin 16,
          if mask (group j) s then coeff j * low s else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro s hs
          have hsum :
              (∑ g : Fin 12,
                (if group j = g then coeff j else 0) *
                (if mask g s then low s else 0)) =
                (if mask (group j) s then coeff j * low s else 0) := by
            rw [Finset.sum_eq_single (group j)]
            · simp
            · intro g hg hne
              simp [Ne.symm hne]
            · simp
          exact hsum
    _ = ∑ j : Fin 64, ∑ s : Fin 16,
          if inactive j s then coeff j * low s else 0 := by
          simp_rw [← hclass]

/-- All 1024 cells of the current S3 lookup classify the same inactive bits as
`Variant::row` followed by `COPY_ACTIVE_ROW_MASKS`. -/
theorem s3_table_matches_source (j : Fin 64) (s : Fin 16) :
    groupedInactive j.val s.val = sourceInactive (s2Row (16*j.val+s.val)) := by
  fin_cases j <;> fin_cases s <;> decide

theorem s3_group_classification (j : Fin 64) (s : Fin 16) :
    inactiveAtSource j s = inactiveAtGroup (groupAt j) s := by
  unfold inactiveAtSource inactiveAtGroup
  rw [← s3_table_matches_source j s]
  simp [groupedInactive, groupAt, bitAt]

theorem s3_grouped_pair_exact {E : Type} [CommSemiring E]
    (coeff : Fin 64 → E) (low : Fin 16 → E) :
    groupedPair coeff low groupAt inactiveAtGroup =
      ungroupedPair coeff low inactiveAtSource := by
  apply grouped_pair_eq_ungrouped_of_classification
  intro j s
  exact s3_group_classification j s

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
#print axioms s3_group_classification
#print axioms s3_grouped_pair_exact
#print axioms s3_group_ranges
#print axioms s9_source_weights_equal
#print axioms s9_index_ranges
end AspisR1.S3S9CurrentSourceModel
