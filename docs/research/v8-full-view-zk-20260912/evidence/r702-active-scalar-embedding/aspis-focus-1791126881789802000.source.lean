import AspisV8R19.R698ActiveCoreLayout
import AspisV8R19.R700ActiveBlockInverse
import AspisV8R19.SparseGPolynomial
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R702ActiveScalarEmbedding
open scoped BigOperators
open AspisV8R19.R698ActiveCoreLayout AspisV8R19.R700ActiveBlockInverse AspisR19.SparseGPolynomial AspisV8R17

abbrev I := Fin 1024
abbrev High := {i : I // i ∈ highActive}

variable {F : Type*} [CommRing F]

@[simp] def block (i : High) : Nat := i.val.val / 4
@[simp] def zero (i : High) : Prop := i.val.val % 4 = 0
local instance : DecidablePred zero := by
  intro i
  unfold zero
  infer_instance

def coeff (x : High → F) (n : Nat) : F :=
  ∑ i : High, if (selectedColumn i).val = n then x i else 0

def chosenQ (x : High → F) (r : Nat) : F :=
  if 22 ≤ r / 4 ∧ r / 4 < 255 then
    if r % 4 = 0 then
      -(∑ k : Fin 3, coeff x (3 * (r / 4 - 22) + k.val))
    else coeff x (3 * (r / 4 - 22) + (r % 4 - 1))
  else 0

lemma high_block_bounds (i : High) : 22 ≤ block i ∧ block i ≤ 254 := by
  have h := highActive_bounds i.val i.property
  constructor
  · exact (Nat.le_div_iff_mul_le (by omega : 0 < 4)).mpr (by omega)
  · exact (Nat.div_le_iff_le_mul (by omega : 0 < 4)).mpr (by omega)

lemma selectedColumn_val (i : High) :
    (selectedColumn i).val = 3 * (block i - 22) + selectedLocal i.val := rfl

lemma coeff_at_selected (x : High → F) (i : High) :
    coeff x (selectedColumn i).val = x i := by
  classical
  unfold coeff
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    by_cases hcol : (selectedColumn j).val = (selectedColumn i).val
    · exfalso
      apply hj
      exact selectedColumn_injective (Fin.ext hcol)
    · simp [hcol]
  · simp

lemma block_same_of_column_eq (i j : High) (k : Fin 3)
    (h : (selectedColumn i).val = 3 * (block j - 22) + k.val) :
    block i = block j := by
  rw [selectedColumn_val] at h
  have hi := high_block_bounds i
  have hj := high_block_bounds j
  have hl := selectedLocal_lt_three_all i.val
  omega

lemma local_eq_of_column_eq (i j : High) (k : Fin 3)
    (hb : block i = block j)
    (h : (selectedColumn i).val = 3 * (block j - 22) + k.val) :
    selectedLocal i.val = k.val := by
  rw [selectedColumn_val] at h
  omega

lemma sum_channels_block (x : High → F) (j : High) :
    (∑ k : Fin 3, coeff x (3 * (block j - 22) + k.val)) =
      ∑ i ∈ blockRows block j, x i := by
  classical
  unfold coeff
  rw [Finset.sum_comm]
  rw [show (∑ i ∈ blockRows block j, x i) = ∑ i : High,
      if block i = block j then x i else 0 by
        simp only [blockRows, Finset.sum_filter]]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hb : block i = block j
  · change i.val.val / 4 = j.val.val / 4 at hb
    let k0 : Fin 3 := ⟨selectedLocal i.val, selectedLocal_lt_three_all i.val⟩
    have hcol : (selectedColumn i).val = 3 * (block j - 22) + k0.val := by
      rw [selectedColumn_val]
      change 3 * (i.val.val / 4 - 22) + selectedLocal i.val =
        3 * (j.val.val / 4 - 22) + k0.val
      rw [hb]
    have hsum : (∑ k : Fin 3, if (selectedColumn i).val =
        3 * (block j - 22) + k.val then x i else 0) = x i := by
      rw [Finset.sum_eq_single k0]
      · simp [hcol]
      · intro k _ hk
        by_cases heq : (selectedColumn i).val = 3 * (block j - 22) + k.val
        · apply False.elim
          apply hk
          apply Fin.ext
          rw [selectedColumn_val] at heq
          change 3 * (i.val.val / 4 - 22) + selectedLocal i.val =
            3 * (j.val.val / 4 - 22) + k.val at heq
          rw [selectedColumn_val] at hcol
          change 3 * (i.val.val / 4 - 22) + selectedLocal i.val =
            3 * (j.val.val / 4 - 22) + k0.val at hcol
          rw [hb] at heq
          have hv : k.val = k0.val := by omega
          exact hv
        · change (if (selectedColumn i).val = 3 * (block j - 22) + k.val then x i else 0) = 0
          intro hh
          exfalso
          apply heq
          change (selectedColumn i).val = 3 * (j.val.val / 4 - 22) + k.val at heq
          exact hh
      · simp
    rw [hsum]
    simp [hb]
  · change ¬(i.val.val / 4 = j.val.val / 4) at hb
    have hzero : ∀ k : Fin 3, (if (selectedColumn i).val =
        3 * (block j - 22) + k.val then x i else 0) = 0 := by
      intro k
      split_ifs with h
      · exfalso
        apply hb
        exact block_same_of_column_eq i j k h
      · rfl
    have hsumzero : (∑ k : Fin 3, if (selectedColumn i).val =
        3 * (block j - 22) + k.val then x i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      exact hzero k
    rw [hsumzero]
    simp [hb]

lemma chosenQ_at_high (x : High → F) (i : High) :
    chosenQ x i.val.val = blockTransform block zero x i := by
  classical
  have hb := high_block_bounds i
  have hvalid : 22 ≤ i.val.val / 4 ∧ i.val.val / 4 < 255 := by
    change 22 ≤ block i ∧ block i < 255
    omega
  unfold chosenQ blockTransform
  rw [if_pos hvalid]
  by_cases hz : zero i
  · have hsum := sum_channels_block x i
    simp only [zero] at hz
    have hz' : i.val.val % 4 = 0 := by simpa [zero] using hz
    rw [if_pos hz']
    change -(∑ k : Fin 3, coeff x (3 * (block i - 22) + k.val)) = _
    rw [hsum]
    simp [zero, hz]
  · have hrem : i.val.val % 4 ≠ 0 := hz
    rw [if_neg hrem, if_neg hz]
    have hcol := coeff_at_selected x i
    rw [selectedColumn_val] at hcol
    have hsel := selectedLocal_nonzero i.val hrem
    rw [hsel] at hcol
    simpa using hcol

lemma zero_unique : ∀ i j : High, zero i → zero j → block i = block j → i = j := by
  intro i j hi hj hb
  apply Subtype.ext
  apply Fin.ext
  have hmi := Nat.mod_add_div i.val.val 4
  have hmj := Nat.mod_add_div j.val.val 4
  dsimp [zero, block] at hi hj hb
  omega

theorem high_block_involution (x : High → F) :
    blockTransform block zero (blockTransform block zero x) = x :=
  block_involution block zero zero_unique x

lemma coeff_extraTop_zero (x : High → F) : coeff x 697 = 0 := by
  classical
  unfold coeff
  apply Finset.sum_eq_zero
  intro i _
  split_ifs with h
  · exact False.elim (extraTopColumn_absent i (by apply Fin.ext; simpa [extraTopColumn] using h))
  · rfl

lemma chosenQ_1018_zero (x : High → F) : chosenQ x 1018 = 0 := by
  classical
  unfold chosenQ
  norm_num
  rw [coeff_extraTop_zero]

lemma chosenQ_top_zero (x : High → F) :
    chosenQ x 1020 = 0 ∧ chosenQ x 1021 = 0 ∧ chosenQ x 1022 = 0 ∧ chosenQ x 1023 = 0 := by
  unfold chosenQ
  norm_num

lemma scalar_chord_row (half : F) (x : High → F) (i : High) :
    sourceChord half (chosenQ x) 2 0 0 i.val.val =
      2 * blockTransform block zero x i := by
  by_cases hnt : Nontrivial F
  · letI : Nontrivial F := hnt
    rw [source_scalar half 2 (chosenQ x) i.val.val i.val.isLt]
    rw [chosenQ_at_high]
  · haveI : Subsingleton F := not_nontrivial_iff_subsingleton.mp hnt
    exact Subsingleton.elim _ _

#print axioms coeff_at_selected
#print axioms sum_channels_block
#print axioms chosenQ_at_high
#print axioms high_block_involution
#print axioms coeff_extraTop_zero
#print axioms chosenQ_1018_zero
#print axioms chosenQ_top_zero
#print axioms scalar_chord_row
end AspisV8R19.R702ActiveScalarEmbedding
