import AspisV8R19.R702ActiveScalarEmbedding
import AspisV8R19.R706ExtraActiveColumn
import AspisV8R17.WeightedScatter
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R709ChosenColumnBasis
open scoped BigOperators
open AspisV8R19.R698ActiveCoreLayout AspisV8R19.R702ActiveScalarEmbedding
open AspisV8R19.R706ExtraActiveColumn AspisR19.SparseGPolynomial AspisV8R17

variable {F : Type*} [CommRing F]

lemma coeff_single (j : R702ActiveScalarEmbedding.High) (n : Nat) :
    coeff (Pi.single j (1:F)) n = if (selectedColumn j).val = n then 1 else 0 := by
  classical
  unfold coeff
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hne
    simp [Pi.single_apply, hne]
  · simp

theorem chosenQ_single_basis (j : R702ActiveScalarEmbedding.High) (r : Nat) :
    chosenQ (Pi.single j (1:F)) r =
      AspisV8R17.unitVector (4 * (22 + (selectedColumn j).val / 3) +
        (1 + (selectedColumn j).val % 3)) r -
      AspisV8R17.unitVector (4 * (22 + (selectedColumn j).val / 3)) r := by
  classical
  let n := (selectedColumn j).val
  let b := block j
  let l := selectedLocal j.val
  let base := 4 * (22 + n / 3)
  let slot := 1 + n % 3
  change chosenQ (Pi.single j (1:F)) r =
    AspisV8R17.unitVector (base + slot) r - AspisV8R17.unitVector base r
  have hb := high_block_bounds j
  have hl := selectedLocal_lt_three_all j.val
  have hn : n = 3 * (b - 22) + l := by
    dsimp [n,b,l]
    exact selectedColumn_val j
  have hdiv : n / 3 = b - 22 := by rw [hn]; omega
  have hmod : n % 3 = l := by rw [hn]; omega
  have hbase : base = 4 * b := by dsimp [base]; rw [hdiv]; omega
  have hslot : slot = l + 1 := by dsimp [slot]; rw [hmod]; omega
  have hwindow : 22 ≤ base / 4 ∧ base / 4 < 255 := by
    rw [hbase]
    constructor <;> simp [Nat.mul_div_right] <;> omega
  have hcoeff (k : Fin 3) :
      coeff (Pi.single j (1:F)) (3 * (b - 22) + k.val) =
        if k.val = l then 1 else 0 := by
    rw [coeff_single]
    rw [selectedColumn_val]
    change (if 3 * (b - 22) + l = 3 * (b - 22) + k.val then (1:F) else 0) = _
    split_ifs <;> congr 1 <;> omega
  have hrow0 : r % 4 = 0 →
      (∑ k : Fin 3, coeff (Pi.single j (1:F)) (3 * (r / 4 - 22) + k.val)) =
        (if r / 4 = b then 1 else 0) := by
    intro hr
    by_cases hdivr : r / 4 = b
    · have harg : r / 4 - 22 = b - 22 := by omega
      rw [harg]
      have hs : (∑ k : Fin 3, if k.val = l then (1:F) else 0) = 1 := by
        rw [Finset.sum_eq_single ⟨l, hl⟩]
        · simp
        · intro k hk hne
          have : k.val ≠ l := by intro he; apply hne; exact Fin.ext he
          simp [this]
        · simp
      calc
        (∑ k : Fin 3, coeff (Pi.single j (1:F)) (3 * (b - 22) + k.val)) =
            ∑ k : Fin 3, if k.val = l then (1:F) else 0 := by
              apply Finset.sum_congr rfl
              intro k hk
              exact hcoeff k
        _ = 1 := hs
        _ = if r / 4 = b then 1 else 0 := by simp [hdivr]
    · have hz : ∀ k : Fin 3,
        coeff (Pi.single j (1:F)) (3 * (r / 4 - 22) + k.val) = 0 := by
        intro k
        rw [coeff_single]
        rw [selectedColumn_val]
        change (if 3 * (b - 22) + l = 3 * (r / 4 - 22) + k.val then (1:F) else 0) = 0
        have he : 3 * (b - 22) + l ≠ 3 * (r / 4 - 22) + k.val := by omega
        simp [he]
      rw [Finset.sum_eq_zero (by intro k hk; exact hz k)]
      simp [hdivr]
  -- Keep the table-index arithmetic symbolic; only the three local channels are summed.
  by_cases hvalid : 22 ≤ r / 4 ∧ r / 4 < 255
  · by_cases hzero : r % 4 = 0
    · have hsum := hrow0 hzero
      simp only [chosenQ, if_pos hvalid, if_pos hzero]
      rw [hsum]
      by_cases hrb : r / 4 = b
      · have hr : r = base := by rw [hbase]; have := Nat.mod_add_div r 4; omega
        simp [AspisV8R17.unitVector, hr, hslot]
      · have hrbase : r ≠ base := by intro h; rw [hbase] at h; have := Nat.mod_add_div r 4; omega
        have hrslot : r ≠ base + slot := by
          intro h
          rw [hbase, hslot] at h
          have hm := Nat.mod_add_div r 4
          omega
        simp [AspisV8R17.unitVector, hrbase, hrslot]
    · have hnonzero : r % 4 ≠ 0 := hzero
      have hchannel :
          3 * (r / 4 - 22) + (r % 4 - 1) = n ↔ r = base + slot := by
        rw [hn, hbase, hslot]
        constructor <;> intro hh <;> have hm := Nat.mod_add_div r 4 <;> omega
      simp only [chosenQ, if_pos hvalid, if_neg hzero]
      rw [coeff_single]
      have hchannel' : n = 3 * (r / 4 - 22) + (r % 4 - 1) ↔ r = base + slot := by
        rw [eq_comm]
        exact hchannel
      simp [AspisV8R17.unitVector, hnonzero, hchannel']
  · have hrbase : r ≠ base := by
      intro he
      have hm := Nat.mod_add_div r 4
      have hb' : base / 4 = b := by rw [hbase]; omega
      have hsupp := hwindow.1
      rw [← he] at hsupp
      omega
    have hrslot : r ≠ base + slot := by
      intro he
      have hm := Nat.mod_add_div r 4
      have hb' : base / 4 = b := by rw [hbase]; omega
      have hsupp := hwindow.2
      rw [← he, hbase, hslot] at hsupp
      omega
    simp only [chosenQ, if_neg hvalid]
    simp [AspisV8R17.unitVector, hrbase, hrslot]

theorem extraQ_basis (r : Nat) :
    extraQ (F:=F) r = AspisV8R17.unitVector 1018 r - AspisV8R17.unitVector 1016 r := by
  simp only [extraQ, AspisV8R17.unitVector]
  split_ifs <;> norm_num <;> omega

#print axioms coeff_single
#print axioms chosenQ_single_basis
#print axioms extraQ_basis
end AspisV8R19.R709ChosenColumnBasis
