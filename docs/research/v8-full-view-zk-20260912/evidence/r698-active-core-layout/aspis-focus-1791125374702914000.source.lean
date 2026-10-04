import AspisV8R19.TwoSwapSourceTable
import Mathlib.Tactic

/-! Literal finite layout facts for the active H1 core route.
No field entry, rank, determinant, or source-execution theorem appears here. -/
set_option autoImplicit false
namespace AspisV8R19.R698ActiveCoreLayout
open AspisR19.TwoSwapSourceTable

abbrev I := Fin 1024

def activeCode : Finset I :=
  Finset.univ.filter (fun j => isInactive (order j) = false)

def highActive : Finset I := activeCode.filter (fun j => j.val < 1020)

def highRow (b : Fin 233) (s : Fin 4) : I :=
  ⟨4 * (22 + b.val) + s.val, by omega⟩

def blockActive (j : I) (s : Fin 4) : Bool :=
  isInactive (order ⟨4 * (j.val / 4) + s.val, by omega⟩) = false

def selectedLocal (j : I) : Nat :=
  if j.val % 4 = 0 then
    if blockActive j 1 then
      if blockActive j 2 then 2 else 1
    else 0
  else j.val % 4 - 1

lemma selectedLocal_lt_three_all (j : I) : selectedLocal j < 3 := by
  unfold selectedLocal
  split <;> split <;> split <;> omega

/-- This is the sole small table check used to exclude the lower padding. -/
theorem no_active_below_88 (j : Fin 88) :
    (⟨j.val, by omega⟩ : I) ∉ activeCode := by decide

theorem highActive_bounds (j : I) (hj : j ∈ highActive) :
    88 ≤ j.val ∧ j.val < 1020 := by
  have ha : j ∈ activeCode := (Finset.mem_filter.mp hj).1
  have hu : j.val < 1020 := (Finset.mem_filter.mp hj).2
  constructor
  · by_contra hn
    have hs : j.val < 88 := by omega
    have hz := no_active_below_88 ⟨j.val, hs⟩
    apply hz
    simpa using ha
  · exact hu

def selectedColumn (j : {j : I // j ∈ highActive}) : Fin 699 :=
  ⟨3 * (j.val.val / 4 - 22) + selectedLocal j.val, by
    have hb := highActive_bounds j.val j.property
    have hl := selectedLocal_lt_three_all j.val
    omega⟩

def extraTopColumn : Fin 699 := ⟨698, by omega⟩

theorem activeCode_card : activeCode.card = 214 := by decide
theorem highActive_card : highActive.card = 213 := by decide

theorem active_outside_high (j : I) (hj : j ∈ activeCode) :
    j ∉ highActive ↔ j = (1022 : I) := by
  constructor
  · intro h
    have hge : 1020 ≤ j.val := by
      by_contra hn
      apply h
      exact Finset.mem_filter.mpr ⟨hj, by omega⟩
    interval_cases j.val <;> decide
  · intro h
    subst j
    decide

/-- No high four-slot block has all four source rows active. -/
theorem high_block_not_full (b : Fin 233) :
    ¬ ∀ s : Fin 4, highRow b s ∈ activeCode := by
  fin_cases b <;> decide

theorem selectedLocal_nonzero (j : I) (hs : j.val % 4 ≠ 0) :
    selectedLocal j = j.val % 4 - 1 := by simp [selectedLocal, hs]

lemma blockActive_of_same_block (j k : I) (hk : k ∈ highActive)
    (hdiv : j.val / 4 = k.val / 4) :
    blockActive j ⟨k.val % 4, by omega⟩ = true := by
  have ha : isInactive (order k) = false := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
  have he : 4 * (j.val / 4) + k.val % 4 = k.val := by omega
  simp only [blockActive, he, ha]

lemma selectedLocal_zero_missing (j : I) (hj : j ∈ highActive)
    (hzero : j.val % 4 = 0) :
    blockActive j ⟨selectedLocal j + 1, by
      have := selectedLocal_lt_three_all j
      omega⟩ = false := by
  unfold selectedLocal
  simp [hzero]

/-- The chosen 213 high channels are pairwise distinct. -/
theorem selectedColumn_injective : Function.Injective selectedColumn := by
  intro x y h
  have hx := highActive_bounds x.val x.property
  have hy := highActive_bounds y.val y.property
  have hlx := selectedLocal_lt_three_all x.val
  have hly := selectedLocal_lt_three_all y.val
  have hdiv : x.val.val / 4 = y.val.val / 4 := by
    change 3 * (x.val.val / 4 - 22) + selectedLocal x.val =
      3 * (y.val.val / 4 - 22) + selectedLocal y.val at h
    omega
  have hsx : x.val.val % 4 = y.val.val % 4 := by
    by_cases xzero : x.val.val % 4 = 0
    · by_cases yzero : y.val.val % 4 = 0
      · omega
      · have hselx := selectedLocal_zero_missing x.val x.property xzero
        have hsely := selectedLocal_nonzero y.val yzero
        have hloc : selectedLocal x.val = selectedLocal y.val := by
          change 3 * (x.val.val / 4 - 22) + selectedLocal x.val =
            3 * (y.val.val / 4 - 22) + selectedLocal y.val at h
          omega
        have hba := blockActive_of_same_block x.val y.val y.property hdiv
        have hslot : ⟨selectedLocal x.val + 1, by omega⟩ =
            ⟨y.val.val % 4, by omega⟩ := by
          apply Fin.ext
          rw [hloc, hsely]
          omega
        rw [hslot] at hselx
        omega
    · by_cases yzero : y.val.val % 4 = 0
      · have hsely := selectedLocal_zero_missing y.val y.property yzero
        have hselx := selectedLocal_nonzero x.val xzero
        have hloc : selectedLocal x.val = selectedLocal y.val := by
          change 3 * (x.val.val / 4 - 22) + selectedLocal x.val =
            3 * (y.val.val / 4 - 22) + selectedLocal y.val at h
          omega
        have hba := blockActive_of_same_block y.val x.val x.property hdiv.symm
        have hslot : ⟨selectedLocal y.val + 1, by omega⟩ =
            ⟨x.val.val % 4, by omega⟩ := by
          apply Fin.ext
          rw [← hloc, hselx]
          omega
        rw [hslot] at hsely
        omega
      · rw [selectedLocal_nonzero x.val xzero, selectedLocal_nonzero y.val yzero] at h
        omega
  apply Subtype.ext
  apply Fin.ext
  omega

theorem selectedColumn_bound (j : I) (hj : j ∈ highActive) :
    (selectedColumn ⟨j,hj⟩).val < 699 := (selectedColumn ⟨j,hj⟩).isLt

theorem block254_active_slots (s : Fin 4) :
    highRow ⟨232, by omega⟩ s ∈ activeCode ↔ s = 1 ∨ s = 3 := by
  fin_cases s <;> decide

theorem extraTopColumn_absent (j : highActive) :
    selectedColumn j ≠ extraTopColumn := by
  have hj := highActive_bounds j.val j.property
  have hl := selectedLocal_lt_three_all j.val
  intro h
  change 3 * (j.val.val / 4 - 22) + selectedLocal j.val = 698 at h
  have hd : j.val.val / 4 = 254 := by omega
  have hs : j.val.val % 4 = 2 := by omega
  have ha : highRow ⟨232, by omega⟩ ⟨2, by omega⟩ ∈ activeCode := by
    change j.val ∈ activeCode
    apply Fin.ext
    omega
  have hslot := block254_active_slots ⟨2, by omega⟩
  omega

#print axioms activeCode_card
#print axioms highActive_card
#print axioms active_outside_high
#print axioms high_block_not_full
#print axioms selectedColumn_injective
#print axioms block254_active_slots
#print axioms extraTopColumn_absent
end AspisV8R19.R698ActiveCoreLayout
