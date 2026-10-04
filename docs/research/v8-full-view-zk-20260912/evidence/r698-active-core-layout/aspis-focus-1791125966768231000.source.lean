import AspisV8R19.TwoSwapSourceTable
import Mathlib.Tactic

/-! Literal finite layout facts for the active H1 core route.
No field entry, rank, determinant, or source-execution theorem appears here. -/
set_option autoImplicit false
set_option maxRecDepth 32768
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
  by_cases h0 : j.val % 4 = 0
  · by_cases h1 : blockActive j 1 = true
    · by_cases h2 : blockActive j 2 = true <;> simp [selectedLocal, h0, h1, h2]
    · simp [selectedLocal, h0, h1]
  · have hm : j.val % 4 < 4 := Nat.mod_lt _ (by decide)
    simp [selectedLocal, h0]
    omega

/-- This is the sole small table check used to exclude the lower padding. -/
theorem no_active_below_88 (j : Fin 88) :
    (⟨j.val, by omega⟩ : I) ∉ activeCode := by
  revert j
  decide

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

def extraTopColumn : Fin 699 := ⟨697, by omega⟩

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
    have hcases : j.val = 1020 ∨ j.val = 1021 ∨ j.val = 1022 ∨ j.val = 1023 := by omega
    rcases hcases with h | h | h | h
    · exfalso
      have he : j = (1020 : I) := Fin.ext h
      have hno : (1020 : I) ∉ activeCode := by decide
      exact hno (by simpa [he] using hj)
    · exfalso
      have he : j = (1021 : I) := Fin.ext h
      have hno : (1021 : I) ∉ activeCode := by decide
      exact hno (by simpa [he] using hj)
    · exact Fin.ext h
    · exfalso
      have he : j = (1023 : I) := Fin.ext h
      have hno : (1023 : I) ∉ activeCode := by decide
      exact hno (by simpa [he] using hj)
  · intro h
    subst j
    decide

/-- No high four-slot block has all four source rows active. -/
theorem high_block_not_full (b : Fin 233) :
    ¬ ∀ s : Fin 4, highRow b s ∈ activeCode := by
  revert b
  decide

theorem selectedLocal_nonzero (j : I) (hs : j.val % 4 ≠ 0) :
    selectedLocal j = j.val % 4 - 1 := by simp [selectedLocal, hs]

lemma blockActive_of_same_block (j k : I) (hk : k ∈ highActive)
    (hdiv : j.val / 4 = k.val / 4) :
    blockActive j ⟨k.val % 4, by omega⟩ = true := by
  have ha : isInactive (order k) = false := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
  have he : (⟨4 * (j.val / 4) + k.val % 4, by omega⟩ : I) = k := by
    apply Fin.ext
    rw [hdiv]
    simpa [Nat.add_comm] using (Nat.mod_add_div k.val 4)
  simp [blockActive, he, ha]

lemma selectedLocal_zero_missing (j : I) (hj : j ∈ highActive)
    (hzero : j.val % 4 = 0) :
    blockActive j ⟨selectedLocal j + 1, by
      have := selectedLocal_lt_three_all j
      omega⟩ = false := by
  have hbounds := highActive_bounds j hj
  have hactive0 : blockActive j ⟨0, by omega⟩ = true := by
    have h := blockActive_of_same_block j j hj rfl
    simpa [hzero] using h
  by_cases h1 : blockActive j ⟨1, by omega⟩ = true
  · by_cases h2 : blockActive j ⟨2, by omega⟩ = true
    · have h3 : blockActive j ⟨3, by omega⟩ = false := by
        by_cases h3t : blockActive j ⟨3, by omega⟩ = true
        · let b : Fin 233 := ⟨j.val / 4 - 22, by
            have hlo : 22 ≤ j.val / 4 :=
              (Nat.le_div_iff_mul_le (by omega : 0 < 4)).mpr (by omega)
            have hhi : j.val / 4 ≤ 254 :=
              (Nat.div_le_iff_le_mul (by omega : 0 < 4)).mpr (by omega)
            omega⟩
          have hnot := high_block_not_full b
          exfalso
          apply hnot
          intro s
          have hm : isInactive (order (⟨4 * (j.val / 4) + s.val, by omega⟩ : I)) = false := by
            fin_cases s
            · simpa [blockActive] using hactive0
            · simpa [blockActive] using h1
            · simpa [blockActive] using h2
            · simpa [blockActive] using h3t
          apply Finset.mem_filter.mpr
          constructor
          · exact Finset.mem_univ _
          · change isInactive (order (highRow b s)) = false
            have he : highRow b s = (⟨4 * (j.val / 4) + s.val, by omega⟩ : I) := by
              apply Fin.ext
              dsimp [highRow, b]
              omega
            rw [he]
            exact hm
        · cases h3b : blockActive j ⟨3, by omega⟩ <;> simp_all
      have hsel : selectedLocal j = 2 := by simp [selectedLocal, hzero, h1, h2]
      rw [hsel]
      simpa using h3
    · have h2f : blockActive j ⟨2, by omega⟩ = false := by
        cases h2b : blockActive j ⟨2, by omega⟩ <;> simp_all
      have hsel : selectedLocal j = 1 := by simp [selectedLocal, hzero, h1, h2f]
      rw [hsel]
      simpa using h2f
  · have h1f : blockActive j ⟨1, by omega⟩ = false := by
      cases h1b : blockActive j ⟨1, by omega⟩ <;> simp_all
    have hsel : selectedLocal j = 0 := by simp [selectedLocal, hzero, h1f]
    rw [hsel]
    simpa using h1f

/-- The chosen 213 high channels are pairwise distinct. -/
theorem selectedColumn_injective : Function.Injective selectedColumn := by
  intro x y h
  have hx := highActive_bounds x.val x.property
  have hy := highActive_bounds y.val y.property
  have hlx := selectedLocal_lt_three_all x.val
  have hly := selectedLocal_lt_three_all y.val
  have hh := congrArg Fin.val h
  change 3 * (x.val.val / 4 - 22) + selectedLocal x.val =
    3 * (y.val.val / 4 - 22) + selectedLocal y.val at hh
  have hdiv : x.val.val / 4 = y.val.val / 4 := by omega
  have hsx : x.val.val % 4 = y.val.val % 4 := by
    by_cases xzero : x.val.val % 4 = 0
    · by_cases yzero : y.val.val % 4 = 0
      · omega
      · have hselx := selectedLocal_zero_missing x.val x.property xzero
        have hsely := selectedLocal_nonzero y.val yzero
        have hloc : selectedLocal x.val = selectedLocal y.val := by omega
        have hba := blockActive_of_same_block x.val y.val y.property hdiv
        have hslotval : selectedLocal x.val + 1 = y.val.val % 4 := by
          rw [hloc, hsely]
          omega
        have hfalse : blockActive x.val ⟨y.val.val % 4, by omega⟩ = false := by
          simpa [hslotval] using hselx
        rw [hba] at hfalse
        contradiction
    · by_cases yzero : y.val.val % 4 = 0
      · have hsely := selectedLocal_zero_missing y.val y.property yzero
        have hselx := selectedLocal_nonzero x.val xzero
        have hloc : selectedLocal x.val = selectedLocal y.val := by omega
        have hba := blockActive_of_same_block y.val x.val x.property hdiv.symm
        have hslotval : selectedLocal y.val + 1 = x.val.val % 4 := by
          rw [← hloc, hselx]
          omega
        have hfalse : blockActive y.val ⟨x.val.val % 4, by omega⟩ = false := by
          simpa [hslotval] using hsely
        rw [hba] at hfalse
        contradiction
      · rw [selectedLocal_nonzero x.val xzero, selectedLocal_nonzero y.val yzero] at hh
        omega
  apply Subtype.ext
  apply Fin.ext
  omega

theorem selectedColumn_bound (j : I) (hj : j ∈ highActive) :
    (selectedColumn ⟨j,hj⟩).val < 699 := (selectedColumn ⟨j,hj⟩).isLt

theorem block254_active_slots (s : Fin 4) :
    highRow ⟨232, by omega⟩ s ∈ activeCode ↔ s = 1 ∨ s = 3 := by
  revert s
  decide

theorem extraTopColumn_absent (j : highActive) :
    selectedColumn j ≠ extraTopColumn := by
  have hj := highActive_bounds j.val j.property
  have hl := selectedLocal_lt_three_all j.val
  intro h
  have hh := congrArg Fin.val h
  change 3 * (j.val.val / 4 - 22) + selectedLocal j.val = 697 at hh
  have hd : j.val.val / 4 = 254 := by omega
  have hloc : selectedLocal j.val = 1 := by omega
  have ha0 : j.val ∈ activeCode := (Finset.mem_filter.mp j.property).1
  let s : Fin 4 := ⟨j.val.val % 4, by omega⟩
  have heq : highRow ⟨232, by omega⟩ s = j.val := by
    apply Fin.ext
    dsimp [highRow, s]
    omega
  have ha : highRow ⟨232, by omega⟩ s ∈ activeCode := by
    rw [heq]
    exact ha0
  have hs := (block254_active_slots s).mp ha
  rcases hs with hs | hs
  · have hrem : j.val.val % 4 = 1 := by
      have := congrArg Fin.val hs
      simpa [s] using this
    have hn : j.val.val % 4 ≠ 0 := by omega
    rw [selectedLocal_nonzero j.val hn] at hloc
    omega
  · have hrem : j.val.val % 4 = 3 := by
      have := congrArg Fin.val hs
      simpa [s] using this
    have hn : j.val.val % 4 ≠ 0 := by omega
    rw [selectedLocal_nonzero j.val hn] at hloc
    omega

#print axioms activeCode_card
#print axioms highActive_card
#print axioms active_outside_high
#print axioms high_block_not_full
#print axioms selectedColumn_injective
#print axioms block254_active_slots
#print axioms extraTopColumn_absent
end AspisV8R19.R698ActiveCoreLayout
