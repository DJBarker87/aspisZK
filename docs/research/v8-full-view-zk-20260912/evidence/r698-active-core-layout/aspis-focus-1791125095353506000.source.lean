import AspisV8R19.TwoSwapSourceTable
import Mathlib.Tactic

/-! Literal finite layout facts for the active H1 core route.
No field entry, rank, determinant, or source-execution theorem appears here. -/
set_option autoImplicit false
namespace AspisV8R19.R698ActiveCoreLayout
open scoped BigOperators
open AspisR19.TwoSwapSourceTable

abbrev I := Fin 1024

/-- Source-code rows whose TwoSwap code position is active. -/
def activeCode : Finset I :=
  Finset.univ.filter (fun j => isInactive (order j) = false)

/-- The 233 four-slot high blocks, represented by source rows below 1020. -/
def highActive : Finset I := activeCode.filter (fun j => j.val < 1020)

/-- The source row in high block `d=22+b`, at its local slot. -/
def highRow (b : Fin 233) (s : Fin 4) : I :=
  ⟨4 * (22 + b.val) + s.val, by omega⟩

/-- Whether a local slot of the high block containing `j` is active. -/
def blockActive (j : I) (s : Fin 4) : Bool :=
  isInactive (order ⟨4 * (j.val / 4) + s.val, by omega⟩) = false

/-- A high nonconstant channel.  Channel `0,1,2` means source q slots `1,2,3`. -/
def selectedLocal (j : I) : Nat :=
  if j.val % 4 = 0 then
    if blockActive j 1 then
      if blockActive j 2 then 2 else 1
    else 0
  else j.val % 4 - 1

/-- The selected direct quotient channel in the 699-dimensional high section.
Outside the high range this harmlessly returns zero; all use below is restricted
to `highActive`. -/
def selectedColumn (j : I) : Fin 699 :=
  if h : 88 ≤ j.val ∧ j.val < 1020 then
    ⟨3 * (j.val / 4 - 22) + selectedLocal j, by omega⟩
  else 0

/-- The unused third channel in block 254, i.e. source q index 1018. -/
def extraTopColumn : Fin 699 := ⟨698, by omega⟩

/-- The literal active-table count. -/
theorem activeCode_card : activeCode.card = 214 := by decide

theorem highActive_card : highActive.card = 213 := by decide

theorem active_outside_high (j : I) (hj : j ∈ activeCode) :
    j ∉ highActive ↔ j = (1022 : I) := by decide

theorem highActive_bounds (j : I) (hj : j ∈ highActive) :
    88 ≤ j.val ∧ j.val < 1020 := by decide

/-- No high four-slot block has all four source rows active. -/
theorem high_block_not_full (b : Fin 233) :
    ¬ ∀ s : Fin 4, highRow b s ∈ activeCode := by decide

/-- A selected active row uses a valid nonconstant local channel. -/
theorem selectedLocal_lt_three (j : I) (hj : j ∈ highActive) :
    selectedLocal j < 3 := by decide

/-- If the active row itself is nonconstant, it selects its own channel. -/
theorem selectedLocal_nonzero (j : I) (hj : j ∈ highActive)
    (hs : j.val % 4 ≠ 0) : selectedLocal j = j.val % 4 - 1 := by
  simp [selectedLocal, hs]

/-- A selected slot-zero row selects a nonconstant slot which is not active in
its source block. -/
theorem selectedLocal_zero_missing (j : I) (hj : j ∈ highActive)
    (hzero : j.val % 4 = 0) :
    blockActive j ⟨selectedLocal j + 1, by
      have := selectedLocal_lt_three j hj
      omega⟩ = false := by decide

/-- The chosen 213 high channels are pairwise distinct. -/
theorem selectedColumn_injective :
    Function.Injective (fun j : highActive => selectedColumn j.val) := by decide

theorem selectedColumn_bound (j : I) (hj : j ∈ highActive) :
    (selectedColumn j).val < 699 := (selectedColumn j).isLt

/-- Block 254 has exactly active source slots 1 and 3. -/
theorem block254_active_slots (s : Fin 4) :
    highRow ⟨232, by omega⟩ s ∈ activeCode ↔ s = 1 ∨ s = 3 := by decide

/-- Channel two of block 254 (source q[1018]) is unused by the 213 selected
high rows. -/
theorem extraTopColumn_absent (j : highActive) :
    selectedColumn j.val ≠ extraTopColumn := by decide

#print axioms activeCode_card
#print axioms highActive_card
#print axioms active_outside_high
#print axioms high_block_not_full
#print axioms selectedLocal_zero_missing
#print axioms selectedColumn_injective
#print axioms block254_active_slots
#print axioms extraTopColumn_absent
end AspisV8R19.R698ActiveCoreLayout
