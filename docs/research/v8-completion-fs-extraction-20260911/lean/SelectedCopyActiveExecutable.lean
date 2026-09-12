import SelectedCopyActiveFlat

/-! Exact selected `selector_mask_sum_16` complement semantics and active sum.

This ports the generic executable proof from V7's
`NativePaymentCompiledActiveExecutableV1` but instantiates it with V8's
different literal `ACTIVE_ROW_MASKS`.  The observable set-bit scan is modeled
as its sorted set; addition/subtraction order is immaterial in a field. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
namespace AspisV8Completion.SelectedCopyActiveExecutable
open scoped BigOperators
open AspisV8.SelectedWeightedCopyRows
open AspisV8.SelectedSelectorExpansion
open AspisV8Completion.SelectedSelectorToSemanticWeight
open AspisV8Completion.SelectedCopyActiveFlat

variable {K : Type*} [Field K] [DecidableEq K]

def selectedMaskNat (block : Fin 64) : Nat := activeMasks.getD block.val 0

theorem selectedMaskNat_fit_u16 (block : Fin 64) :
    selectedMaskNat block < 2 ^ 16 := by
  fin_cases block <;> decide

def selectedMaskU16 (block : Fin 64) : Fin (2 ^ 16) :=
  ⟨selectedMaskNat block, selectedMaskNat_fit_u16 block⟩

def u16SetBits (mask : Fin (2 ^ 16)) : Finset (Fin 16) :=
  Finset.univ.filter fun slot => Nat.testBit mask.val slot.val

def u16Complement (mask : Fin (2 ^ 16)) : Fin (2 ^ 16) :=
  ⟨2 ^ 16 - (mask.val + 1), by omega⟩

theorem u16SetBits_complement (mask : Fin (2 ^ 16)) :
    u16SetBits (u16Complement mask) = Finset.univ \ u16SetBits mask := by
  ext slot
  simp only [u16SetBits, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_sdiff]
  rw [show (u16Complement mask).val = 2 ^ 16 - (mask.val + 1) by rfl,
    Nat.testBit_two_pow_sub_succ mask.isLt]
  simp [slot.isLt]

def rustSelectorMaskSum16 (values : Fin 16 → K)
    (mask : Fin (2 ^ 16)) : K :=
  if 8 < (u16SetBits mask).card then
    1 - ∑ slot ∈ u16SetBits (u16Complement mask), values slot
  else ∑ slot ∈ u16SetBits mask, values slot

theorem rustSelectorMaskSum16_eq_selected (values : Fin 16 → K)
    (mask : Fin (2 ^ 16)) (total : ∑ slot, values slot = 1) :
    rustSelectorMaskSum16 values mask =
      ∑ slot ∈ u16SetBits mask, values slot := by
  unfold rustSelectorMaskSum16
  split_ifs
  · rw [u16SetBits_complement]
    have partition := Finset.sum_sdiff (f := values)
      (Finset.subset_univ (u16SetBits mask))
    have all : ∑ slot ∈ (Finset.univ : Finset (Fin 16)), values slot = 1 := by
      simpa using total
    rw [all] at partition
    rw [← partition]
    ring
  · rfl

def selectedHighWeight (point : Fin 10 → K) (block : Fin 64) : K :=
  expand (pointNat point) 6 block.val

def selectedLowWeight (point : Fin 10 → K) (slot : Fin 16) : K :=
  expand (fun i => pointNat point (6 + i)) 4 slot.val

theorem selectedLowWeight_eq_product (point : Fin 10 → K) (slot : Fin 16) :
    selectedLowWeight point slot =
      ∏ coordinate : Fin 4,
        if Nat.testBit slot.val (3 - coordinate.val) then
          point ⟨6 + coordinate.val, by omega⟩
        else 1 - point ⟨6 + coordinate.val, by omega⟩ := by
  rw [selectedLowWeight, expand_product _ 4 slot.val (by omega)]
  unfold tensorProduct
  rw [Finset.prod_fin_eq_prod_range]
  apply Finset.prod_congr rfl
  intro coordinate membership
  have within : coordinate < 4 := Finset.mem_range.mp membership
  simp only [within, dite_true]
  have pointRange : 6 + coordinate < 10 := by omega
  rw [pointNat_inRange point (6 + coordinate) pointRange]
  unfold factor
  rfl

theorem selectedLowWeight_sum (point : Fin 10 → K) :
    ∑ slot : Fin 16, selectedLowWeight point slot = 1 := by
  simp_rw [selectedLowWeight_eq_product]
  norm_num [Fin.sum_univ_succ, Fin.prod_univ_succ,
    Nat.testBit_eq_decide_div_mod_eq]
  ring

def rowOfBlockLocal (block : Fin 64) (slot : Fin 16) : Fin 1024 :=
  ⟨slot.val + 16 * block.val, by omega⟩

@[simp] theorem rowOfBlockLocal_val (block : Fin 64) (slot : Fin 16) :
    (rowOfBlockLocal block slot).val = slot.val + 16 * block.val := rfl

theorem rowActive_rowOfBlockLocal (block : Fin 64) (slot : Fin 16) :
    rowActive (rowOfBlockLocal block slot) ↔
      Nat.testBit (selectedMaskNat block) slot.val = true := by
  unfold rowActive selectedMaskNat
  rw [rowOfBlockLocal_val]
  have quotient : (slot.val + 16 * block.val) / 16 = block.val := by omega
  have remainder : (slot.val + 16 * block.val) % 16 = slot.val := by omega
  rw [quotient, remainder]

theorem selectedSelector_rowOfBlockLocal (point : Fin 10 → K)
    (block : Fin 64) (slot : Fin 16) :
    selectedSelector (pointNat point) (rowOfBlockLocal block slot).val =
      selectedHighWeight point block * selectedLowWeight point slot := by
  unfold selectedSelector selectedHighWeight selectedLowWeight
  rw [rowOfBlockLocal_val]
  have quotient : (slot.val + 16 * block.val) / 16 = block.val := by omega
  have remainder : (slot.val + 16 * block.val) % 16 = slot.val := by omega
  rw [Nat.shiftRight_eq_div_pow]
  norm_num only [pow_succ, pow_zero, mul_one]
  have andMask : (slot.val + 16 * block.val) &&& 15 =
      (slot.val + 16 * block.val) % 16 := by
    simpa using Nat.and_two_pow_sub_one_eq_mod (slot.val + 16 * block.val) 4
  rw [quotient, andMask, remainder]

noncomputable def rustSelectedCopyActive (point : Fin 10 → K) : K :=
  ∑ block : Fin 64,
    if selectedMaskNat block = 0 then 0
    else selectedHighWeight point block *
      rustSelectorMaskSum16 (selectedLowWeight point) (selectedMaskU16 block)

theorem rustSelectedCopyActive_eq_sourceActiveFlat (point : Fin 10 → K) :
    rustSelectedCopyActive point = sourceActiveFlat point := by
  classical
  unfold rustSelectedCopyActive sourceActiveFlat activeIndicator
  calc
    (∑ block : Fin 64,
      if selectedMaskNat block = 0 then 0
      else selectedHighWeight point block *
        rustSelectorMaskSum16 (selectedLowWeight point) (selectedMaskU16 block)) =
      ∑ block : Fin 64, ∑ slot : Fin 16,
        if Nat.testBit (selectedMaskNat block) slot.val then
          selectedHighWeight point block * selectedLowWeight point slot else 0 := by
      apply Finset.sum_congr rfl
      intro block _
      rw [rustSelectorMaskSum16_eq_selected _ _ (selectedLowWeight_sum point)]
      unfold u16SetBits
      rw [Finset.mul_sum]
      simp only [Finset.sum_filter, Finset.mem_univ, selectedMaskU16, true_and]
      by_cases zeroMask : selectedMaskNat block = 0
      · simp [zeroMask]
      · rw [if_neg zeroMask]
    _ = ∑ pair : Fin 64 × Fin 16,
        if rowActive (rowOfBlockLocal pair.1 pair.2) then
          selectedSelector (pointNat point) (rowOfBlockLocal pair.1 pair.2).val
        else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro block _
      apply Finset.sum_congr rfl
      intro slot _
      rw [selectedSelector_rowOfBlockLocal]
      by_cases active : Nat.testBit (selectedMaskNat block) slot.val
      · have sourceActive : rowActive (rowOfBlockLocal block slot) :=
          (rowActive_rowOfBlockLocal block slot).2 active
        simp [active, sourceActive]
      · have sourceInactive : ¬rowActive (rowOfBlockLocal block slot) := by
          intro contradiction
          exact active ((rowActive_rowOfBlockLocal block slot).1 contradiction)
        simp [active, sourceInactive]
    _ = ∑ row : Fin 1024,
        (if rowActive row then selectedSelector (pointNat point) row.val else 0) :=
      (finProdFinEquiv : Fin 64 × Fin 16 ≃ Fin 1024).sum_comp
        (fun row => if rowActive row then selectedSelector (pointNat point) row.val else 0)
    _ = ∑ row : Fin 1024,
        selectedSelector (pointNat point) row.val *
          (if rowActive row then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro row _
      by_cases active : rowActive row <;> simp [active]

#print axioms selectedMaskNat_fit_u16
#print axioms u16SetBits_complement
#print axioms rustSelectorMaskSum16_eq_selected
#print axioms selectedLowWeight_sum
#print axioms selectedSelector_rowOfBlockLocal
#print axioms rustSelectedCopyActive_eq_sourceActiveFlat
end AspisV8Completion.SelectedCopyActiveExecutable
