import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R754Point1GuardedTransport
import AspisV8R19.R752SharedWitnessPointSupport
import AspisV8R19.T163SourceTable
import AspisV8R19.TwoSwapSourceTable

namespace AspisR19.R754Point1GuardedLeaves
open AspisV8R16 AspisV8R17 AspisV8R19 AspisR19
open AspisR19.TwoSwapSourceTable
set_option maxRecDepth 4096
noncomputable section

lemma w_guarded_leaf_0320 :
    R748JointWitnessPointEntry.w 320 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨320, by omega⟩
  have ho : order j = (522 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (522 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (522 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (522 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0320
lemma w_guarded_leaf_0321 :
    R748JointWitnessPointEntry.w 321 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨321, by omega⟩
  have ho : order j = (523 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (523 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (523 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (523 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (523 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (523 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (523 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0321
lemma w_guarded_leaf_0322 :
    R748JointWitnessPointEntry.w 322 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨322, by omega⟩
  have ho : order j = (538 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (538 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (538 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (538 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0322
lemma w_guarded_leaf_0323 :
    R748JointWitnessPointEntry.w 323 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨323, by omega⟩
  have ho : order j = (539 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (539 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (539 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (539 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (539 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (539 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (539 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0323
lemma w_guarded_leaf_0324 :
    R748JointWitnessPointEntry.w 324 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨324, by omega⟩
  have ho : order j = (554 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (554 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (554 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (554 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0324
lemma w_guarded_leaf_0325 :
    R748JointWitnessPointEntry.w 325 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨325, by omega⟩
  have ho : order j = (555 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (555 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (555 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (555 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (555 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (555 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (555 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0325
lemma w_guarded_leaf_0326 :
    R748JointWitnessPointEntry.w 326 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨326, by omega⟩
  have ho : order j = (570 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (570 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (570 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (570 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0326
lemma w_guarded_leaf_0327 :
    R748JointWitnessPointEntry.w 327 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨327, by omega⟩
  have ho : order j = (571 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (571 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (571 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (571 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (571 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (571 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (571 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0327
lemma w_guarded_leaf_0328 :
    R748JointWitnessPointEntry.w 328 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨328, by omega⟩
  have ho : order j = (586 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (586 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (586 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (586 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0328
lemma w_guarded_leaf_0329 :
    R748JointWitnessPointEntry.w 329 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨329, by omega⟩
  have ho : order j = (587 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (587 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (587 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (587 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (587 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (587 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (587 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0329
lemma w_guarded_leaf_0330 :
    R748JointWitnessPointEntry.w 330 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨330, by omega⟩
  have ho : order j = (602 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (602 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (602 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (602 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0330
lemma w_guarded_leaf_0331 :
    R748JointWitnessPointEntry.w 331 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨331, by omega⟩
  have ho : order j = (603 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (603 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (603 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (603 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (603 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (603 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (603 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0331
lemma w_guarded_leaf_0332 :
    R748JointWitnessPointEntry.w 332 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨332, by omega⟩
  have ho : order j = (618 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (618 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (618 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (618 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0332
lemma w_guarded_leaf_0333 :
    R748JointWitnessPointEntry.w 333 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨333, by omega⟩
  have ho : order j = (619 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (619 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (619 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (619 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (619 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (619 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (619 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0333
lemma w_guarded_leaf_0334 :
    R748JointWitnessPointEntry.w 334 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨334, by omega⟩
  have ho : order j = (634 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (634 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (634 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (634 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0334
lemma w_guarded_leaf_0335 :
    R748JointWitnessPointEntry.w 335 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨335, by omega⟩
  have ho : order j = (635 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (635 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (635 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (635 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (635 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (635 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (635 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0335
lemma w_guarded_leaf_0336 :
    R748JointWitnessPointEntry.w 336 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨336, by omega⟩
  have ho : order j = (650 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (650 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (650 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (650 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0336
lemma w_guarded_leaf_0337 :
    R748JointWitnessPointEntry.w 337 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨337, by omega⟩
  have ho : order j = (651 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (651 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (651 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (651 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (651 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (651 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (651 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0337
lemma w_guarded_leaf_0338 :
    R748JointWitnessPointEntry.w 338 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨338, by omega⟩
  have ho : order j = (666 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (666 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (666 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (666 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0338
lemma w_guarded_leaf_0339 :
    R748JointWitnessPointEntry.w 339 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨339, by omega⟩
  have ho : order j = (667 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (667 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (667 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (667 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (667 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (667 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (667 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0339
lemma w_guarded_leaf_0340 :
    R748JointWitnessPointEntry.w 340 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨340, by omega⟩
  have ho : order j = (682 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (682 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (682 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (682 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0340
lemma w_guarded_leaf_0341 :
    R748JointWitnessPointEntry.w 341 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨341, by omega⟩
  have ho : order j = (683 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (683 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (683 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (683 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (683 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (683 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (683 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0341
lemma w_guarded_leaf_0342 :
    R748JointWitnessPointEntry.w 342 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨342, by omega⟩
  have ho : order j = (698 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (698 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (698 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (698 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0342
lemma w_guarded_leaf_0343 :
    R748JointWitnessPointEntry.w 343 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨343, by omega⟩
  have ho : order j = (699 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (699 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (699 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (699 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (699 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (699 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (699 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0343
lemma w_guarded_leaf_0344 :
    R748JointWitnessPointEntry.w 344 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨344, by omega⟩
  have ho : order j = (714 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (714 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (714 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (714 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0344
lemma w_guarded_leaf_0345 :
    R748JointWitnessPointEntry.w 345 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨345, by omega⟩
  have ho : order j = (715 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (715 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (715 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (715 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (715 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (715 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (715 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0345
lemma w_guarded_leaf_0346 :
    R748JointWitnessPointEntry.w 346 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨346, by omega⟩
  have ho : order j = (730 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (730 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (730 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (730 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0346
lemma w_guarded_leaf_0347 :
    R748JointWitnessPointEntry.w 347 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨347, by omega⟩
  have ho : order j = (731 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (731 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (731 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (731 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (731 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (731 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (731 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0347
lemma w_guarded_leaf_0348 :
    R748JointWitnessPointEntry.w 348 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨348, by omega⟩
  have ho : order j = (746 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (746 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (746 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (746 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0348
lemma w_guarded_leaf_0349 :
    R748JointWitnessPointEntry.w 349 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨349, by omega⟩
  have ho : order j = (747 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (747 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (747 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (747 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (747 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (747 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (747 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0349
lemma w_guarded_leaf_0350 :
    R748JointWitnessPointEntry.w 350 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨350, by omega⟩
  have ho : order j = (762 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (762 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (762 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (762 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0350
lemma w_guarded_leaf_0351 :
    R748JointWitnessPointEntry.w 351 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨351, by omega⟩
  have ho : order j = (763 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (763 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (763 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (763 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (763 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (763 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (763 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0351
end
end AspisR19.R754Point1GuardedLeaves
