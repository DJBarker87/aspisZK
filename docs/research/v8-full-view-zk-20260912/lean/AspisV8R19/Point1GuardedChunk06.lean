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

lemma w_guarded_leaf_0384 :
    R748JointWitnessPointEntry.w 384 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨384, by omega⟩
  have ho : order j = (8 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (8 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (8 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (8 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0384
lemma w_guarded_leaf_0385 :
    R748JointWitnessPointEntry.w 385 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨385, by omega⟩
  have ho : order j = (9 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (9 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (9 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (9 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0385
lemma w_guarded_leaf_0386 :
    R748JointWitnessPointEntry.w 386 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨386, by omega⟩
  have ho : order j = (24 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (24 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (24 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (24 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0386
lemma w_guarded_leaf_0448 :
    R748JointWitnessPointEntry.w 448 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨448, by omega⟩
  have ho : order j = (520 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (520 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (520 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (520 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0448
lemma w_guarded_leaf_0449 :
    R748JointWitnessPointEntry.w 449 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨449, by omega⟩
  have ho : order j = (521 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (521 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (521 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (521 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0449
lemma w_guarded_leaf_0450 :
    R748JointWitnessPointEntry.w 450 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨450, by omega⟩
  have ho : order j = (536 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (536 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (536 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (536 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0450
lemma w_guarded_leaf_0512 :
    R748JointWitnessPointEntry.w 512 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨512, by omega⟩
  have ho : order j = (6 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (6 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (6 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (6 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0512
lemma w_guarded_leaf_0513 :
    R748JointWitnessPointEntry.w 513 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨513, by omega⟩
  have ho : order j = (7 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (7 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (7 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (7 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0513
lemma w_guarded_leaf_0514 :
    R748JointWitnessPointEntry.w 514 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨514, by omega⟩
  have ho : order j = (22 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (22 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (22 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (22 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0514
lemma w_guarded_leaf_0576 :
    R748JointWitnessPointEntry.w 576 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨576, by omega⟩
  have ho : order j = (518 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (518 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (518 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (518 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0576
lemma w_guarded_leaf_0577 :
    R748JointWitnessPointEntry.w 577 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨577, by omega⟩
  have ho : order j = (519 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (519 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (519 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (519 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0577
lemma w_guarded_leaf_0578 :
    R748JointWitnessPointEntry.w 578 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨578, by omega⟩
  have ho : order j = (534 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (534 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (534 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (534 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0578
lemma w_guarded_leaf_0640 :
    R748JointWitnessPointEntry.w 640 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨640, by omega⟩
  have ho : order j = (4 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (4 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (4 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (4 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0640
lemma w_guarded_leaf_0641 :
    R748JointWitnessPointEntry.w 641 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨641, by omega⟩
  have ho : order j = (5 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (5 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (5 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (5 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0641
lemma w_guarded_leaf_0642 :
    R748JointWitnessPointEntry.w 642 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨642, by omega⟩
  have ho : order j = (20 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (20 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (20 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (20 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0642
lemma w_guarded_leaf_0704 :
    R748JointWitnessPointEntry.w 704 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨704, by omega⟩
  have ho : order j = (516 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (516 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (516 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (516 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0704
lemma w_guarded_leaf_0768 :
    R748JointWitnessPointEntry.w 768 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨768, by omega⟩
  have ho : order j = (2 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (2 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (2 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (2 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0768
lemma w_guarded_leaf_0832 :
    R748JointWitnessPointEntry.w 832 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨832, by omega⟩
  have ho : order j = (514 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (514 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (514 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (514 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0832
lemma w_guarded_leaf_0896 :
    R748JointWitnessPointEntry.w 896 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨896, by omega⟩
  have ho : order j = (0 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (0 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (0 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (0 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0896
lemma w_guarded_leaf_0900 :
    R748JointWitnessPointEntry.w 900 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨900, by omega⟩
  have ho : order j = (32 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (32 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (32 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (32 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (32 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (32 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (32 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0900
lemma w_guarded_leaf_0901 :
    R748JointWitnessPointEntry.w 901 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨901, by omega⟩
  have ho : order j = (33 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (33 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (33 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (33 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0901
lemma w_guarded_leaf_0902 :
    R748JointWitnessPointEntry.w 902 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨902, by omega⟩
  have ho : order j = (48 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (48 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (48 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (48 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (48 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (48 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (48 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0902
lemma w_guarded_leaf_0903 :
    R748JointWitnessPointEntry.w 903 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨903, by omega⟩
  have ho : order j = (49 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (49 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (49 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (49 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0903
lemma w_guarded_leaf_0904 :
    R748JointWitnessPointEntry.w 904 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨904, by omega⟩
  have ho : order j = (64 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (64 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (64 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (64 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (64 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (64 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (64 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0904
lemma w_guarded_leaf_0905 :
    R748JointWitnessPointEntry.w 905 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨905, by omega⟩
  have ho : order j = (65 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (65 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (65 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (65 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0905
lemma w_guarded_leaf_0906 :
    R748JointWitnessPointEntry.w 906 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨906, by omega⟩
  have ho : order j = (80 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (80 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (80 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (80 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (80 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (80 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (80 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0906
lemma w_guarded_leaf_0907 :
    R748JointWitnessPointEntry.w 907 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨907, by omega⟩
  have ho : order j = (81 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (81 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (81 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (81 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0907
lemma w_guarded_leaf_0908 :
    R748JointWitnessPointEntry.w 908 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨908, by omega⟩
  have ho : order j = (96 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (96 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (96 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (96 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (96 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (96 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (96 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0908
lemma w_guarded_leaf_0909 :
    R748JointWitnessPointEntry.w 909 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨909, by omega⟩
  have ho : order j = (97 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (97 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (97 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (97 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0909
lemma w_guarded_leaf_0910 :
    R748JointWitnessPointEntry.w 910 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨910, by omega⟩
  have ho : order j = (112 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (112 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (112 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (112 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (112 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (112 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (112 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0910
lemma w_guarded_leaf_0911 :
    R748JointWitnessPointEntry.w 911 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨911, by omega⟩
  have ho : order j = (113 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (113 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (113 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (113 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0911
lemma w_guarded_leaf_0912 :
    R748JointWitnessPointEntry.w 912 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨912, by omega⟩
  have ho : order j = (128 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (128 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (128 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (128 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (128 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (128 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (128 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0912
end
end AspisR19.R754Point1GuardedLeaves
