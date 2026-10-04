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

lemma w_guarded_leaf_0148 :
    R748JointWitnessPointEntry.w 148 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨148, by omega⟩
  have ho : order j = (172 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (172 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (172 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (172 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (172 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (172 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (172 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0148
lemma w_guarded_leaf_0149 :
    R748JointWitnessPointEntry.w 149 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨149, by omega⟩
  have ho : order j = (173 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (173 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (173 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (173 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0149
lemma w_guarded_leaf_0150 :
    R748JointWitnessPointEntry.w 150 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨150, by omega⟩
  have ho : order j = (188 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (188 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (188 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (188 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (188 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (188 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (188 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0150
lemma w_guarded_leaf_0151 :
    R748JointWitnessPointEntry.w 151 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨151, by omega⟩
  have ho : order j = (189 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (189 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (189 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (189 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0151
lemma w_guarded_leaf_0152 :
    R748JointWitnessPointEntry.w 152 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨152, by omega⟩
  have ho : order j = (204 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (204 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (204 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (204 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (204 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (204 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (204 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0152
lemma w_guarded_leaf_0153 :
    R748JointWitnessPointEntry.w 153 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨153, by omega⟩
  have ho : order j = (205 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (205 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (205 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (205 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0153
lemma w_guarded_leaf_0154 :
    R748JointWitnessPointEntry.w 154 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨154, by omega⟩
  have ho : order j = (220 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (220 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (220 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (220 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (220 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (220 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (220 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0154
lemma w_guarded_leaf_0155 :
    R748JointWitnessPointEntry.w 155 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨155, by omega⟩
  have ho : order j = (221 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (221 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (221 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (221 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0155
lemma w_guarded_leaf_0156 :
    R748JointWitnessPointEntry.w 156 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨156, by omega⟩
  have ho : order j = (236 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (236 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (236 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (236 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (236 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (236 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (236 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0156
lemma w_guarded_leaf_0157 :
    R748JointWitnessPointEntry.w 157 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨157, by omega⟩
  have ho : order j = (237 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (237 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (237 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (237 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0157
lemma w_guarded_leaf_0158 :
    R748JointWitnessPointEntry.w 158 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨158, by omega⟩
  have ho : order j = (252 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (252 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (252 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (252 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (252 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (252 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (252 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0158
lemma w_guarded_leaf_0159 :
    R748JointWitnessPointEntry.w 159 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨159, by omega⟩
  have ho : order j = (253 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (253 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (253 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (253 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0159
lemma w_guarded_leaf_0160 :
    R748JointWitnessPointEntry.w 160 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨160, by omega⟩
  have ho : order j = (268 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (268 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (268 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (268 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (268 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (268 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (268 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0160
lemma w_guarded_leaf_0163 :
    R748JointWitnessPointEntry.w 163 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨163, by omega⟩
  have ho : order j = (285 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (285 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (285 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (285 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0163
lemma w_guarded_leaf_0164 :
    R748JointWitnessPointEntry.w 164 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨164, by omega⟩
  have ho : order j = (300 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (300 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (300 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (300 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (300 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (300 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (300 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0164
lemma w_guarded_leaf_0165 :
    R748JointWitnessPointEntry.w 165 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨165, by omega⟩
  have ho : order j = (301 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (301 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (301 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (301 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0165
lemma w_guarded_leaf_0166 :
    R748JointWitnessPointEntry.w 166 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨166, by omega⟩
  have ho : order j = (316 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (316 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (316 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (316 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (316 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (316 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (316 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0166
lemma w_guarded_leaf_0167 :
    R748JointWitnessPointEntry.w 167 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨167, by omega⟩
  have ho : order j = (317 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (317 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (317 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (317 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0167
lemma w_guarded_leaf_0168 :
    R748JointWitnessPointEntry.w 168 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨168, by omega⟩
  have ho : order j = (332 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (332 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (332 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (332 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (332 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (332 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (332 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0168
lemma w_guarded_leaf_0169 :
    R748JointWitnessPointEntry.w 169 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨169, by omega⟩
  have ho : order j = (333 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (333 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (333 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (333 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0169
lemma w_guarded_leaf_0170 :
    R748JointWitnessPointEntry.w 170 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨170, by omega⟩
  have ho : order j = (348 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (348 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (348 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (348 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (348 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (348 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (348 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0170
lemma w_guarded_leaf_0171 :
    R748JointWitnessPointEntry.w 171 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨171, by omega⟩
  have ho : order j = (349 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (349 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (349 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (349 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0171
lemma w_guarded_leaf_0172 :
    R748JointWitnessPointEntry.w 172 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨172, by omega⟩
  have ho : order j = (364 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (364 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (364 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (364 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (364 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (364 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (364 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0172
lemma w_guarded_leaf_0173 :
    R748JointWitnessPointEntry.w 173 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨173, by omega⟩
  have ho : order j = (365 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (365 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (365 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (365 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0173
lemma w_guarded_leaf_0174 :
    R748JointWitnessPointEntry.w 174 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨174, by omega⟩
  have ho : order j = (380 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (380 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (380 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (380 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (380 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (380 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (380 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0174
lemma w_guarded_leaf_0175 :
    R748JointWitnessPointEntry.w 175 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨175, by omega⟩
  have ho : order j = (381 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (381 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (381 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (381 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0175
lemma w_guarded_leaf_0176 :
    R748JointWitnessPointEntry.w 176 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨176, by omega⟩
  have ho : order j = (396 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (396 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (396 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (396 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (396 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (396 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (396 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0176
lemma w_guarded_leaf_0179 :
    R748JointWitnessPointEntry.w 179 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨179, by omega⟩
  have ho : order j = (413 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (413 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (413 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (413 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0179
lemma w_guarded_leaf_0180 :
    R748JointWitnessPointEntry.w 180 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨180, by omega⟩
  have ho : order j = (428 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (428 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (428 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (428 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (428 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (428 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (428 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0180
lemma w_guarded_leaf_0181 :
    R748JointWitnessPointEntry.w 181 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨181, by omega⟩
  have ho : order j = (429 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (429 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (429 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (429 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0181
lemma w_guarded_leaf_0182 :
    R748JointWitnessPointEntry.w 182 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨182, by omega⟩
  have ho : order j = (444 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (444 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (444 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (444 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0182
lemma w_guarded_leaf_0183 :
    R748JointWitnessPointEntry.w 183 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨183, by omega⟩
  have ho : order j = (445 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (445 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (445 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (445 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0183
end
end AspisR19.R754Point1GuardedLeaves
