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

lemma w_guarded_leaf_0945 :
    R748JointWitnessPointEntry.w 945 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨945, by omega⟩
  have ho : order j = (385 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (385 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (385 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (385 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0945
lemma w_guarded_leaf_0946 :
    R748JointWitnessPointEntry.w 946 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨946, by omega⟩
  have ho : order j = (400 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (400 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (400 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (400 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0946
lemma w_guarded_leaf_0947 :
    R748JointWitnessPointEntry.w 947 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨947, by omega⟩
  have ho : order j = (401 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (401 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (401 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (401 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0947
lemma w_guarded_leaf_0948 :
    R748JointWitnessPointEntry.w 948 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨948, by omega⟩
  have ho : order j = (416 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (416 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (416 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (416 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (416 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (416 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (416 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0948
lemma w_guarded_leaf_0949 :
    R748JointWitnessPointEntry.w 949 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨949, by omega⟩
  have ho : order j = (417 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (417 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (417 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (417 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0949
lemma w_guarded_leaf_0950 :
    R748JointWitnessPointEntry.w 950 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨950, by omega⟩
  have ho : order j = (432 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (432 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (432 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (432 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0950
lemma w_guarded_leaf_0951 :
    R748JointWitnessPointEntry.w 951 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨951, by omega⟩
  have ho : order j = (433 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (433 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (433 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (433 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0951
lemma w_guarded_leaf_0952 :
    R748JointWitnessPointEntry.w 952 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨952, by omega⟩
  have ho : order j = (448 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (448 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (448 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (448 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (448 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (448 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (448 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0952
lemma w_guarded_leaf_0953 :
    R748JointWitnessPointEntry.w 953 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨953, by omega⟩
  have ho : order j = (449 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (449 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (449 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (449 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0953
lemma w_guarded_leaf_0954 :
    R748JointWitnessPointEntry.w 954 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨954, by omega⟩
  have ho : order j = (464 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (464 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (464 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (464 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (464 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (464 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (464 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0954
lemma w_guarded_leaf_0955 :
    R748JointWitnessPointEntry.w 955 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨955, by omega⟩
  have ho : order j = (465 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (465 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (465 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (465 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0955
lemma w_guarded_leaf_0956 :
    R748JointWitnessPointEntry.w 956 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨956, by omega⟩
  have ho : order j = (480 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (480 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (480 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (480 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0956
lemma w_guarded_leaf_0957 :
    R748JointWitnessPointEntry.w 957 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨957, by omega⟩
  have ho : order j = (481 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (481 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (481 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (481 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0957
lemma w_guarded_leaf_0958 :
    R748JointWitnessPointEntry.w 958 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨958, by omega⟩
  have ho : order j = (496 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (496 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (496 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (496 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (496 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (496 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (496 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0958
lemma w_guarded_leaf_0959 :
    R748JointWitnessPointEntry.w 959 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨959, by omega⟩
  have ho : order j = (497 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (497 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (497 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (497 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0959
lemma w_guarded_leaf_0960 :
    R748JointWitnessPointEntry.w 960 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨960, by omega⟩
  have ho : order j = (512 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (512 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (512 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (512 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (512 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (512 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (512 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0960
lemma w_guarded_leaf_0961 :
    R748JointWitnessPointEntry.w 961 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨961, by omega⟩
  have ho : order j = (513 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (513 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (513 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (513 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0961
lemma w_guarded_leaf_0962 :
    R748JointWitnessPointEntry.w 962 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨962, by omega⟩
  have ho : order j = (528 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (528 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (528 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (528 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (528 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (528 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (528 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0962
lemma w_guarded_leaf_0963 :
    R748JointWitnessPointEntry.w 963 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨963, by omega⟩
  have ho : order j = (529 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (529 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (529 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (529 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0963
lemma w_guarded_leaf_0964 :
    R748JointWitnessPointEntry.w 964 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨964, by omega⟩
  have ho : order j = (544 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (544 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (544 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (544 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (544 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (544 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (544 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0964
lemma w_guarded_leaf_0965 :
    R748JointWitnessPointEntry.w 965 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨965, by omega⟩
  have ho : order j = (545 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (545 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (545 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (545 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0965
lemma w_guarded_leaf_0966 :
    R748JointWitnessPointEntry.w 966 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨966, by omega⟩
  have ho : order j = (560 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (560 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (560 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (560 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (560 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (560 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (560 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0966
lemma w_guarded_leaf_0967 :
    R748JointWitnessPointEntry.w 967 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨967, by omega⟩
  have ho : order j = (561 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (561 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (561 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (561 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0967
lemma w_guarded_leaf_0968 :
    R748JointWitnessPointEntry.w 968 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨968, by omega⟩
  have ho : order j = (576 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (576 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (576 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (576 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (576 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (576 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (576 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0968
lemma w_guarded_leaf_0969 :
    R748JointWitnessPointEntry.w 969 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨969, by omega⟩
  have ho : order j = (577 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (577 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (577 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (577 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0969
lemma w_guarded_leaf_0970 :
    R748JointWitnessPointEntry.w 970 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨970, by omega⟩
  have ho : order j = (592 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (592 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (592 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (592 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (592 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (592 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (592 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0970
lemma w_guarded_leaf_0971 :
    R748JointWitnessPointEntry.w 971 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨971, by omega⟩
  have ho : order j = (593 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (593 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (593 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (593 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0971
lemma w_guarded_leaf_0972 :
    R748JointWitnessPointEntry.w 972 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨972, by omega⟩
  have ho : order j = (608 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (608 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (608 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (608 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (608 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (608 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (608 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0972
lemma w_guarded_leaf_0973 :
    R748JointWitnessPointEntry.w 973 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨973, by omega⟩
  have ho : order j = (609 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (609 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (609 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (609 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0973
lemma w_guarded_leaf_0974 :
    R748JointWitnessPointEntry.w 974 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨974, by omega⟩
  have ho : order j = (624 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (624 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (624 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (624 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (624 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (624 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (624 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0974
lemma w_guarded_leaf_0975 :
    R748JointWitnessPointEntry.w 975 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨975, by omega⟩
  have ho : order j = (625 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (625 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (625 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (625 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0975
lemma w_guarded_leaf_0976 :
    R748JointWitnessPointEntry.w 976 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨976, by omega⟩
  have ho : order j = (640 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (640 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (640 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (640 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (640 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (640 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (640 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0976
end
end AspisR19.R754Point1GuardedLeaves
