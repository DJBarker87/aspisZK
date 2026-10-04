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

lemma w_guarded_leaf_0977 :
    R748JointWitnessPointEntry.w 977 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨977, by omega⟩
  have ho : order j = (641 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (641 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (641 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (641 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0977
lemma w_guarded_leaf_0978 :
    R748JointWitnessPointEntry.w 978 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨978, by omega⟩
  have ho : order j = (656 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (656 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (656 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (656 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (656 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (656 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (656 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0978
lemma w_guarded_leaf_0979 :
    R748JointWitnessPointEntry.w 979 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨979, by omega⟩
  have ho : order j = (657 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (657 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (657 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (657 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0979
lemma w_guarded_leaf_0980 :
    R748JointWitnessPointEntry.w 980 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨980, by omega⟩
  have ho : order j = (672 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (672 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (672 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (672 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (672 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (672 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (672 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0980
lemma w_guarded_leaf_0981 :
    R748JointWitnessPointEntry.w 981 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨981, by omega⟩
  have ho : order j = (673 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (673 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (673 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (673 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0981
lemma w_guarded_leaf_0982 :
    R748JointWitnessPointEntry.w 982 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨982, by omega⟩
  have ho : order j = (688 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (688 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (688 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (688 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (688 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (688 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (688 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0982
lemma w_guarded_leaf_0983 :
    R748JointWitnessPointEntry.w 983 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨983, by omega⟩
  have ho : order j = (689 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (689 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (689 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (689 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0983
lemma w_guarded_leaf_0984 :
    R748JointWitnessPointEntry.w 984 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨984, by omega⟩
  have ho : order j = (704 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (704 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (704 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (704 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (704 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (704 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (704 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0984
lemma w_guarded_leaf_0985 :
    R748JointWitnessPointEntry.w 985 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨985, by omega⟩
  have ho : order j = (705 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (705 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (705 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (705 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0985
lemma w_guarded_leaf_0986 :
    R748JointWitnessPointEntry.w 986 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨986, by omega⟩
  have ho : order j = (720 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (720 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (720 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (720 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (720 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (720 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (720 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0986
lemma w_guarded_leaf_0987 :
    R748JointWitnessPointEntry.w 987 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨987, by omega⟩
  have ho : order j = (721 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (721 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (721 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (721 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0987
lemma w_guarded_leaf_0988 :
    R748JointWitnessPointEntry.w 988 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨988, by omega⟩
  have ho : order j = (736 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (736 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (736 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (736 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (736 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (736 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (736 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0988
lemma w_guarded_leaf_0989 :
    R748JointWitnessPointEntry.w 989 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨989, by omega⟩
  have ho : order j = (737 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (737 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (737 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (737 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0989
lemma w_guarded_leaf_0990 :
    R748JointWitnessPointEntry.w 990 = (0 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨990, by omega⟩
  have ho : order j = (752 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (752 : Fin 1024) ∉ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    intro h
    change (752 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (752 : Fin 1024) ∈ T163SourceTable.inactive :=
      (Finset.mem_erase.mp h).2
    change (752 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (752 : Fin 1024) = true :=
      (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (752 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_neg hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0990
lemma w_guarded_leaf_0991 :
    R748JointWitnessPointEntry.w 991 = (576 : R748JointWitnessPointEntry.M) := by
  let j : Fin 1024 := ⟨991, by omega⟩
  have ho : order j = (753 : Fin 1024) := by decide
  have hbits : (((order j).val >>> 9) &&& 1) = 0 ∨ (((order j).val >>> 8) &&& 1) = 0 := by
    rw [ho]
    decide
  have hmem : (753 : Fin 1024) ∈ TwoSwapSourceTable.inactive.erase (1023 : Fin 1024) := by
    change (753 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · change (753 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  have hw := R754Point1GuardedTransport.w_guarded j hbits
  rw [ho] at hw
  simp only [if_pos hmem] at hw
  simpa [j] using hw

#print axioms w_guarded_leaf_0991
end
end AspisR19.R754Point1GuardedLeaves
