import AspisV8R19.R755Point1BasisTransport
import AspisV8R19.R753Point1BasisChunk04
import AspisV8R19.R753Point1BasisChunk05
import AspisV8R19.R753Point1BasisChunk06

namespace AspisR19.R759Point1TransportLeaves
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisR19.R755Point1BasisTransport
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R753Point1BasisValues
noncomputable section

/-- finite transport leaf j=1019, original=977 -/
lemma transport_leaf_1019 : w 1019 = (2147483575:M) := by
  let j : Fin 1024 := ⟨1019, by omega⟩
  have horder : order j = (977 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483575:M) := by
    rw [horder]
    exact point1_basis_977
  have hw := w_from_basis j (2147483575:M) hb
  rw [horder] at hw
  have hnotmem : (977 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (977 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (977 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (977 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (977 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (977 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_1019

/-- finite transport leaf j=1020, original=992 -/
lemma transport_leaf_1020 : w 1020 = (96:M) + 576 := by
  let j : Fin 1024 := ⟨1020, by omega⟩
  have horder : order j = (992 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (96:M) := by
    rw [horder]
    exact point1_basis_992
  have hw := w_from_basis j (96:M) hb
  rw [horder] at hw
  have hmem : (992 : Fin 1024) ∈ inactive.erase 1023 := by
    change (992 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_1020

/-- finite transport leaf j=1021, original=1022 -/
lemma transport_leaf_1021 : w 1021 = (1152:M) + 576 := by
  let j : Fin 1024 := ⟨1021, by omega⟩
  have horder : order j = (1022 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (1152:M) := by
    rw [horder]
    exact point1_basis_1022
  have hw := w_from_basis j (1152:M) hb
  rw [horder] at hw
  have hmem : (1022 : Fin 1024) ∈ inactive.erase 1023 := by
    change (1022 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_1021

/-- finite transport leaf j=1022, original=1008 -/
lemma transport_leaf_1022 : w 1022 = (2147483455:M) := by
  let j : Fin 1024 := ⟨1022, by omega⟩
  have horder : order j = (1008 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483455:M) := by
    rw [horder]
    exact point1_basis_1008
  have hw := w_from_basis j (2147483455:M) hb
  rw [horder] at hw
  have hnotmem : (1008 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (1008 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (1008 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (1008 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (1008 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (1008 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_1022

end
end AspisR19.R759Point1TransportLeaves
