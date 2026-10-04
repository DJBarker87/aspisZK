import AspisV8R19.R755Point1BasisTransport
import AspisV8R19.R753Point1BasisChunk00
import AspisV8R19.R753Point1BasisChunk01
import AspisV8R19.R753Point1BasisChunk02
import AspisV8R19.R753Point1BasisChunk03
import AspisV8R19.R753Point1BasisChunk04
import AspisV8R19.R753Point1BasisChunk05

namespace AspisR19.R759Point1TransportLeaves
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisR19.R755Point1BasisTransport
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R753Point1BasisValues
noncomputable section

/-- finite transport leaf j=891, original=979 -/
lemma transport_leaf_0891 : w 891 = (144:M) + 576 := by
  let j : Fin 1024 := ⟨891, by omega⟩
  have horder : order j = (979 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (144:M) := by
    rw [horder]
    exact point1_basis_979
  have hw := w_from_basis j (144:M) hb
  rw [horder] at hw
  have hmem : (979 : Fin 1024) ∈ inactive.erase 1023 := by
    change (979 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0891

/-- finite transport leaf j=892, original=994 -/
lemma transport_leaf_0892 : w 892 = (2147483455:M) := by
  let j : Fin 1024 := ⟨892, by omega⟩
  have horder : order j = (994 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483455:M) := by
    rw [horder]
    exact point1_basis_994
  have hw := w_from_basis j (2147483455:M) hb
  rw [horder] at hw
  have hnotmem : (994 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (994 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (994 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (994 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (994 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (994 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0892

/-- finite transport leaf j=893, original=995 -/
lemma transport_leaf_0893 : w 893 = (96:M) + 576 := by
  let j : Fin 1024 := ⟨893, by omega⟩
  have horder : order j = (995 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (96:M) := by
    rw [horder]
    exact point1_basis_995
  have hw := w_from_basis j (96:M) hb
  rw [horder] at hw
  have hmem : (995 : Fin 1024) ∈ inactive.erase 1023 := by
    change (995 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0893

/-- finite transport leaf j=894, original=1010 -/
lemma transport_leaf_0894 : w 894 = (384:M) := by
  let j : Fin 1024 := ⟨894, by omega⟩
  have horder : order j = (1010 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (384:M) := by
    rw [horder]
    exact point1_basis_1010
  have hw := w_from_basis j (384:M) hb
  rw [horder] at hw
  have hnotmem : (1010 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (1010 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (1010 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (1010 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (1010 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (1010 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0894

/-- finite transport leaf j=895, original=1011 -/
lemma transport_leaf_0895 : w 895 = (2147483455:M) + 576 := by
  let j : Fin 1024 := ⟨895, by omega⟩
  have horder : order j = (1011 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483455:M) := by
    rw [horder]
    exact point1_basis_1011
  have hw := w_from_basis j (2147483455:M) hb
  rw [horder] at hw
  have hmem : (1011 : Fin 1024) ∈ inactive.erase 1023 := by
    change (1011 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0895

/-- finite transport leaf j=992, original=768 -/
lemma transport_leaf_0992 : w 992 = (2147483623:M) := by
  let j : Fin 1024 := ⟨992, by omega⟩
  have horder : order j = (768 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483623:M) := by
    rw [horder]
    exact point1_basis_768
  have hw := w_from_basis j (2147483623:M) hb
  rw [horder] at hw
  have hnotmem : (768 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (768 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (768 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (768 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (768 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (768 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0992

/-- finite transport leaf j=993, original=769 -/
lemma transport_leaf_0993 : w 993 = (12:M) + 576 := by
  let j : Fin 1024 := ⟨993, by omega⟩
  have horder : order j = (769 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (12:M) := by
    rw [horder]
    exact point1_basis_769
  have hw := w_from_basis j (12:M) hb
  rw [horder] at hw
  have hmem : (769 : Fin 1024) ∈ inactive.erase 1023 := by
    change (769 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0993

/-- finite transport leaf j=994, original=784 -/
lemma transport_leaf_0994 : w 994 = (48:M) := by
  let j : Fin 1024 := ⟨994, by omega⟩
  have horder : order j = (784 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (48:M) := by
    rw [horder]
    exact point1_basis_784
  have hw := w_from_basis j (48:M) hb
  rw [horder] at hw
  have hnotmem : (784 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (784 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (784 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (784 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (784 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (784 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0994

/-- finite transport leaf j=995, original=785 -/
lemma transport_leaf_0995 : w 995 = (2147483623:M) + 576 := by
  let j : Fin 1024 := ⟨995, by omega⟩
  have horder : order j = (785 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483623:M) := by
    rw [horder]
    exact point1_basis_785
  have hw := w_from_basis j (2147483623:M) hb
  rw [horder] at hw
  have hmem : (785 : Fin 1024) ∈ inactive.erase 1023 := by
    change (785 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0995

/-- finite transport leaf j=996, original=800 -/
lemma transport_leaf_0996 : w 996 = (32:M) := by
  let j : Fin 1024 := ⟨996, by omega⟩
  have horder : order j = (800 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (32:M) := by
    rw [horder]
    exact point1_basis_800
  have hw := w_from_basis j (32:M) hb
  rw [horder] at hw
  have hnotmem : (800 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (800 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (800 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (800 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (800 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (800 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0996

/-- finite transport leaf j=997, original=801 -/
lemma transport_leaf_0997 : w 997 = (2147483631:M) + 576 := by
  let j : Fin 1024 := ⟨997, by omega⟩
  have horder : order j = (801 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483631:M) := by
    rw [horder]
    exact point1_basis_801
  have hw := w_from_basis j (2147483631:M) hb
  rw [horder] at hw
  have hmem : (801 : Fin 1024) ∈ inactive.erase 1023 := by
    change (801 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0997

/-- finite transport leaf j=998, original=816 -/
lemma transport_leaf_0998 : w 998 = (2147483583:M) := by
  let j : Fin 1024 := ⟨998, by omega⟩
  have horder : order j = (816 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483583:M) := by
    rw [horder]
    exact point1_basis_816
  have hw := w_from_basis j (2147483583:M) hb
  rw [horder] at hw
  have hnotmem : (816 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (816 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (816 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (816 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (816 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (816 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0998

/-- finite transport leaf j=999, original=817 -/
lemma transport_leaf_0999 : w 999 = (32:M) + 576 := by
  let j : Fin 1024 := ⟨999, by omega⟩
  have horder : order j = (817 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (32:M) := by
    rw [horder]
    exact point1_basis_817
  have hw := w_from_basis j (32:M) hb
  rw [horder] at hw
  have hmem : (817 : Fin 1024) ∈ inactive.erase 1023 := by
    change (817 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0999

/-- finite transport leaf j=1000, original=832 -/
lemma transport_leaf_1000 : w 1000 = (36:M) := by
  let j : Fin 1024 := ⟨1000, by omega⟩
  have horder : order j = (832 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (36:M) := by
    rw [horder]
    exact point1_basis_832
  have hw := w_from_basis j (36:M) hb
  rw [horder] at hw
  have hnotmem : (832 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (832 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (832 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (832 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (832 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (832 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_1000

/-- finite transport leaf j=1001, original=833 -/
lemma transport_leaf_1001 : w 1001 = (2147483629:M) + 576 := by
  let j : Fin 1024 := ⟨1001, by omega⟩
  have horder : order j = (833 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483629:M) := by
    rw [horder]
    exact point1_basis_833
  have hw := w_from_basis j (2147483629:M) hb
  rw [horder] at hw
  have hmem : (833 : Fin 1024) ∈ inactive.erase 1023 := by
    change (833 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_1001

/-- finite transport leaf j=1002, original=848 -/
lemma transport_leaf_1002 : w 1002 = (2147483575:M) := by
  let j : Fin 1024 := ⟨1002, by omega⟩
  have horder : order j = (848 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483575:M) := by
    rw [horder]
    exact point1_basis_848
  have hw := w_from_basis j (2147483575:M) hb
  rw [horder] at hw
  have hnotmem : (848 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (848 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (848 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (848 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (848 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (848 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_1002

/-- finite transport leaf j=1003, original=849 -/
lemma transport_leaf_1003 : w 1003 = (36:M) + 576 := by
  let j : Fin 1024 := ⟨1003, by omega⟩
  have horder : order j = (849 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (36:M) := by
    rw [horder]
    exact point1_basis_849
  have hw := w_from_basis j (36:M) hb
  rw [horder] at hw
  have hmem : (849 : Fin 1024) ∈ inactive.erase 1023 := by
    change (849 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_1003

/-- finite transport leaf j=1004, original=864 -/
lemma transport_leaf_1004 : w 1004 = (2147483599:M) := by
  let j : Fin 1024 := ⟨1004, by omega⟩
  have horder : order j = (864 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483599:M) := by
    rw [horder]
    exact point1_basis_864
  have hw := w_from_basis j (2147483599:M) hb
  rw [horder] at hw
  have hnotmem : (864 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (864 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (864 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (864 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (864 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (864 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_1004

/-- finite transport leaf j=1005, original=865 -/
lemma transport_leaf_1005 : w 1005 = (24:M) + 576 := by
  let j : Fin 1024 := ⟨1005, by omega⟩
  have horder : order j = (865 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (24:M) := by
    rw [horder]
    exact point1_basis_865
  have hw := w_from_basis j (24:M) hb
  rw [horder] at hw
  have hmem : (865 : Fin 1024) ∈ inactive.erase 1023 := by
    change (865 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_1005

/-- finite transport leaf j=1006, original=880 -/
lemma transport_leaf_1006 : w 1006 = (96:M) := by
  let j : Fin 1024 := ⟨1006, by omega⟩
  have horder : order j = (880 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (96:M) := by
    rw [horder]
    exact point1_basis_880
  have hw := w_from_basis j (96:M) hb
  rw [horder] at hw
  have hnotmem : (880 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (880 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (880 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (880 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (880 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (880 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_1006

/-- finite transport leaf j=1007, original=881 -/
lemma transport_leaf_1007 : w 1007 = (2147483599:M) + 576 := by
  let j : Fin 1024 := ⟨1007, by omega⟩
  have horder : order j = (881 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483599:M) := by
    rw [horder]
    exact point1_basis_881
  have hw := w_from_basis j (2147483599:M) hb
  rw [horder] at hw
  have hmem : (881 : Fin 1024) ∈ inactive.erase 1023 := by
    change (881 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_1007

/-- finite transport leaf j=1008, original=896 -/
lemma transport_leaf_1008 : w 1008 = (48:M) := by
  let j : Fin 1024 := ⟨1008, by omega⟩
  have horder : order j = (896 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (48:M) := by
    rw [horder]
    exact point1_basis_896
  have hw := w_from_basis j (48:M) hb
  rw [horder] at hw
  have hnotmem : (896 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (896 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (896 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (896 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (896 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (896 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_1008

/-- finite transport leaf j=1009, original=897 -/
lemma transport_leaf_1009 : w 1009 = (2147483623:M) + 576 := by
  let j : Fin 1024 := ⟨1009, by omega⟩
  have horder : order j = (897 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483623:M) := by
    rw [horder]
    exact point1_basis_897
  have hw := w_from_basis j (2147483623:M) hb
  rw [horder] at hw
  have hmem : (897 : Fin 1024) ∈ inactive.erase 1023 := by
    change (897 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_1009

/-- finite transport leaf j=1010, original=912 -/
lemma transport_leaf_1010 : w 1010 = (2147483551:M) + 576 := by
  let j : Fin 1024 := ⟨1010, by omega⟩
  have horder : order j = (912 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483551:M) := by
    rw [horder]
    exact point1_basis_912
  have hw := w_from_basis j (2147483551:M) hb
  rw [horder] at hw
  have hmem : (912 : Fin 1024) ∈ inactive.erase 1023 := by
    change (912 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_1010

/-- finite transport leaf j=1011, original=913 -/
lemma transport_leaf_1011 : w 1011 = (48:M) := by
  let j : Fin 1024 := ⟨1011, by omega⟩
  have horder : order j = (913 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (48:M) := by
    rw [horder]
    exact point1_basis_913
  have hw := w_from_basis j (48:M) hb
  rw [horder] at hw
  have hnotmem : (913 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (913 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (913 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (913 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (913 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (913 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_1011

/-- finite transport leaf j=1012, original=928 -/
lemma transport_leaf_1012 : w 1012 = (2147483583:M) + 576 := by
  let j : Fin 1024 := ⟨1012, by omega⟩
  have horder : order j = (928 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483583:M) := by
    rw [horder]
    exact point1_basis_928
  have hw := w_from_basis j (2147483583:M) hb
  rw [horder] at hw
  have hmem : (928 : Fin 1024) ∈ inactive.erase 1023 := by
    change (928 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_1012

/-- finite transport leaf j=1013, original=929 -/
lemma transport_leaf_1013 : w 1013 = (32:M) := by
  let j : Fin 1024 := ⟨1013, by omega⟩
  have horder : order j = (929 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (32:M) := by
    rw [horder]
    exact point1_basis_929
  have hw := w_from_basis j (32:M) hb
  rw [horder] at hw
  have hnotmem : (929 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (929 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (929 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (929 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (929 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (929 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_1013

/-- finite transport leaf j=1014, original=944 -/
lemma transport_leaf_1014 : w 1014 = (128:M) + 576 := by
  let j : Fin 1024 := ⟨1014, by omega⟩
  have horder : order j = (944 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (128:M) := by
    rw [horder]
    exact point1_basis_944
  have hw := w_from_basis j (128:M) hb
  rw [horder] at hw
  have hmem : (944 : Fin 1024) ∈ inactive.erase 1023 := by
    change (944 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_1014

/-- finite transport leaf j=1015, original=945 -/
lemma transport_leaf_1015 : w 1015 = (2147483583:M) := by
  let j : Fin 1024 := ⟨1015, by omega⟩
  have horder : order j = (945 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483583:M) := by
    rw [horder]
    exact point1_basis_945
  have hw := w_from_basis j (2147483583:M) hb
  rw [horder] at hw
  have hnotmem : (945 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (945 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (945 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (945 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (945 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (945 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_1015

/-- finite transport leaf j=1016, original=960 -/
lemma transport_leaf_1016 : w 1016 = (2147483575:M) + 576 := by
  let j : Fin 1024 := ⟨1016, by omega⟩
  have horder : order j = (960 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483575:M) := by
    rw [horder]
    exact point1_basis_960
  have hw := w_from_basis j (2147483575:M) hb
  rw [horder] at hw
  have hmem : (960 : Fin 1024) ∈ inactive.erase 1023 := by
    change (960 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_1016

/-- finite transport leaf j=1017, original=961 -/
lemma transport_leaf_1017 : w 1017 = (36:M) := by
  let j : Fin 1024 := ⟨1017, by omega⟩
  have horder : order j = (961 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (36:M) := by
    rw [horder]
    exact point1_basis_961
  have hw := w_from_basis j (36:M) hb
  rw [horder] at hw
  have hnotmem : (961 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (961 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (961 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (961 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (961 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (961 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_1017

/-- finite transport leaf j=1018, original=976 -/
lemma transport_leaf_1018 : w 1018 = (144:M) + 576 := by
  let j : Fin 1024 := ⟨1018, by omega⟩
  have horder : order j = (976 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (144:M) := by
    rw [horder]
    exact point1_basis_976
  have hw := w_from_basis j (144:M) hb
  rw [horder] at hw
  have hmem : (976 : Fin 1024) ∈ inactive.erase 1023 := by
    change (976 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_1018

end
end AspisR19.R759Point1TransportLeaves
