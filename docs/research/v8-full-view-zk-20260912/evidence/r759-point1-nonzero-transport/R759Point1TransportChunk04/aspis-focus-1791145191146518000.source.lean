import AspisV8R19.R755Point1BasisTransport
import AspisV8R19.R753Point1BasisChunk00
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

/-- finite transport leaf j=637, original=999 -/
lemma transport_leaf_0637 : w 637 = (2147483503:M) + 576 := by
  let j : Fin 1024 := ⟨637, by omega⟩
  have horder : order j = (999 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483503:M) := by
    rw [horder]
    exact point1_basis_999
  have hw := w_from_basis j (2147483503:M) hb
  rw [horder] at hw
  have hmem : (999 : Fin 1024) ∈ inactive.erase 1023 := by
    change (999 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0637

/-- finite transport leaf j=638, original=1014 -/
lemma transport_leaf_0638 : w 638 = (2147483071:M) := by
  let j : Fin 1024 := ⟨638, by omega⟩
  have horder : order j = (1014 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483071:M) := by
    rw [horder]
    exact point1_basis_1014
  have hw := w_from_basis j (2147483071:M) hb
  rw [horder] at hw
  have hnotmem : (1014 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (1014 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (1014 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (1014 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (1014 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (1014 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0638

/-- finite transport leaf j=639, original=1015 -/
lemma transport_leaf_0639 : w 639 = (288:M) := by
  let j : Fin 1024 := ⟨639, by omega⟩
  have horder : order j = (1015 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (288:M) := by
    rw [horder]
    exact point1_basis_1015
  have hw := w_from_basis j (288:M) hb
  rw [horder] at hw
  have hnotmem : (1015 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (1015 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (1015 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (1015 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (1015 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (1015 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0639

/-- finite transport leaf j=736, original=772 -/
lemma transport_leaf_0736 : w 736 = (36:M) + 576 := by
  let j : Fin 1024 := ⟨736, by omega⟩
  have horder : order j = (772 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (36:M) := by
    rw [horder]
    exact point1_basis_772
  have hw := w_from_basis j (36:M) hb
  rw [horder] at hw
  have hmem : (772 : Fin 1024) ∈ inactive.erase 1023 := by
    change (772 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0736

/-- finite transport leaf j=752, original=900 -/
lemma transport_leaf_0752 : w 752 = (2147483575:M) + 576 := by
  let j : Fin 1024 := ⟨752, by omega⟩
  have horder : order j = (900 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483575:M) := by
    rw [horder]
    exact point1_basis_900
  have hw := w_from_basis j (2147483575:M) hb
  rw [horder] at hw
  have hmem : (900 : Fin 1024) ∈ inactive.erase 1023 := by
    change (900 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0752

/-- finite transport leaf j=753, original=901 -/
lemma transport_leaf_0753 : w 753 = (36:M) + 576 := by
  let j : Fin 1024 := ⟨753, by omega⟩
  have horder : order j = (901 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (36:M) := by
    rw [horder]
    exact point1_basis_901
  have hw := w_from_basis j (36:M) hb
  rw [horder] at hw
  have hmem : (901 : Fin 1024) ∈ inactive.erase 1023 := by
    change (901 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0753

/-- finite transport leaf j=754, original=916 -/
lemma transport_leaf_0754 : w 754 = (144:M) + 576 := by
  let j : Fin 1024 := ⟨754, by omega⟩
  have horder : order j = (916 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (144:M) := by
    rw [horder]
    exact point1_basis_916
  have hw := w_from_basis j (144:M) hb
  rw [horder] at hw
  have hmem : (916 : Fin 1024) ∈ inactive.erase 1023 := by
    change (916 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0754

/-- finite transport leaf j=755, original=917 -/
lemma transport_leaf_0755 : w 755 = (2147483575:M) := by
  let j : Fin 1024 := ⟨755, by omega⟩
  have horder : order j = (917 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483575:M) := by
    rw [horder]
    exact point1_basis_917
  have hw := w_from_basis j (2147483575:M) hb
  rw [horder] at hw
  have hnotmem : (917 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (917 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (917 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (917 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (917 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (917 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0755

/-- finite transport leaf j=756, original=932 -/
lemma transport_leaf_0756 : w 756 = (96:M) + 576 := by
  let j : Fin 1024 := ⟨756, by omega⟩
  have horder : order j = (932 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (96:M) := by
    rw [horder]
    exact point1_basis_932
  have hw := w_from_basis j (96:M) hb
  rw [horder] at hw
  have hmem : (932 : Fin 1024) ∈ inactive.erase 1023 := by
    change (932 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0756

/-- finite transport leaf j=757, original=933 -/
lemma transport_leaf_0757 : w 757 = (2147483599:M) := by
  let j : Fin 1024 := ⟨757, by omega⟩
  have horder : order j = (933 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483599:M) := by
    rw [horder]
    exact point1_basis_933
  have hw := w_from_basis j (2147483599:M) hb
  rw [horder] at hw
  have hnotmem : (933 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (933 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (933 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (933 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (933 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (933 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0757

/-- finite transport leaf j=758, original=948 -/
lemma transport_leaf_0758 : w 758 = (2147483455:M) + 576 := by
  let j : Fin 1024 := ⟨758, by omega⟩
  have horder : order j = (948 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483455:M) := by
    rw [horder]
    exact point1_basis_948
  have hw := w_from_basis j (2147483455:M) hb
  rw [horder] at hw
  have hmem : (948 : Fin 1024) ∈ inactive.erase 1023 := by
    change (948 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0758

/-- finite transport leaf j=759, original=949 -/
lemma transport_leaf_0759 : w 759 = (96:M) := by
  let j : Fin 1024 := ⟨759, by omega⟩
  have horder : order j = (949 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (96:M) := by
    rw [horder]
    exact point1_basis_949
  have hw := w_from_basis j (96:M) hb
  rw [horder] at hw
  have hnotmem : (949 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (949 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (949 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (949 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (949 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (949 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0759

/-- finite transport leaf j=760, original=964 -/
lemma transport_leaf_0760 : w 760 = (108:M) + 576 := by
  let j : Fin 1024 := ⟨760, by omega⟩
  have horder : order j = (964 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (108:M) := by
    rw [horder]
    exact point1_basis_964
  have hw := w_from_basis j (108:M) hb
  rw [horder] at hw
  have hmem : (964 : Fin 1024) ∈ inactive.erase 1023 := by
    change (964 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0760

/-- finite transport leaf j=761, original=965 -/
lemma transport_leaf_0761 : w 761 = (2147483593:M) := by
  let j : Fin 1024 := ⟨761, by omega⟩
  have horder : order j = (965 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483593:M) := by
    rw [horder]
    exact point1_basis_965
  have hw := w_from_basis j (2147483593:M) hb
  rw [horder] at hw
  have hnotmem : (965 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (965 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (965 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (965 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (965 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (965 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0761

/-- finite transport leaf j=762, original=980 -/
lemma transport_leaf_0762 : w 762 = (2147483431:M) + 576 := by
  let j : Fin 1024 := ⟨762, by omega⟩
  have horder : order j = (980 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483431:M) := by
    rw [horder]
    exact point1_basis_980
  have hw := w_from_basis j (2147483431:M) hb
  rw [horder] at hw
  have hmem : (980 : Fin 1024) ∈ inactive.erase 1023 := by
    change (980 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0762

/-- finite transport leaf j=763, original=981 -/
lemma transport_leaf_0763 : w 763 = (108:M) := by
  let j : Fin 1024 := ⟨763, by omega⟩
  have horder : order j = (981 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (108:M) := by
    rw [horder]
    exact point1_basis_981
  have hw := w_from_basis j (108:M) hb
  rw [horder] at hw
  have hnotmem : (981 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (981 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (981 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (981 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (981 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (981 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0763

/-- finite transport leaf j=764, original=996 -/
lemma transport_leaf_0764 : w 764 = (2147483503:M) + 576 := by
  let j : Fin 1024 := ⟨764, by omega⟩
  have horder : order j = (996 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483503:M) := by
    rw [horder]
    exact point1_basis_996
  have hw := w_from_basis j (2147483503:M) hb
  rw [horder] at hw
  have hmem : (996 : Fin 1024) ∈ inactive.erase 1023 := by
    change (996 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0764

/-- finite transport leaf j=765, original=997 -/
lemma transport_leaf_0765 : w 765 = (72:M) := by
  let j : Fin 1024 := ⟨765, by omega⟩
  have horder : order j = (997 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (72:M) := by
    rw [horder]
    exact point1_basis_997
  have hw := w_from_basis j (72:M) hb
  rw [horder] at hw
  have hnotmem : (997 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (997 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (997 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (997 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (997 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (997 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0765

/-- finite transport leaf j=766, original=1012 -/
lemma transport_leaf_0766 : w 766 = (288:M) := by
  let j : Fin 1024 := ⟨766, by omega⟩
  have horder : order j = (1012 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (288:M) := by
    rw [horder]
    exact point1_basis_1012
  have hw := w_from_basis j (288:M) hb
  rw [horder] at hw
  have hnotmem : (1012 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (1012 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (1012 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (1012 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (1012 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (1012 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0766

/-- finite transport leaf j=767, original=1013 -/
lemma transport_leaf_0767 : w 767 = (2147483503:M) + 576 := by
  let j : Fin 1024 := ⟨767, by omega⟩
  have horder : order j = (1013 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483503:M) := by
    rw [horder]
    exact point1_basis_1013
  have hw := w_from_basis j (2147483503:M) hb
  rw [horder] at hw
  have hmem : (1013 : Fin 1024) ∈ inactive.erase 1023 := by
    change (1013 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0767

/-- finite transport leaf j=864, original=770 -/
lemma transport_leaf_0864 : w 864 = (48:M) + 576 := by
  let j : Fin 1024 := ⟨864, by omega⟩
  have horder : order j = (770 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (48:M) := by
    rw [horder]
    exact point1_basis_770
  have hw := w_from_basis j (48:M) hb
  rw [horder] at hw
  have hmem : (770 : Fin 1024) ∈ inactive.erase 1023 := by
    change (770 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0864

/-- finite transport leaf j=880, original=898 -/
lemma transport_leaf_0880 : w 880 = (2147483551:M) + 576 := by
  let j : Fin 1024 := ⟨880, by omega⟩
  have horder : order j = (898 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483551:M) := by
    rw [horder]
    exact point1_basis_898
  have hw := w_from_basis j (2147483551:M) hb
  rw [horder] at hw
  have hmem : (898 : Fin 1024) ∈ inactive.erase 1023 := by
    change (898 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0880

/-- finite transport leaf j=881, original=899 -/
lemma transport_leaf_0881 : w 881 = (48:M) + 576 := by
  let j : Fin 1024 := ⟨881, by omega⟩
  have horder : order j = (899 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (48:M) := by
    rw [horder]
    exact point1_basis_899
  have hw := w_from_basis j (48:M) hb
  rw [horder] at hw
  have hmem : (899 : Fin 1024) ∈ inactive.erase 1023 := by
    change (899 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0881

/-- finite transport leaf j=882, original=914 -/
lemma transport_leaf_0882 : w 882 = (192:M) := by
  let j : Fin 1024 := ⟨882, by omega⟩
  have horder : order j = (914 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (192:M) := by
    rw [horder]
    exact point1_basis_914
  have hw := w_from_basis j (192:M) hb
  rw [horder] at hw
  have hnotmem : (914 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (914 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (914 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (914 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (914 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (914 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0882

/-- finite transport leaf j=883, original=915 -/
lemma transport_leaf_0883 : w 883 = (2147483551:M) + 576 := by
  let j : Fin 1024 := ⟨883, by omega⟩
  have horder : order j = (915 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483551:M) := by
    rw [horder]
    exact point1_basis_915
  have hw := w_from_basis j (2147483551:M) hb
  rw [horder] at hw
  have hmem : (915 : Fin 1024) ∈ inactive.erase 1023 := by
    change (915 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0883

/-- finite transport leaf j=884, original=930 -/
lemma transport_leaf_0884 : w 884 = (128:M) := by
  let j : Fin 1024 := ⟨884, by omega⟩
  have horder : order j = (930 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (128:M) := by
    rw [horder]
    exact point1_basis_930
  have hw := w_from_basis j (128:M) hb
  rw [horder] at hw
  have hnotmem : (930 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (930 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (930 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (930 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (930 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (930 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0884

/-- finite transport leaf j=885, original=931 -/
lemma transport_leaf_0885 : w 885 = (2147483583:M) + 576 := by
  let j : Fin 1024 := ⟨885, by omega⟩
  have horder : order j = (931 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483583:M) := by
    rw [horder]
    exact point1_basis_931
  have hw := w_from_basis j (2147483583:M) hb
  rw [horder] at hw
  have hmem : (931 : Fin 1024) ∈ inactive.erase 1023 := by
    change (931 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0885

/-- finite transport leaf j=886, original=946 -/
lemma transport_leaf_0886 : w 886 = (2147483391:M) := by
  let j : Fin 1024 := ⟨886, by omega⟩
  have horder : order j = (946 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483391:M) := by
    rw [horder]
    exact point1_basis_946
  have hw := w_from_basis j (2147483391:M) hb
  rw [horder] at hw
  have hnotmem : (946 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (946 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (946 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (946 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (946 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (946 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0886

/-- finite transport leaf j=887, original=947 -/
lemma transport_leaf_0887 : w 887 = (128:M) + 576 := by
  let j : Fin 1024 := ⟨887, by omega⟩
  have horder : order j = (947 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (128:M) := by
    rw [horder]
    exact point1_basis_947
  have hw := w_from_basis j (128:M) hb
  rw [horder] at hw
  have hmem : (947 : Fin 1024) ∈ inactive.erase 1023 := by
    change (947 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0887

/-- finite transport leaf j=888, original=962 -/
lemma transport_leaf_0888 : w 888 = (144:M) := by
  let j : Fin 1024 := ⟨888, by omega⟩
  have horder : order j = (962 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (144:M) := by
    rw [horder]
    exact point1_basis_962
  have hw := w_from_basis j (144:M) hb
  rw [horder] at hw
  have hnotmem : (962 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (962 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (962 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (962 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (962 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (962 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0888

/-- finite transport leaf j=889, original=963 -/
lemma transport_leaf_0889 : w 889 = (2147483575:M) + 576 := by
  let j : Fin 1024 := ⟨889, by omega⟩
  have horder : order j = (963 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483575:M) := by
    rw [horder]
    exact point1_basis_963
  have hw := w_from_basis j (2147483575:M) hb
  rw [horder] at hw
  have hmem : (963 : Fin 1024) ∈ inactive.erase 1023 := by
    change (963 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0889

/-- finite transport leaf j=890, original=978 -/
lemma transport_leaf_0890 : w 890 = (2147483359:M) := by
  let j : Fin 1024 := ⟨890, by omega⟩
  have horder : order j = (978 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483359:M) := by
    rw [horder]
    exact point1_basis_978
  have hw := w_from_basis j (2147483359:M) hb
  rw [horder] at hw
  have hnotmem : (978 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (978 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (978 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (978 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (978 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (978 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0890

end
end AspisR19.R759Point1TransportLeaves
