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

/-- finite transport leaf j=96, original=782 -/
lemma transport_leaf_0096 : w 96 = (144:M) + 576 := by
  let j : Fin 1024 := ⟨96, by omega⟩
  have horder : order j = (782 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (144:M) := by
    rw [horder]
    exact point1_basis_782
  have hw := w_from_basis j (144:M) hb
  rw [horder] at hw
  have hmem : (782 : Fin 1024) ∈ inactive.erase 1023 := by
    change (782 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0096

/-- finite transport leaf j=97, original=783 -/
lemma transport_leaf_0097 : w 97 = (2147483575:M) + 576 := by
  let j : Fin 1024 := ⟨97, by omega⟩
  have horder : order j = (783 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483575:M) := by
    rw [horder]
    exact point1_basis_783
  have hw := w_from_basis j (2147483575:M) hb
  rw [horder] at hw
  have hmem : (783 : Fin 1024) ∈ inactive.erase 1023 := by
    change (783 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0097

/-- finite transport leaf j=98, original=798 -/
lemma transport_leaf_0098 : w 98 = (2147483359:M) + 576 := by
  let j : Fin 1024 := ⟨98, by omega⟩
  have horder : order j = (798 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483359:M) := by
    rw [horder]
    exact point1_basis_798
  have hw := w_from_basis j (2147483359:M) hb
  rw [horder] at hw
  have hmem : (798 : Fin 1024) ∈ inactive.erase 1023 := by
    change (798 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0098

/-- finite transport leaf j=99, original=799 -/
lemma transport_leaf_0099 : w 99 = (144:M) + 576 := by
  let j : Fin 1024 := ⟨99, by omega⟩
  have horder : order j = (799 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (144:M) := by
    rw [horder]
    exact point1_basis_799
  have hw := w_from_basis j (144:M) hb
  rw [horder] at hw
  have hmem : (799 : Fin 1024) ∈ inactive.erase 1023 := by
    change (799 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0099

/-- finite transport leaf j=100, original=814 -/
lemma transport_leaf_0100 : w 100 = (2147483455:M) + 576 := by
  let j : Fin 1024 := ⟨100, by omega⟩
  have horder : order j = (814 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483455:M) := by
    rw [horder]
    exact point1_basis_814
  have hw := w_from_basis j (2147483455:M) hb
  rw [horder] at hw
  have hmem : (814 : Fin 1024) ∈ inactive.erase 1023 := by
    change (814 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0100

/-- finite transport leaf j=101, original=815 -/
lemma transport_leaf_0101 : w 101 = (96:M) + 576 := by
  let j : Fin 1024 := ⟨101, by omega⟩
  have horder : order j = (815 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (96:M) := by
    rw [horder]
    exact point1_basis_815
  have hw := w_from_basis j (96:M) hb
  rw [horder] at hw
  have hmem : (815 : Fin 1024) ∈ inactive.erase 1023 := by
    change (815 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0101

/-- finite transport leaf j=102, original=830 -/
lemma transport_leaf_0102 : w 102 = (384:M) + 576 := by
  let j : Fin 1024 := ⟨102, by omega⟩
  have horder : order j = (830 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (384:M) := by
    rw [horder]
    exact point1_basis_830
  have hw := w_from_basis j (384:M) hb
  rw [horder] at hw
  have hmem : (830 : Fin 1024) ∈ inactive.erase 1023 := by
    change (830 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0102

/-- finite transport leaf j=105, original=847 -/
lemma transport_leaf_0105 : w 105 = (108:M) + 576 := by
  let j : Fin 1024 := ⟨105, by omega⟩
  have horder : order j = (847 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (108:M) := by
    rw [horder]
    exact point1_basis_847
  have hw := w_from_basis j (108:M) hb
  rw [horder] at hw
  have hmem : (847 : Fin 1024) ∈ inactive.erase 1023 := by
    change (847 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0105

/-- finite transport leaf j=106, original=862 -/
lemma transport_leaf_0106 : w 106 = (432:M) + 576 := by
  let j : Fin 1024 := ⟨106, by omega⟩
  have horder : order j = (862 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (432:M) := by
    rw [horder]
    exact point1_basis_862
  have hw := w_from_basis j (432:M) hb
  rw [horder] at hw
  have hmem : (862 : Fin 1024) ∈ inactive.erase 1023 := by
    change (862 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0106

/-- finite transport leaf j=108, original=878 -/
lemma transport_leaf_0108 : w 108 = (288:M) + 576 := by
  let j : Fin 1024 := ⟨108, by omega⟩
  have horder : order j = (878 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (288:M) := by
    rw [horder]
    exact point1_basis_878
  have hw := w_from_basis j (288:M) hb
  rw [horder] at hw
  have hmem : (878 : Fin 1024) ∈ inactive.erase 1023 := by
    change (878 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0108

/-- finite transport leaf j=109, original=879 -/
lemma transport_leaf_0109 : w 109 = (2147483503:M) + 576 := by
  let j : Fin 1024 := ⟨109, by omega⟩
  have horder : order j = (879 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483503:M) := by
    rw [horder]
    exact point1_basis_879
  have hw := w_from_basis j (2147483503:M) hb
  rw [horder] at hw
  have hmem : (879 : Fin 1024) ∈ inactive.erase 1023 := by
    change (879 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0109

/-- finite transport leaf j=110, original=894 -/
lemma transport_leaf_0110 : w 110 = (2147483071:M) + 576 := by
  let j : Fin 1024 := ⟨110, by omega⟩
  have horder : order j = (894 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483071:M) := by
    rw [horder]
    exact point1_basis_894
  have hw := w_from_basis j (2147483071:M) hb
  rw [horder] at hw
  have hmem : (894 : Fin 1024) ∈ inactive.erase 1023 := by
    change (894 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0110

/-- finite transport leaf j=111, original=895 -/
lemma transport_leaf_0111 : w 111 = (288:M) + 576 := by
  let j : Fin 1024 := ⟨111, by omega⟩
  have horder : order j = (895 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (288:M) := by
    rw [horder]
    exact point1_basis_895
  have hw := w_from_basis j (288:M) hb
  rw [horder] at hw
  have hmem : (895 : Fin 1024) ∈ inactive.erase 1023 := by
    change (895 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0111

/-- finite transport leaf j=112, original=910 -/
lemma transport_leaf_0112 : w 112 = (2147483359:M) + 576 := by
  let j : Fin 1024 := ⟨112, by omega⟩
  have horder : order j = (910 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483359:M) := by
    rw [horder]
    exact point1_basis_910
  have hw := w_from_basis j (2147483359:M) hb
  rw [horder] at hw
  have hmem : (910 : Fin 1024) ∈ inactive.erase 1023 := by
    change (910 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0112

/-- finite transport leaf j=113, original=911 -/
lemma transport_leaf_0113 : w 113 = (144:M) + 576 := by
  let j : Fin 1024 := ⟨113, by omega⟩
  have horder : order j = (911 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (144:M) := by
    rw [horder]
    exact point1_basis_911
  have hw := w_from_basis j (144:M) hb
  rw [horder] at hw
  have hmem : (911 : Fin 1024) ∈ inactive.erase 1023 := by
    change (911 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0113

/-- finite transport leaf j=114, original=926 -/
lemma transport_leaf_0114 : w 114 = (576:M) := by
  let j : Fin 1024 := ⟨114, by omega⟩
  have horder : order j = (926 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (576:M) := by
    rw [horder]
    exact point1_basis_926
  have hw := w_from_basis j (576:M) hb
  rw [horder] at hw
  have hnotmem : (926 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (926 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (926 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (926 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (926 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (926 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0114

/-- finite transport leaf j=115, original=927 -/
lemma transport_leaf_0115 : w 115 = (2147483359:M) + 576 := by
  let j : Fin 1024 := ⟨115, by omega⟩
  have horder : order j = (927 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483359:M) := by
    rw [horder]
    exact point1_basis_927
  have hw := w_from_basis j (2147483359:M) hb
  rw [horder] at hw
  have hmem : (927 : Fin 1024) ∈ inactive.erase 1023 := by
    change (927 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0115

/-- finite transport leaf j=116, original=942 -/
lemma transport_leaf_0116 : w 116 = (384:M) := by
  let j : Fin 1024 := ⟨116, by omega⟩
  have horder : order j = (942 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (384:M) := by
    rw [horder]
    exact point1_basis_942
  have hw := w_from_basis j (384:M) hb
  rw [horder] at hw
  have hnotmem : (942 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (942 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (942 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (942 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (942 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (942 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0116

/-- finite transport leaf j=117, original=943 -/
lemma transport_leaf_0117 : w 117 = (2147483455:M) + 576 := by
  let j : Fin 1024 := ⟨117, by omega⟩
  have horder : order j = (943 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483455:M) := by
    rw [horder]
    exact point1_basis_943
  have hw := w_from_basis j (2147483455:M) hb
  rw [horder] at hw
  have hmem : (943 : Fin 1024) ∈ inactive.erase 1023 := by
    change (943 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0117

/-- finite transport leaf j=118, original=958 -/
lemma transport_leaf_0118 : w 118 = (2147482879:M) := by
  let j : Fin 1024 := ⟨118, by omega⟩
  have horder : order j = (958 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147482879:M) := by
    rw [horder]
    exact point1_basis_958
  have hw := w_from_basis j (2147482879:M) hb
  rw [horder] at hw
  have hnotmem : (958 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (958 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (958 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (958 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (958 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (958 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0118

/-- finite transport leaf j=119, original=959 -/
lemma transport_leaf_0119 : w 119 = (384:M) + 576 := by
  let j : Fin 1024 := ⟨119, by omega⟩
  have horder : order j = (959 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (384:M) := by
    rw [horder]
    exact point1_basis_959
  have hw := w_from_basis j (384:M) hb
  rw [horder] at hw
  have hmem : (959 : Fin 1024) ∈ inactive.erase 1023 := by
    change (959 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0119

/-- finite transport leaf j=120, original=974 -/
lemma transport_leaf_0120 : w 120 = (432:M) := by
  let j : Fin 1024 := ⟨120, by omega⟩
  have horder : order j = (974 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (432:M) := by
    rw [horder]
    exact point1_basis_974
  have hw := w_from_basis j (432:M) hb
  rw [horder] at hw
  have hnotmem : (974 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (974 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (974 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (974 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (974 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (974 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0120

/-- finite transport leaf j=121, original=975 -/
lemma transport_leaf_0121 : w 121 = (2147483431:M) + 576 := by
  let j : Fin 1024 := ⟨121, by omega⟩
  have horder : order j = (975 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483431:M) := by
    rw [horder]
    exact point1_basis_975
  have hw := w_from_basis j (2147483431:M) hb
  rw [horder] at hw
  have hmem : (975 : Fin 1024) ∈ inactive.erase 1023 := by
    change (975 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0121

/-- finite transport leaf j=122, original=990 -/
lemma transport_leaf_0122 : w 122 = (2147482783:M) := by
  let j : Fin 1024 := ⟨122, by omega⟩
  have horder : order j = (990 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147482783:M) := by
    rw [horder]
    exact point1_basis_990
  have hw := w_from_basis j (2147482783:M) hb
  rw [horder] at hw
  have hnotmem : (990 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (990 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (990 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (990 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (990 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (990 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0122

/-- finite transport leaf j=123, original=991 -/
lemma transport_leaf_0123 : w 123 = (432:M) + 576 := by
  let j : Fin 1024 := ⟨123, by omega⟩
  have horder : order j = (991 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (432:M) := by
    rw [horder]
    exact point1_basis_991
  have hw := w_from_basis j (432:M) hb
  rw [horder] at hw
  have hmem : (991 : Fin 1024) ∈ inactive.erase 1023 := by
    change (991 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0123

/-- finite transport leaf j=124, original=1006 -/
lemma transport_leaf_0124 : w 124 = (2147483071:M) := by
  let j : Fin 1024 := ⟨124, by omega⟩
  have horder : order j = (1006 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483071:M) := by
    rw [horder]
    exact point1_basis_1006
  have hw := w_from_basis j (2147483071:M) hb
  rw [horder] at hw
  have hnotmem : (1006 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (1006 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (1006 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (1006 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (1006 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (1006 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0124

/-- finite transport leaf j=125, original=1007 -/
lemma transport_leaf_0125 : w 125 = (288:M) + 576 := by
  let j : Fin 1024 := ⟨125, by omega⟩
  have horder : order j = (1007 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (288:M) := by
    rw [horder]
    exact point1_basis_1007
  have hw := w_from_basis j (288:M) hb
  rw [horder] at hw
  have hmem : (1007 : Fin 1024) ∈ inactive.erase 1023 := by
    change (1007 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0125

/-- finite transport leaf j=126, original=993 -/
lemma transport_leaf_0126 : w 126 = (2147483599:M) := by
  let j : Fin 1024 := ⟨126, by omega⟩
  have horder : order j = (993 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483599:M) := by
    rw [horder]
    exact point1_basis_993
  have hw := w_from_basis j (2147483599:M) hb
  rw [horder] at hw
  have hnotmem : (993 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (993 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (993 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (993 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (993 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (993 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0126

/-- finite transport leaf j=127, original=1009 -/
lemma transport_leaf_0127 : w 127 = (96:M) + 576 := by
  let j : Fin 1024 := ⟨127, by omega⟩
  have horder : order j = (1009 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (96:M) := by
    rw [horder]
    exact point1_basis_1009
  have hw := w_from_basis j (96:M) hb
  rw [horder] at hw
  have hmem : (1009 : Fin 1024) ∈ inactive.erase 1023 := by
    change (1009 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0127

/-- finite transport leaf j=224, original=780 -/
lemma transport_leaf_0224 : w 224 = (2147483575:M) := by
  let j : Fin 1024 := ⟨224, by omega⟩
  have horder : order j = (780 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483575:M) := by
    rw [horder]
    exact point1_basis_780
  have hw := w_from_basis j (2147483575:M) hb
  rw [horder] at hw
  have hnotmem : (780 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (780 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (780 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (780 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (780 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (780 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0224

/-- finite transport leaf j=225, original=781 -/
lemma transport_leaf_0225 : w 225 = (36:M) + 576 := by
  let j : Fin 1024 := ⟨225, by omega⟩
  have horder : order j = (781 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (36:M) := by
    rw [horder]
    exact point1_basis_781
  have hw := w_from_basis j (36:M) hb
  rw [horder] at hw
  have hmem : (781 : Fin 1024) ∈ inactive.erase 1023 := by
    change (781 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0225

/-- finite transport leaf j=226, original=796 -/
lemma transport_leaf_0226 : w 226 = (144:M) := by
  let j : Fin 1024 := ⟨226, by omega⟩
  have horder : order j = (796 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (144:M) := by
    rw [horder]
    exact point1_basis_796
  have hw := w_from_basis j (144:M) hb
  rw [horder] at hw
  have hnotmem : (796 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (796 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (796 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (796 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (796 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (796 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0226

end
end AspisR19.R759Point1TransportLeaves
