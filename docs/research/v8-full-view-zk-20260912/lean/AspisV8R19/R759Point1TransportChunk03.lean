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

/-- finite transport leaf j=496, original=904 -/
lemma transport_leaf_0496 : w 496 = (2147483551:M) + 576 := by
  let j : Fin 1024 := ⟨496, by omega⟩
  have horder : order j = (904 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483551:M) := by
    rw [horder]
    exact point1_basis_904
  have hw := w_from_basis j (2147483551:M) hb
  rw [horder] at hw
  have hmem : (904 : Fin 1024) ∈ inactive.erase 1023 := by
    change (904 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0496

/-- finite transport leaf j=497, original=905 -/
lemma transport_leaf_0497 : w 497 = (48:M) + 576 := by
  let j : Fin 1024 := ⟨497, by omega⟩
  have horder : order j = (905 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (48:M) := by
    rw [horder]
    exact point1_basis_905
  have hw := w_from_basis j (48:M) hb
  rw [horder] at hw
  have hmem : (905 : Fin 1024) ∈ inactive.erase 1023 := by
    change (905 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0497

/-- finite transport leaf j=498, original=920 -/
lemma transport_leaf_0498 : w 498 = (192:M) + 576 := by
  let j : Fin 1024 := ⟨498, by omega⟩
  have horder : order j = (920 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (192:M) := by
    rw [horder]
    exact point1_basis_920
  have hw := w_from_basis j (192:M) hb
  rw [horder] at hw
  have hmem : (920 : Fin 1024) ∈ inactive.erase 1023 := by
    change (920 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0498

/-- finite transport leaf j=499, original=921 -/
lemma transport_leaf_0499 : w 499 = (2147483551:M) := by
  let j : Fin 1024 := ⟨499, by omega⟩
  have horder : order j = (921 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483551:M) := by
    rw [horder]
    exact point1_basis_921
  have hw := w_from_basis j (2147483551:M) hb
  rw [horder] at hw
  have hnotmem : (921 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (921 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (921 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (921 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (921 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (921 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0499

/-- finite transport leaf j=500, original=936 -/
lemma transport_leaf_0500 : w 500 = (128:M) + 576 := by
  let j : Fin 1024 := ⟨500, by omega⟩
  have horder : order j = (936 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (128:M) := by
    rw [horder]
    exact point1_basis_936
  have hw := w_from_basis j (128:M) hb
  rw [horder] at hw
  have hmem : (936 : Fin 1024) ∈ inactive.erase 1023 := by
    change (936 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0500

/-- finite transport leaf j=501, original=937 -/
lemma transport_leaf_0501 : w 501 = (2147483583:M) := by
  let j : Fin 1024 := ⟨501, by omega⟩
  have horder : order j = (937 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483583:M) := by
    rw [horder]
    exact point1_basis_937
  have hw := w_from_basis j (2147483583:M) hb
  rw [horder] at hw
  have hnotmem : (937 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (937 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (937 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (937 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (937 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (937 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0501

/-- finite transport leaf j=502, original=952 -/
lemma transport_leaf_0502 : w 502 = (2147483391:M) + 576 := by
  let j : Fin 1024 := ⟨502, by omega⟩
  have horder : order j = (952 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483391:M) := by
    rw [horder]
    exact point1_basis_952
  have hw := w_from_basis j (2147483391:M) hb
  rw [horder] at hw
  have hmem : (952 : Fin 1024) ∈ inactive.erase 1023 := by
    change (952 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0502

/-- finite transport leaf j=503, original=953 -/
lemma transport_leaf_0503 : w 503 = (128:M) := by
  let j : Fin 1024 := ⟨503, by omega⟩
  have horder : order j = (953 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (128:M) := by
    rw [horder]
    exact point1_basis_953
  have hw := w_from_basis j (128:M) hb
  rw [horder] at hw
  have hnotmem : (953 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (953 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (953 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (953 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (953 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (953 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0503

/-- finite transport leaf j=504, original=968 -/
lemma transport_leaf_0504 : w 504 = (144:M) + 576 := by
  let j : Fin 1024 := ⟨504, by omega⟩
  have horder : order j = (968 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (144:M) := by
    rw [horder]
    exact point1_basis_968
  have hw := w_from_basis j (144:M) hb
  rw [horder] at hw
  have hmem : (968 : Fin 1024) ∈ inactive.erase 1023 := by
    change (968 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0504

/-- finite transport leaf j=505, original=969 -/
lemma transport_leaf_0505 : w 505 = (2147483575:M) := by
  let j : Fin 1024 := ⟨505, by omega⟩
  have horder : order j = (969 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483575:M) := by
    rw [horder]
    exact point1_basis_969
  have hw := w_from_basis j (2147483575:M) hb
  rw [horder] at hw
  have hnotmem : (969 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (969 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (969 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (969 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (969 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (969 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0505

/-- finite transport leaf j=506, original=984 -/
lemma transport_leaf_0506 : w 506 = (2147483359:M) + 576 := by
  let j : Fin 1024 := ⟨506, by omega⟩
  have horder : order j = (984 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483359:M) := by
    rw [horder]
    exact point1_basis_984
  have hw := w_from_basis j (2147483359:M) hb
  rw [horder] at hw
  have hmem : (984 : Fin 1024) ∈ inactive.erase 1023 := by
    change (984 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0506

/-- finite transport leaf j=507, original=985 -/
lemma transport_leaf_0507 : w 507 = (144:M) := by
  let j : Fin 1024 := ⟨507, by omega⟩
  have horder : order j = (985 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (144:M) := by
    rw [horder]
    exact point1_basis_985
  have hw := w_from_basis j (144:M) hb
  rw [horder] at hw
  have hnotmem : (985 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (985 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (985 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (985 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (985 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (985 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0507

/-- finite transport leaf j=508, original=1000 -/
lemma transport_leaf_0508 : w 508 = (2147483455:M) + 576 := by
  let j : Fin 1024 := ⟨508, by omega⟩
  have horder : order j = (1000 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483455:M) := by
    rw [horder]
    exact point1_basis_1000
  have hw := w_from_basis j (2147483455:M) hb
  rw [horder] at hw
  have hmem : (1000 : Fin 1024) ∈ inactive.erase 1023 := by
    change (1000 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0508

/-- finite transport leaf j=509, original=1001 -/
lemma transport_leaf_0509 : w 509 = (96:M) := by
  let j : Fin 1024 := ⟨509, by omega⟩
  have horder : order j = (1001 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (96:M) := by
    rw [horder]
    exact point1_basis_1001
  have hw := w_from_basis j (96:M) hb
  rw [horder] at hw
  have hnotmem : (1001 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (1001 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (1001 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (1001 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (1001 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (1001 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0509

/-- finite transport leaf j=510, original=1016 -/
lemma transport_leaf_0510 : w 510 = (384:M) + 576 := by
  let j : Fin 1024 := ⟨510, by omega⟩
  have horder : order j = (1016 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (384:M) := by
    rw [horder]
    exact point1_basis_1016
  have hw := w_from_basis j (384:M) hb
  rw [horder] at hw
  have hmem : (1016 : Fin 1024) ∈ inactive.erase 1023 := by
    change (1016 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0510

/-- finite transport leaf j=511, original=1017 -/
lemma transport_leaf_0511 : w 511 = (2147483455:M) := by
  let j : Fin 1024 := ⟨511, by omega⟩
  have horder : order j = (1017 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483455:M) := by
    rw [horder]
    exact point1_basis_1017
  have hw := w_from_basis j (2147483455:M) hb
  rw [horder] at hw
  have hnotmem : (1017 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (1017 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (1017 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (1017 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (1017 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (1017 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0511

/-- finite transport leaf j=608, original=774 -/
lemma transport_leaf_0608 : w 608 = (2147483575:M) + 576 := by
  let j : Fin 1024 := ⟨608, by omega⟩
  have horder : order j = (774 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483575:M) := by
    rw [horder]
    exact point1_basis_774
  have hw := w_from_basis j (2147483575:M) hb
  rw [horder] at hw
  have hmem : (774 : Fin 1024) ∈ inactive.erase 1023 := by
    change (774 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0608

/-- finite transport leaf j=609, original=775 -/
lemma transport_leaf_0609 : w 609 = (36:M) + 576 := by
  let j : Fin 1024 := ⟨609, by omega⟩
  have horder : order j = (775 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (36:M) := by
    rw [horder]
    exact point1_basis_775
  have hw := w_from_basis j (36:M) hb
  rw [horder] at hw
  have hmem : (775 : Fin 1024) ∈ inactive.erase 1023 := by
    change (775 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0609

/-- finite transport leaf j=610, original=790 -/
lemma transport_leaf_0610 : w 610 = (144:M) + 576 := by
  let j : Fin 1024 := ⟨610, by omega⟩
  have horder : order j = (790 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (144:M) := by
    rw [horder]
    exact point1_basis_790
  have hw := w_from_basis j (144:M) hb
  rw [horder] at hw
  have hmem : (790 : Fin 1024) ∈ inactive.erase 1023 := by
    change (790 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0610

/-- finite transport leaf j=624, original=902 -/
lemma transport_leaf_0624 : w 624 = (144:M) + 576 := by
  let j : Fin 1024 := ⟨624, by omega⟩
  have horder : order j = (902 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (144:M) := by
    rw [horder]
    exact point1_basis_902
  have hw := w_from_basis j (144:M) hb
  rw [horder] at hw
  have hmem : (902 : Fin 1024) ∈ inactive.erase 1023 := by
    change (902 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0624

/-- finite transport leaf j=625, original=903 -/
lemma transport_leaf_0625 : w 625 = (2147483575:M) + 576 := by
  let j : Fin 1024 := ⟨625, by omega⟩
  have horder : order j = (903 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483575:M) := by
    rw [horder]
    exact point1_basis_903
  have hw := w_from_basis j (2147483575:M) hb
  rw [horder] at hw
  have hmem : (903 : Fin 1024) ∈ inactive.erase 1023 := by
    change (903 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0625

/-- finite transport leaf j=626, original=918 -/
lemma transport_leaf_0626 : w 626 = (2147483359:M) := by
  let j : Fin 1024 := ⟨626, by omega⟩
  have horder : order j = (918 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483359:M) := by
    rw [horder]
    exact point1_basis_918
  have hw := w_from_basis j (2147483359:M) hb
  rw [horder] at hw
  have hnotmem : (918 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (918 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (918 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (918 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (918 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (918 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0626

/-- finite transport leaf j=627, original=919 -/
lemma transport_leaf_0627 : w 627 = (144:M) + 576 := by
  let j : Fin 1024 := ⟨627, by omega⟩
  have horder : order j = (919 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (144:M) := by
    rw [horder]
    exact point1_basis_919
  have hw := w_from_basis j (144:M) hb
  rw [horder] at hw
  have hmem : (919 : Fin 1024) ∈ inactive.erase 1023 := by
    change (919 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0627

/-- finite transport leaf j=628, original=934 -/
lemma transport_leaf_0628 : w 628 = (2147483455:M) := by
  let j : Fin 1024 := ⟨628, by omega⟩
  have horder : order j = (934 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483455:M) := by
    rw [horder]
    exact point1_basis_934
  have hw := w_from_basis j (2147483455:M) hb
  rw [horder] at hw
  have hnotmem : (934 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (934 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (934 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (934 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (934 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (934 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0628

/-- finite transport leaf j=629, original=935 -/
lemma transport_leaf_0629 : w 629 = (96:M) + 576 := by
  let j : Fin 1024 := ⟨629, by omega⟩
  have horder : order j = (935 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (96:M) := by
    rw [horder]
    exact point1_basis_935
  have hw := w_from_basis j (96:M) hb
  rw [horder] at hw
  have hmem : (935 : Fin 1024) ∈ inactive.erase 1023 := by
    change (935 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0629

/-- finite transport leaf j=630, original=950 -/
lemma transport_leaf_0630 : w 630 = (384:M) := by
  let j : Fin 1024 := ⟨630, by omega⟩
  have horder : order j = (950 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (384:M) := by
    rw [horder]
    exact point1_basis_950
  have hw := w_from_basis j (384:M) hb
  rw [horder] at hw
  have hnotmem : (950 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (950 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (950 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (950 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (950 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (950 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0630

/-- finite transport leaf j=631, original=951 -/
lemma transport_leaf_0631 : w 631 = (2147483455:M) + 576 := by
  let j : Fin 1024 := ⟨631, by omega⟩
  have horder : order j = (951 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483455:M) := by
    rw [horder]
    exact point1_basis_951
  have hw := w_from_basis j (2147483455:M) hb
  rw [horder] at hw
  have hmem : (951 : Fin 1024) ∈ inactive.erase 1023 := by
    change (951 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0631

/-- finite transport leaf j=632, original=966 -/
lemma transport_leaf_0632 : w 632 = (2147483431:M) := by
  let j : Fin 1024 := ⟨632, by omega⟩
  have horder : order j = (966 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483431:M) := by
    rw [horder]
    exact point1_basis_966
  have hw := w_from_basis j (2147483431:M) hb
  rw [horder] at hw
  have hnotmem : (966 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (966 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (966 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (966 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (966 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (966 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0632

/-- finite transport leaf j=633, original=967 -/
lemma transport_leaf_0633 : w 633 = (108:M) + 576 := by
  let j : Fin 1024 := ⟨633, by omega⟩
  have horder : order j = (967 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (108:M) := by
    rw [horder]
    exact point1_basis_967
  have hw := w_from_basis j (108:M) hb
  rw [horder] at hw
  have hmem : (967 : Fin 1024) ∈ inactive.erase 1023 := by
    change (967 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0633

/-- finite transport leaf j=634, original=982 -/
lemma transport_leaf_0634 : w 634 = (432:M) := by
  let j : Fin 1024 := ⟨634, by omega⟩
  have horder : order j = (982 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (432:M) := by
    rw [horder]
    exact point1_basis_982
  have hw := w_from_basis j (432:M) hb
  rw [horder] at hw
  have hnotmem : (982 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (982 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (982 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (982 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (982 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (982 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0634

/-- finite transport leaf j=635, original=983 -/
lemma transport_leaf_0635 : w 635 = (2147483431:M) + 576 := by
  let j : Fin 1024 := ⟨635, by omega⟩
  have horder : order j = (983 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483431:M) := by
    rw [horder]
    exact point1_basis_983
  have hw := w_from_basis j (2147483431:M) hb
  rw [horder] at hw
  have hmem : (983 : Fin 1024) ∈ inactive.erase 1023 := by
    change (983 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0635

/-- finite transport leaf j=636, original=998 -/
lemma transport_leaf_0636 : w 636 = (288:M) := by
  let j : Fin 1024 := ⟨636, by omega⟩
  have horder : order j = (998 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (288:M) := by
    rw [horder]
    exact point1_basis_998
  have hw := w_from_basis j (288:M) hb
  rw [horder] at hw
  have hnotmem : (998 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (998 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (998 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (998 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (998 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (998 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0636

end
end AspisR19.R759Point1TransportLeaves
