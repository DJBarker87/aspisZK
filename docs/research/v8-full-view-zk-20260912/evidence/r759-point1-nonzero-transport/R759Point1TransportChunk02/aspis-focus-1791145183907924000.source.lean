import AspisV8R19.R755Point1BasisTransport
import AspisV8R19.R753Point1BasisChunk00
import AspisV8R19.R753Point1BasisChunk01
import AspisV8R19.R753Point1BasisChunk02
import AspisV8R19.R753Point1BasisChunk03
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

/-- finite transport leaf j=355, original=795 -/
lemma transport_leaf_0355 : w 355 = (2147483551:M) := by
  let j : Fin 1024 := ⟨355, by omega⟩
  have horder : order j = (795 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483551:M) := by
    rw [horder]
    exact point1_basis_795
  have hw := w_from_basis j (2147483551:M) hb
  rw [horder] at hw
  have hnotmem : (795 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (795 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (795 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (795 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (795 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (795 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0355

/-- finite transport leaf j=356, original=810 -/
lemma transport_leaf_0356 : w 356 = (128:M) + 576 := by
  let j : Fin 1024 := ⟨356, by omega⟩
  have horder : order j = (810 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (128:M) := by
    rw [horder]
    exact point1_basis_810
  have hw := w_from_basis j (128:M) hb
  rw [horder] at hw
  have hmem : (810 : Fin 1024) ∈ inactive.erase 1023 := by
    change (810 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0356

/-- finite transport leaf j=357, original=811 -/
lemma transport_leaf_0357 : w 357 = (2147483583:M) := by
  let j : Fin 1024 := ⟨357, by omega⟩
  have horder : order j = (811 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483583:M) := by
    rw [horder]
    exact point1_basis_811
  have hw := w_from_basis j (2147483583:M) hb
  rw [horder] at hw
  have hnotmem : (811 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (811 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (811 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (811 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (811 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (811 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0357

/-- finite transport leaf j=358, original=826 -/
lemma transport_leaf_0358 : w 358 = (2147483391:M) + 576 := by
  let j : Fin 1024 := ⟨358, by omega⟩
  have horder : order j = (826 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483391:M) := by
    rw [horder]
    exact point1_basis_826
  have hw := w_from_basis j (2147483391:M) hb
  rw [horder] at hw
  have hmem : (826 : Fin 1024) ∈ inactive.erase 1023 := by
    change (826 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0358

/-- finite transport leaf j=359, original=827 -/
lemma transport_leaf_0359 : w 359 = (128:M) := by
  let j : Fin 1024 := ⟨359, by omega⟩
  have horder : order j = (827 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (128:M) := by
    rw [horder]
    exact point1_basis_827
  have hw := w_from_basis j (128:M) hb
  rw [horder] at hw
  have hnotmem : (827 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (827 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (827 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (827 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (827 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (827 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0359

/-- finite transport leaf j=360, original=842 -/
lemma transport_leaf_0360 : w 360 = (144:M) + 576 := by
  let j : Fin 1024 := ⟨360, by omega⟩
  have horder : order j = (842 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (144:M) := by
    rw [horder]
    exact point1_basis_842
  have hw := w_from_basis j (144:M) hb
  rw [horder] at hw
  have hmem : (842 : Fin 1024) ∈ inactive.erase 1023 := by
    change (842 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0360

/-- finite transport leaf j=361, original=843 -/
lemma transport_leaf_0361 : w 361 = (2147483575:M) := by
  let j : Fin 1024 := ⟨361, by omega⟩
  have horder : order j = (843 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483575:M) := by
    rw [horder]
    exact point1_basis_843
  have hw := w_from_basis j (2147483575:M) hb
  rw [horder] at hw
  have hnotmem : (843 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (843 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (843 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (843 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (843 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (843 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0361

/-- finite transport leaf j=362, original=858 -/
lemma transport_leaf_0362 : w 362 = (2147483359:M) + 576 := by
  let j : Fin 1024 := ⟨362, by omega⟩
  have horder : order j = (858 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483359:M) := by
    rw [horder]
    exact point1_basis_858
  have hw := w_from_basis j (2147483359:M) hb
  rw [horder] at hw
  have hmem : (858 : Fin 1024) ∈ inactive.erase 1023 := by
    change (858 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0362

/-- finite transport leaf j=363, original=859 -/
lemma transport_leaf_0363 : w 363 = (144:M) + 576 := by
  let j : Fin 1024 := ⟨363, by omega⟩
  have horder : order j = (859 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (144:M) := by
    rw [horder]
    exact point1_basis_859
  have hw := w_from_basis j (144:M) hb
  rw [horder] at hw
  have hmem : (859 : Fin 1024) ∈ inactive.erase 1023 := by
    change (859 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0363

/-- finite transport leaf j=364, original=874 -/
lemma transport_leaf_0364 : w 364 = (2147483455:M) + 576 := by
  let j : Fin 1024 := ⟨364, by omega⟩
  have horder : order j = (874 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483455:M) := by
    rw [horder]
    exact point1_basis_874
  have hw := w_from_basis j (2147483455:M) hb
  rw [horder] at hw
  have hmem : (874 : Fin 1024) ∈ inactive.erase 1023 := by
    change (874 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0364

/-- finite transport leaf j=365, original=875 -/
lemma transport_leaf_0365 : w 365 = (96:M) := by
  let j : Fin 1024 := ⟨365, by omega⟩
  have horder : order j = (875 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (96:M) := by
    rw [horder]
    exact point1_basis_875
  have hw := w_from_basis j (96:M) hb
  rw [horder] at hw
  have hnotmem : (875 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (875 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (875 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (875 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (875 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (875 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0365

/-- finite transport leaf j=366, original=890 -/
lemma transport_leaf_0366 : w 366 = (384:M) + 576 := by
  let j : Fin 1024 := ⟨366, by omega⟩
  have horder : order j = (890 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (384:M) := by
    rw [horder]
    exact point1_basis_890
  have hw := w_from_basis j (384:M) hb
  rw [horder] at hw
  have hmem : (890 : Fin 1024) ∈ inactive.erase 1023 := by
    change (890 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0366

/-- finite transport leaf j=367, original=891 -/
lemma transport_leaf_0367 : w 367 = (2147483455:M) := by
  let j : Fin 1024 := ⟨367, by omega⟩
  have horder : order j = (891 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483455:M) := by
    rw [horder]
    exact point1_basis_891
  have hw := w_from_basis j (2147483455:M) hb
  rw [horder] at hw
  have hnotmem : (891 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (891 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (891 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (891 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (891 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (891 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0367

/-- finite transport leaf j=368, original=906 -/
lemma transport_leaf_0368 : w 368 = (192:M) + 576 := by
  let j : Fin 1024 := ⟨368, by omega⟩
  have horder : order j = (906 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (192:M) := by
    rw [horder]
    exact point1_basis_906
  have hw := w_from_basis j (192:M) hb
  rw [horder] at hw
  have hmem : (906 : Fin 1024) ∈ inactive.erase 1023 := by
    change (906 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0368

/-- finite transport leaf j=369, original=907 -/
lemma transport_leaf_0369 : w 369 = (2147483551:M) + 576 := by
  let j : Fin 1024 := ⟨369, by omega⟩
  have horder : order j = (907 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483551:M) := by
    rw [horder]
    exact point1_basis_907
  have hw := w_from_basis j (2147483551:M) hb
  rw [horder] at hw
  have hmem : (907 : Fin 1024) ∈ inactive.erase 1023 := by
    change (907 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0369

/-- finite transport leaf j=370, original=922 -/
lemma transport_leaf_0370 : w 370 = (2147483263:M) := by
  let j : Fin 1024 := ⟨370, by omega⟩
  have horder : order j = (922 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483263:M) := by
    rw [horder]
    exact point1_basis_922
  have hw := w_from_basis j (2147483263:M) hb
  rw [horder] at hw
  have hnotmem : (922 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (922 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (922 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (922 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (922 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (922 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0370

/-- finite transport leaf j=371, original=923 -/
lemma transport_leaf_0371 : w 371 = (192:M) + 576 := by
  let j : Fin 1024 := ⟨371, by omega⟩
  have horder : order j = (923 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (192:M) := by
    rw [horder]
    exact point1_basis_923
  have hw := w_from_basis j (192:M) hb
  rw [horder] at hw
  have hmem : (923 : Fin 1024) ∈ inactive.erase 1023 := by
    change (923 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0371

/-- finite transport leaf j=372, original=938 -/
lemma transport_leaf_0372 : w 372 = (2147483391:M) := by
  let j : Fin 1024 := ⟨372, by omega⟩
  have horder : order j = (938 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483391:M) := by
    rw [horder]
    exact point1_basis_938
  have hw := w_from_basis j (2147483391:M) hb
  rw [horder] at hw
  have hnotmem : (938 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (938 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (938 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (938 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (938 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (938 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0372

/-- finite transport leaf j=373, original=939 -/
lemma transport_leaf_0373 : w 373 = (128:M) + 576 := by
  let j : Fin 1024 := ⟨373, by omega⟩
  have horder : order j = (939 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (128:M) := by
    rw [horder]
    exact point1_basis_939
  have hw := w_from_basis j (128:M) hb
  rw [horder] at hw
  have hmem : (939 : Fin 1024) ∈ inactive.erase 1023 := by
    change (939 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0373

/-- finite transport leaf j=374, original=954 -/
lemma transport_leaf_0374 : w 374 = (512:M) := by
  let j : Fin 1024 := ⟨374, by omega⟩
  have horder : order j = (954 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (512:M) := by
    rw [horder]
    exact point1_basis_954
  have hw := w_from_basis j (512:M) hb
  rw [horder] at hw
  have hnotmem : (954 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (954 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (954 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (954 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (954 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (954 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0374

/-- finite transport leaf j=375, original=955 -/
lemma transport_leaf_0375 : w 375 = (2147483391:M) + 576 := by
  let j : Fin 1024 := ⟨375, by omega⟩
  have horder : order j = (955 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483391:M) := by
    rw [horder]
    exact point1_basis_955
  have hw := w_from_basis j (2147483391:M) hb
  rw [horder] at hw
  have hmem : (955 : Fin 1024) ∈ inactive.erase 1023 := by
    change (955 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0375

/-- finite transport leaf j=376, original=970 -/
lemma transport_leaf_0376 : w 376 = (2147483359:M) := by
  let j : Fin 1024 := ⟨376, by omega⟩
  have horder : order j = (970 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483359:M) := by
    rw [horder]
    exact point1_basis_970
  have hw := w_from_basis j (2147483359:M) hb
  rw [horder] at hw
  have hnotmem : (970 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (970 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (970 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (970 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (970 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (970 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0376

/-- finite transport leaf j=377, original=971 -/
lemma transport_leaf_0377 : w 377 = (144:M) + 576 := by
  let j : Fin 1024 := ⟨377, by omega⟩
  have horder : order j = (971 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (144:M) := by
    rw [horder]
    exact point1_basis_971
  have hw := w_from_basis j (144:M) hb
  rw [horder] at hw
  have hmem : (971 : Fin 1024) ∈ inactive.erase 1023 := by
    change (971 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0377

/-- finite transport leaf j=378, original=986 -/
lemma transport_leaf_0378 : w 378 = (576:M) := by
  let j : Fin 1024 := ⟨378, by omega⟩
  have horder : order j = (986 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (576:M) := by
    rw [horder]
    exact point1_basis_986
  have hw := w_from_basis j (576:M) hb
  rw [horder] at hw
  have hnotmem : (986 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (986 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (986 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (986 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (986 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (986 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0378

/-- finite transport leaf j=379, original=987 -/
lemma transport_leaf_0379 : w 379 = (2147483359:M) + 576 := by
  let j : Fin 1024 := ⟨379, by omega⟩
  have horder : order j = (987 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483359:M) := by
    rw [horder]
    exact point1_basis_987
  have hw := w_from_basis j (2147483359:M) hb
  rw [horder] at hw
  have hmem : (987 : Fin 1024) ∈ inactive.erase 1023 := by
    change (987 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0379

/-- finite transport leaf j=380, original=1002 -/
lemma transport_leaf_0380 : w 380 = (384:M) := by
  let j : Fin 1024 := ⟨380, by omega⟩
  have horder : order j = (1002 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (384:M) := by
    rw [horder]
    exact point1_basis_1002
  have hw := w_from_basis j (384:M) hb
  rw [horder] at hw
  have hnotmem : (1002 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (1002 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (1002 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (1002 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (1002 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (1002 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0380

/-- finite transport leaf j=381, original=1003 -/
lemma transport_leaf_0381 : w 381 = (2147483455:M) + 576 := by
  let j : Fin 1024 := ⟨381, by omega⟩
  have horder : order j = (1003 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483455:M) := by
    rw [horder]
    exact point1_basis_1003
  have hw := w_from_basis j (2147483455:M) hb
  rw [horder] at hw
  have hmem : (1003 : Fin 1024) ∈ inactive.erase 1023 := by
    change (1003 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0381

/-- finite transport leaf j=382, original=1018 -/
lemma transport_leaf_0382 : w 382 = (2147482879:M) := by
  let j : Fin 1024 := ⟨382, by omega⟩
  have horder : order j = (1018 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147482879:M) := by
    rw [horder]
    exact point1_basis_1018
  have hw := w_from_basis j (2147482879:M) hb
  rw [horder] at hw
  have hnotmem : (1018 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (1018 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (1018 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (1018 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (1018 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (1018 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0382

/-- finite transport leaf j=383, original=1019 -/
lemma transport_leaf_0383 : w 383 = (384:M) + 576 := by
  let j : Fin 1024 := ⟨383, by omega⟩
  have horder : order j = (1019 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (384:M) := by
    rw [horder]
    exact point1_basis_1019
  have hw := w_from_basis j (384:M) hb
  rw [horder] at hw
  have hmem : (1019 : Fin 1024) ∈ inactive.erase 1023 := by
    change (1019 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0383

/-- finite transport leaf j=480, original=776 -/
lemma transport_leaf_0480 : w 480 = (48:M) + 576 := by
  let j : Fin 1024 := ⟨480, by omega⟩
  have horder : order j = (776 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (48:M) := by
    rw [horder]
    exact point1_basis_776
  have hw := w_from_basis j (48:M) hb
  rw [horder] at hw
  have hmem : (776 : Fin 1024) ∈ inactive.erase 1023 := by
    change (776 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0480

/-- finite transport leaf j=481, original=777 -/
lemma transport_leaf_0481 : w 481 = (2147483623:M) + 576 := by
  let j : Fin 1024 := ⟨481, by omega⟩
  have horder : order j = (777 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483623:M) := by
    rw [horder]
    exact point1_basis_777
  have hw := w_from_basis j (2147483623:M) hb
  rw [horder] at hw
  have hmem : (777 : Fin 1024) ∈ inactive.erase 1023 := by
    change (777 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0481

/-- finite transport leaf j=482, original=792 -/
lemma transport_leaf_0482 : w 482 = (2147483551:M) + 576 := by
  let j : Fin 1024 := ⟨482, by omega⟩
  have horder : order j = (792 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483551:M) := by
    rw [horder]
    exact point1_basis_792
  have hw := w_from_basis j (2147483551:M) hb
  rw [horder] at hw
  have hmem : (792 : Fin 1024) ∈ inactive.erase 1023 := by
    change (792 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0482

end
end AspisR19.R759Point1TransportLeaves
