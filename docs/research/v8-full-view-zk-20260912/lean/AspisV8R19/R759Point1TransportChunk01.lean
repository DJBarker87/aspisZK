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

/-- finite transport leaf j=227, original=797 -/
lemma transport_leaf_0227 : w 227 = (2147483575:M) + 576 := by
  let j : Fin 1024 := ⟨227, by omega⟩
  have horder : order j = (797 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483575:M) := by
    rw [horder]
    exact point1_basis_797
  have hw := w_from_basis j (2147483575:M) hb
  rw [horder] at hw
  have hmem : (797 : Fin 1024) ∈ inactive.erase 1023 := by
    change (797 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0227

/-- finite transport leaf j=228, original=812 -/
lemma transport_leaf_0228 : w 228 = (96:M) := by
  let j : Fin 1024 := ⟨228, by omega⟩
  have horder : order j = (812 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (96:M) := by
    rw [horder]
    exact point1_basis_812
  have hw := w_from_basis j (96:M) hb
  rw [horder] at hw
  have hnotmem : (812 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (812 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (812 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (812 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (812 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (812 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0228

/-- finite transport leaf j=229, original=813 -/
lemma transport_leaf_0229 : w 229 = (2147483599:M) + 576 := by
  let j : Fin 1024 := ⟨229, by omega⟩
  have horder : order j = (813 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483599:M) := by
    rw [horder]
    exact point1_basis_813
  have hw := w_from_basis j (2147483599:M) hb
  rw [horder] at hw
  have hmem : (813 : Fin 1024) ∈ inactive.erase 1023 := by
    change (813 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0229

/-- finite transport leaf j=230, original=828 -/
lemma transport_leaf_0230 : w 230 = (2147483455:M) := by
  let j : Fin 1024 := ⟨230, by omega⟩
  have horder : order j = (828 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483455:M) := by
    rw [horder]
    exact point1_basis_828
  have hw := w_from_basis j (2147483455:M) hb
  rw [horder] at hw
  have hnotmem : (828 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (828 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (828 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (828 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (828 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (828 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0230

/-- finite transport leaf j=231, original=829 -/
lemma transport_leaf_0231 : w 231 = (96:M) + 576 := by
  let j : Fin 1024 := ⟨231, by omega⟩
  have horder : order j = (829 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (96:M) := by
    rw [horder]
    exact point1_basis_829
  have hw := w_from_basis j (96:M) hb
  rw [horder] at hw
  have hmem : (829 : Fin 1024) ∈ inactive.erase 1023 := by
    change (829 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0231

/-- finite transport leaf j=232, original=844 -/
lemma transport_leaf_0232 : w 232 = (108:M) := by
  let j : Fin 1024 := ⟨232, by omega⟩
  have horder : order j = (844 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (108:M) := by
    rw [horder]
    exact point1_basis_844
  have hw := w_from_basis j (108:M) hb
  rw [horder] at hw
  have hnotmem : (844 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (844 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (844 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (844 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (844 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (844 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0232

/-- finite transport leaf j=233, original=845 -/
lemma transport_leaf_0233 : w 233 = (2147483593:M) + 576 := by
  let j : Fin 1024 := ⟨233, by omega⟩
  have horder : order j = (845 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483593:M) := by
    rw [horder]
    exact point1_basis_845
  have hw := w_from_basis j (2147483593:M) hb
  rw [horder] at hw
  have hmem : (845 : Fin 1024) ∈ inactive.erase 1023 := by
    change (845 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0233

/-- finite transport leaf j=234, original=860 -/
lemma transport_leaf_0234 : w 234 = (2147483431:M) := by
  let j : Fin 1024 := ⟨234, by omega⟩
  have horder : order j = (860 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483431:M) := by
    rw [horder]
    exact point1_basis_860
  have hw := w_from_basis j (2147483431:M) hb
  rw [horder] at hw
  have hnotmem : (860 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (860 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (860 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (860 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (860 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (860 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0234

/-- finite transport leaf j=235, original=861 -/
lemma transport_leaf_0235 : w 235 = (108:M) + 576 := by
  let j : Fin 1024 := ⟨235, by omega⟩
  have horder : order j = (861 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (108:M) := by
    rw [horder]
    exact point1_basis_861
  have hw := w_from_basis j (108:M) hb
  rw [horder] at hw
  have hmem : (861 : Fin 1024) ∈ inactive.erase 1023 := by
    change (861 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0235

/-- finite transport leaf j=236, original=876 -/
lemma transport_leaf_0236 : w 236 = (2147483503:M) := by
  let j : Fin 1024 := ⟨236, by omega⟩
  have horder : order j = (876 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483503:M) := by
    rw [horder]
    exact point1_basis_876
  have hw := w_from_basis j (2147483503:M) hb
  rw [horder] at hw
  have hnotmem : (876 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (876 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (876 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (876 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (876 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (876 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0236

/-- finite transport leaf j=237, original=877 -/
lemma transport_leaf_0237 : w 237 = (72:M) + 576 := by
  let j : Fin 1024 := ⟨237, by omega⟩
  have horder : order j = (877 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (72:M) := by
    rw [horder]
    exact point1_basis_877
  have hw := w_from_basis j (72:M) hb
  rw [horder] at hw
  have hmem : (877 : Fin 1024) ∈ inactive.erase 1023 := by
    change (877 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0237

/-- finite transport leaf j=238, original=892 -/
lemma transport_leaf_0238 : w 238 = (288:M) := by
  let j : Fin 1024 := ⟨238, by omega⟩
  have horder : order j = (892 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (288:M) := by
    rw [horder]
    exact point1_basis_892
  have hw := w_from_basis j (288:M) hb
  rw [horder] at hw
  have hnotmem : (892 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (892 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (892 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (892 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (892 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (892 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0238

/-- finite transport leaf j=239, original=893 -/
lemma transport_leaf_0239 : w 239 = (2147483503:M) + 576 := by
  let j : Fin 1024 := ⟨239, by omega⟩
  have horder : order j = (893 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483503:M) := by
    rw [horder]
    exact point1_basis_893
  have hw := w_from_basis j (2147483503:M) hb
  rw [horder] at hw
  have hmem : (893 : Fin 1024) ∈ inactive.erase 1023 := by
    change (893 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0239

/-- finite transport leaf j=240, original=908 -/
lemma transport_leaf_0240 : w 240 = (144:M) := by
  let j : Fin 1024 := ⟨240, by omega⟩
  have horder : order j = (908 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (144:M) := by
    rw [horder]
    exact point1_basis_908
  have hw := w_from_basis j (144:M) hb
  rw [horder] at hw
  have hnotmem : (908 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (908 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (908 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (908 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (908 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (908 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0240

/-- finite transport leaf j=241, original=909 -/
lemma transport_leaf_0241 : w 241 = (2147483575:M) + 576 := by
  let j : Fin 1024 := ⟨241, by omega⟩
  have horder : order j = (909 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483575:M) := by
    rw [horder]
    exact point1_basis_909
  have hw := w_from_basis j (2147483575:M) hb
  rw [horder] at hw
  have hmem : (909 : Fin 1024) ∈ inactive.erase 1023 := by
    change (909 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0241

/-- finite transport leaf j=242, original=924 -/
lemma transport_leaf_0242 : w 242 = (2147483359:M) + 576 := by
  let j : Fin 1024 := ⟨242, by omega⟩
  have horder : order j = (924 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483359:M) := by
    rw [horder]
    exact point1_basis_924
  have hw := w_from_basis j (2147483359:M) hb
  rw [horder] at hw
  have hmem : (924 : Fin 1024) ∈ inactive.erase 1023 := by
    change (924 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0242

/-- finite transport leaf j=243, original=925 -/
lemma transport_leaf_0243 : w 243 = (144:M) := by
  let j : Fin 1024 := ⟨243, by omega⟩
  have horder : order j = (925 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (144:M) := by
    rw [horder]
    exact point1_basis_925
  have hw := w_from_basis j (144:M) hb
  rw [horder] at hw
  have hnotmem : (925 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (925 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (925 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (925 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (925 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (925 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0243

/-- finite transport leaf j=244, original=940 -/
lemma transport_leaf_0244 : w 244 = (2147483455:M) + 576 := by
  let j : Fin 1024 := ⟨244, by omega⟩
  have horder : order j = (940 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483455:M) := by
    rw [horder]
    exact point1_basis_940
  have hw := w_from_basis j (2147483455:M) hb
  rw [horder] at hw
  have hmem : (940 : Fin 1024) ∈ inactive.erase 1023 := by
    change (940 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0244

/-- finite transport leaf j=245, original=941 -/
lemma transport_leaf_0245 : w 245 = (96:M) := by
  let j : Fin 1024 := ⟨245, by omega⟩
  have horder : order j = (941 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (96:M) := by
    rw [horder]
    exact point1_basis_941
  have hw := w_from_basis j (96:M) hb
  rw [horder] at hw
  have hnotmem : (941 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (941 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (941 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (941 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (941 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (941 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0245

/-- finite transport leaf j=246, original=956 -/
lemma transport_leaf_0246 : w 246 = (384:M) + 576 := by
  let j : Fin 1024 := ⟨246, by omega⟩
  have horder : order j = (956 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (384:M) := by
    rw [horder]
    exact point1_basis_956
  have hw := w_from_basis j (384:M) hb
  rw [horder] at hw
  have hmem : (956 : Fin 1024) ∈ inactive.erase 1023 := by
    change (956 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0246

/-- finite transport leaf j=247, original=957 -/
lemma transport_leaf_0247 : w 247 = (2147483455:M) := by
  let j : Fin 1024 := ⟨247, by omega⟩
  have horder : order j = (957 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483455:M) := by
    rw [horder]
    exact point1_basis_957
  have hw := w_from_basis j (2147483455:M) hb
  rw [horder] at hw
  have hnotmem : (957 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (957 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (957 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (957 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (957 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (957 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0247

/-- finite transport leaf j=248, original=972 -/
lemma transport_leaf_0248 : w 248 = (2147483431:M) + 576 := by
  let j : Fin 1024 := ⟨248, by omega⟩
  have horder : order j = (972 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483431:M) := by
    rw [horder]
    exact point1_basis_972
  have hw := w_from_basis j (2147483431:M) hb
  rw [horder] at hw
  have hmem : (972 : Fin 1024) ∈ inactive.erase 1023 := by
    change (972 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0248

/-- finite transport leaf j=249, original=973 -/
lemma transport_leaf_0249 : w 249 = (108:M) := by
  let j : Fin 1024 := ⟨249, by omega⟩
  have horder : order j = (973 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (108:M) := by
    rw [horder]
    exact point1_basis_973
  have hw := w_from_basis j (108:M) hb
  rw [horder] at hw
  have hnotmem : (973 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (973 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (973 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (973 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (973 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (973 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0249

/-- finite transport leaf j=250, original=988 -/
lemma transport_leaf_0250 : w 250 = (432:M) + 576 := by
  let j : Fin 1024 := ⟨250, by omega⟩
  have horder : order j = (988 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (432:M) := by
    rw [horder]
    exact point1_basis_988
  have hw := w_from_basis j (432:M) hb
  rw [horder] at hw
  have hmem : (988 : Fin 1024) ∈ inactive.erase 1023 := by
    change (988 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0250

/-- finite transport leaf j=251, original=989 -/
lemma transport_leaf_0251 : w 251 = (2147483431:M) := by
  let j : Fin 1024 := ⟨251, by omega⟩
  have horder : order j = (989 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483431:M) := by
    rw [horder]
    exact point1_basis_989
  have hw := w_from_basis j (2147483431:M) hb
  rw [horder] at hw
  have hnotmem : (989 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (989 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (989 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (989 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (989 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (989 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0251

/-- finite transport leaf j=252, original=1004 -/
lemma transport_leaf_0252 : w 252 = (288:M) + 576 := by
  let j : Fin 1024 := ⟨252, by omega⟩
  have horder : order j = (1004 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (288:M) := by
    rw [horder]
    exact point1_basis_1004
  have hw := w_from_basis j (288:M) hb
  rw [horder] at hw
  have hmem : (1004 : Fin 1024) ∈ inactive.erase 1023 := by
    change (1004 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0252

/-- finite transport leaf j=253, original=1005 -/
lemma transport_leaf_0253 : w 253 = (2147483503:M) := by
  let j : Fin 1024 := ⟨253, by omega⟩
  have horder : order j = (1005 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483503:M) := by
    rw [horder]
    exact point1_basis_1005
  have hw := w_from_basis j (2147483503:M) hb
  rw [horder] at hw
  have hnotmem : (1005 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (1005 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (1005 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (1005 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (1005 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (1005 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0253

/-- finite transport leaf j=254, original=1020 -/
lemma transport_leaf_0254 : w 254 = (2147483071:M) + 576 := by
  let j : Fin 1024 := ⟨254, by omega⟩
  have horder : order j = (1020 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483071:M) := by
    rw [horder]
    exact point1_basis_1020
  have hw := w_from_basis j (2147483071:M) hb
  rw [horder] at hw
  have hmem : (1020 : Fin 1024) ∈ inactive.erase 1023 := by
    change (1020 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0254

/-- finite transport leaf j=255, original=1021 -/
lemma transport_leaf_0255 : w 255 = (288:M) + 576 := by
  let j : Fin 1024 := ⟨255, by omega⟩
  have horder : order j = (1021 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (288:M) := by
    rw [horder]
    exact point1_basis_1021
  have hw := w_from_basis j (288:M) hb
  rw [horder] at hw
  have hmem : (1021 : Fin 1024) ∈ inactive.erase 1023 := by
    change (1021 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0255

/-- finite transport leaf j=352, original=778 -/
lemma transport_leaf_0352 : w 352 = (2147483551:M) + 576 := by
  let j : Fin 1024 := ⟨352, by omega⟩
  have horder : order j = (778 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (2147483551:M) := by
    rw [horder]
    exact point1_basis_778
  have hw := w_from_basis j (2147483551:M) hb
  rw [horder] at hw
  have hmem : (778 : Fin 1024) ∈ inactive.erase 1023 := by
    change (778 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0352

/-- finite transport leaf j=353, original=779 -/
lemma transport_leaf_0353 : w 353 = (48:M) := by
  let j : Fin 1024 := ⟨353, by omega⟩
  have horder : order j = (779 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (48:M) := by
    rw [horder]
    exact point1_basis_779
  have hw := w_from_basis j (48:M) hb
  rw [horder] at hw
  have hnotmem : (779 : Fin 1024) ∉ inactive.erase 1023 := by
    intro h
    change (779 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
    have hi : (779 : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2
    change (779 : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi
    have hb : T163SourceTable.isInactive (779 : Fin 1024) = true := (Finset.mem_filter.mp hi).2
    have hf : T163SourceTable.isInactive (779 : Fin 1024) = false := by decide
    rw [hf] at hb
    cases hb
  simp only [if_neg hnotmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0353

/-- finite transport leaf j=354, original=794 -/
lemma transport_leaf_0354 : w 354 = (192:M) + 576 := by
  let j : Fin 1024 := ⟨354, by omega⟩
  have horder : order j = (794 : Fin 1024) := by decide
  have hb : sourcePointBasis point (order j).val = (192:M) := by
    rw [horder]
    exact point1_basis_794
  have hw := w_from_basis j (192:M) hb
  rw [horder] at hw
  have hmem : (794 : Fin 1024) ∈ inactive.erase 1023 := by
    change (794 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
    rw [Finset.mem_erase]
    constructor
    · decide
    · rw [T163SourceTable.inactive, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by decide⟩
  simp only [if_pos hmem] at hw
  simpa [j] using hw
#print axioms transport_leaf_0354

end
end AspisR19.R759Point1TransportLeaves
