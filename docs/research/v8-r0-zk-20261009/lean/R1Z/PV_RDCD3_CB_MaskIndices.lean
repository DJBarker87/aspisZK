import R1Z.PV_RDCD3_CB_MaskLeaves
import R1Z.PV_RDCD3_ArrayIndex
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD3_CB_MaskIndices
open Aeneas Aeneas.Std Result
namespace S
abbrev factors := PV_RDCD3_CB_MaskSource.state_only_hiding.FACTOR_EXPONENTS
abbrev maskFactors := PV_RDCD3_CB_MaskSource.state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS
end S
theorem coordinate (column : Usize) : (column &&& 3#usize).val < 4 := by
  rw [UScalar.val_and]
  have h : column.val &&& 3 ≤ 3 := Nat.and_le_right
  exact Nat.lt_succ_of_le h
theorem factors_bound (x : U8) (h : x ∈ S.factors.val) : x.val < 27 := by
  simp only [S.factors,PV_RDCD3_CB_MaskSource.state_only_hiding.FACTOR_EXPONENTS,
    Array.make,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
theorem mask_factors_bound (x : U8) (h : x ∈ S.maskFactors.val) : x.val < 27 := by
  simp only [S.maskFactors,PV_RDCD3_CB_MaskSource.state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS,
    Array.make,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
theorem factors_read (index : Usize) (bound : index.val < 16) :
    ∃ x, Array.index_usize S.factors index = .ok x ∧ x.val < 27 := by
  have hi : index.val < S.factors.val.length := by rw [S.factors.property];exact bound
  refine ⟨S.factors.val[index.val],PV_RDCD3_ArrayIndex.array_index_usize_ok _ _ bound,?_⟩
  apply factors_bound
  exact List.get_mem _ ⟨index.val,hi⟩
theorem mask_factors_read (index : Usize) (bound : index.val < 10) :
    ∃ x, Array.index_usize S.maskFactors index = .ok x ∧ x.val < 27 := by
  have hi : index.val < S.maskFactors.val.length := by rw [S.maskFactors.property];exact bound
  refine ⟨S.maskFactors.val[index.val],PV_RDCD3_ArrayIndex.array_index_usize_ok _ _ bound,?_⟩
  apply mask_factors_bound
  exact List.get_mem _ ⟨index.val,hi⟩
#print axioms coordinate
#print axioms factors_bound
#print axioms mask_factors_bound
#print axioms factors_read
#print axioms mask_factors_read
end R1Z.PV_RDCD3_CB_MaskIndices
