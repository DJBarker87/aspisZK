import R22TotalCheckedComposition
import S3VariantInactiveComposition

set_option autoImplicit false
namespace AspisR1.R22TotalRowCones
open Aeneas Aeneas.Std Result R22TotalCheckedComposition

theorem row_R22 (t : Translation S3VariantRowAeneasCut.s2_row_result) :
    ∀ j, NoOverflow (t.code j) ∧ wrapping (t.code j) = S3VariantRowAeneasCut.s2_row_result j := by
  apply extracted_total_R22
  intro j
  obtain ⟨out, hrun, _⟩ := S3VariantRowAeneasCut.s2_row_result_value_current j
  exact ⟨out, hrun⟩

def rowInactive (input : Fin 64 × Fin 16) := do
  let out ← S3VariantRowAeneasCut.s2_row_result
    (S3VariantInactiveComposition.s2RowInput input.1 input.2)
  AspisR1S3InactiveSource.r0.opening.inactive out

theorem row_inactive_R22 (t : Translation rowInactive) :
    ∀ input, NoOverflow (t.code input) ∧ wrapping (t.code input) = rowInactive input := by
  apply extracted_total_R22
  intro input
  obtain ⟨out, hrun, _, hinactive⟩ :=
    S3VariantInactiveComposition.s2_variant_row_inactive_grouped input.1 input.2
  refine ⟨core.result.Result.Ok (S3S9CurrentSourceModel.inactiveAtGroup
    (S3S9CurrentSourceModel.groupAt input.1) input.2), ?_⟩
  simp only [rowInactive, hrun, bind_tc_ok, hinactive]

/-- Exact original grouped classification survives the checked/wrapping join. -/
theorem wrapping_row_model (t : Translation S3VariantRowAeneasCut.s2_row_result) (j : Usize) :
    ∃ out, NoOverflow (t.code j) ∧ wrapping (t.code j) = ok out ∧
      out.val = S3S9CurrentSourceModel.s2Row j.val := by
  obtain ⟨out, hrun, hv⟩ := S3VariantRowAeneasCut.s2_row_result_value_current j
  obtain ⟨hs, hw⟩ := row_R22 t j
  exact ⟨out, hs, hw.trans hrun, hv⟩

#print axioms row_R22
#print axioms row_inactive_R22
#print axioms wrapping_row_model
end AspisR1.R22TotalRowCones
