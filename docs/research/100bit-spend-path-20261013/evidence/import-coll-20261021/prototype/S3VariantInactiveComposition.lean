import S3VariantRowCurrentSourceBridge
import S3InactiveModelBridge

set_option autoImplicit false
namespace AspisR1.S3VariantInactiveComposition

open Aeneas Aeneas.Std Result WP

/-- Usize input corresponding to the actual S2 caller expression `16*j+s`.
The caller is still explicit: this theorem does not show that the optimized
weights loop invokes this function with these arguments. -/
def s2RowInput (j : Fin 64) (s : Fin 16) : Std.Usize :=
  UScalar.ofNatCore (16 * j.val + s.val) (by scalar_tac)

theorem s2RowInput_val (j : Fin 64) (s : Fin 16) :
    (s2RowInput j s).val = 16 * j.val + s.val := by
  simp [s2RowInput, UScalar.ofNatCore_val_eq]

/-- The actual extracted S2 Variant.row result, fed to the retained actual
inactive helper, is classified by the grouped S3 model.  No row-equality
premise is supplied: it follows from the actual row result theorem. -/
theorem s2_variant_row_inactive_grouped (j : Fin 64) (s : Fin 16) :
    ∃ out,
      AspisR1.S3VariantRowAeneasCut.s2_row_result (s2RowInput j s) = .ok out ∧
      out.val = AspisR1.S3S9CurrentSourceModel.s2Row (16 * j.val + s.val) ∧
      AspisR1S3InactiveSource.r0.opening.inactive out =
        .ok (core.result.Result.Ok
          (AspisR1.S3S9CurrentSourceModel.inactiveAtGroup
            (AspisR1.S3S9CurrentSourceModel.groupAt j) s)) := by
  obtain ⟨out, hrun, hvalue⟩ :=
    AspisR1.S3VariantRowAeneasCut.s2_row_result_value_current (s2RowInput j s)
  have hrow : out.val =
      AspisR1.S3S9CurrentSourceModel.s2Row (16 * j.val + s.val) := by
    rw [hvalue, s2RowInput_val]
  refine ⟨out, hrun, hrow, ?_⟩
  exact AspisR1.S3InactiveModelBridge.actual_inactive_eq_grouped_model out j s hrow

#print axioms s2RowInput_val
#print axioms s2_variant_row_inactive_grouped
end AspisR1.S3VariantInactiveComposition
