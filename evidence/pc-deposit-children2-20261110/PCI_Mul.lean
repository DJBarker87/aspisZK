import RPu_JFv_RawExtractedSemanticCallOpsV20
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_Mul
/-- Existing CLOSED shared-field emitted definition at the same two raw words.
    This pairs the natural-spec multiplication stub; no multiplication is proved in Kani. -/
theorem value (x y : U32) :
    ∃ z, AspisR1SemanticCallExtraction.aspis_core.field.M31.mul x y = ok z ∧
      z.val = (x.val*y.val)%2147483647 ∧ z.val<2147483647 := by
  rw [AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.generated_m31_mul_eq_probe]
  exact AspisR1.ExtractedMaskReducer.current_mul_mod x y
#print axioms value
end PCI_Mul
