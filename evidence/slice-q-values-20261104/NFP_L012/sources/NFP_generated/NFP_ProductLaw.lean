import JFv_RawExtractedSemanticCallOpsV20
import JFv_TX2_NodeCall
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFP_ProductLaw
open Aeneas Aeneas.Std Result
/-- The emitted definition returns exactly the natural product residue.
No multiplication is checked natively; the caller logs the SAME operands. -/
theorem generated (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
 ∃ out, AspisR1SemanticCallExtraction.aspis_core.field.M31.mul x y = ok out ∧
 out.val=(x.val*y.val)%2147483647 ∧ out.val<2147483647 := by
 obtain ⟨out,run,value,canonical⟩ := ExtractedCurrentReducer.current_mul_mod x y
 refine ⟨out,?_,value,canonical⟩
 rw [AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.generated_m31_mul_eq_probe]
 exact run

/-- Exact SAME-z square/double/sub node spec already proved on the probe. -/
theorem node (z : U32) : ∃ out, JFv_TX2_NodeCall.sourceCall z=ok out ∧
 out.val<2147483647 ∧
 out.val=(((z.val*z.val)%2147483647+(z.val*z.val)%2147483647)%2147483647+2147483647-1)%2147483647 :=
 JFv_TX2_NodeCall.source z
#print axioms generated
#print axioms node
end AspisR1.NFP_ProductLaw
end
