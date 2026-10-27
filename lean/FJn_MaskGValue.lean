import FJn_MainArrayValue
import FJn_MaskC1Gather
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_MaskGValue
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open FIp_SemanticValues (Canon decode)
/-- Exact source G27, read from the SAME claims row used by both mask gathers. -/
theorem value (claims : FJn_MaskC1Gather.Claims) (row : Array aspis_core.field.QM31 29#usize)
    (g : aspis_core.field.QM31) (hc : FJn_MaskC1Gather.CanonClaims claims)
    (rr : Array.index_usize claims 0#usize=ok row) (rg : Array.index_usize row 27#usize=ok g) :
    Canon g ∧ decode g=FJn_MainArrayValue.value row 27 := by
  refine ⟨FJn_MainArrayValue.canonical row 27#usize g (hc row (FIr_ArrayRead.member claims 0#usize row rr)) rg,?_⟩
  exact (FJn_MainArrayValue.read row 27#usize g rg).symm
#print axioms value
end AspisR1.FJn_MaskGValue
end
