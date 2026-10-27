import RPv_FJq_MaskC1Callback
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_ClaimZero
open Aeneas Aeneas.Std Result
/-- The source mask callback reads row zero of the original width29 claims. -/
theorem value (c : FJn_MaskC1Gather.Claims) (i : Fin 29) :
    FJq_MaskC1Callback.lookup c i.val=FJn_MainClaims.claims c 0 i := by
  unfold FJq_MaskC1Callback.lookup FJn_MainClaims.claims
  rw [List.getElem?_eq_getElem (by rw [c.property];decide)]
  exact FJq_MainCells.bounded (c.val[0]'(by rw [c.property];decide)) i
#print axioms value
end AspisR1.FJq_ClaimZero
end
