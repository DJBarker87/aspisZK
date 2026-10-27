import RPu_FIy_ScalarPacked
import RPu_FIw_PublicModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_ScalarFamily
open FIv_NativeValue (K)
open FIw_PublicModel (Public Openings Selectors)
theorem value (p : Public) (o : Openings) (s : Selectors) :
    FIw_ScalarSuffix.model p o s=
    R0P.assetFamily.residuals (FIw_PublicModel.ofPublic p) (FIw_PublicModel.openings o) (FIw_PublicModel.selector s) := by
  unfold FIw_ScalarSuffix.model
  rw [FIw_CoefficientTransport.value]
  cases hv : p.variant <;> cases hw : p.withdrawal_amount <;>
    simp [R0P.assetFamily,FIw_PublicModel.ofPublic,FIw_PublicModel.openings,
      FIw_PublicModel.selector,FIw_ScalarSuffix.selector,FIw_CoefficientTransport.variant,
      R0P.assetScalarLanes,hv,hw]
#print axioms value
end AspisR1.FIz_ScalarFamily
end
