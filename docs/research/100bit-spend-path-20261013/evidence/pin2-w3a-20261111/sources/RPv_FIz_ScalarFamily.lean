import RPv_FIy_ScalarPacked
import RPv_FIw_PublicModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_ScalarFamily
open FIv_NativeValue (K)
open FIw_PublicModel (Public Openings Selectors)
theorem value (p : Public) (o : Openings) (s : Selectors) :
    -- PIN2: the native model reads the pre-PIN2 fields (replace by Stream C's PIN2 emission).
    FIw_ScalarSuffix.model p.dropDestination o s=
    R0P.assetFamily.residuals (FIw_PublicModel.ofPublic p) (FIw_PublicModel.openings o) (FIw_PublicModel.selector s) := by
  unfold FIw_ScalarSuffix.model
  rw [FIw_CoefficientTransport.value]
  cases hv : p.variant <;> cases hw : p.withdrawal_amount <;>
    simp [PIN2Native.SemanticPublic.dropDestination,R0P.assetFamily,FIw_PublicModel.ofPublic,FIw_PublicModel.openings,
      FIw_PublicModel.selector,FIw_ScalarSuffix.selector,FIw_CoefficientTransport.variant,
      R0P.assetScalarLanes,hv,hw]
#print axioms value
end AspisR1.FIz_ScalarFamily
end
