import FIw_PublicModel
import FIw_ScalarSuffix
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIw_AssetModel
open FIw_PublicModel

theorem value (pub : Public) (o : Openings) (s : Selectors) :
    FIw_ScalarSuffix.model pub o s=R0P.assetFamily.residuals
      (ofPublic pub) (openings o) (selector s) := by
  cases hv : pub.variant <;> cases ha : pub.withdrawal_amount <;>
    simp only [FIw_ScalarSuffix.model,FIw_ScalarSuffix.selector,ofPublic,openings,selector,
      R0P.assetFamily,R0P.assetScalarLanes,FIw_CoefficientMeaning.scalar,
      FIw_CoefficientTransport.variant,hv,ha,Option.isSome_none,Option.isSome_some,
      Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
      Bool.false_eq_true,↓reduceIte,add_zero]
  all_goals rfl
#print axioms value
end AspisR1.FIw_AssetModel
end
