import RPv_FIz_ScalarFamily
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_ScalarList
open FIv_NativeValue (K)
open FIw_PublicModel (Public Openings Selectors)
theorem value (p : Public) (o : Openings) (s : Selectors) :
    List.ofFn (FIy_ScalarPacked.model p.dropDestination o s)=
      R0P.assetFamily.residuals (FIw_PublicModel.ofPublic p) (FIw_PublicModel.openings o) (FIw_PublicModel.selector s) := by
  rw [←FIz_ScalarFamily.value]
  -- PIN2: the native model reads the pre-PIN2 fields (probe-crate PIN2 emission via PIN2_ProbeSemanticPublicHelpers).
  unfold FIy_ScalarPacked.model FIw_ScalarSuffix.model
  pin2_drop
  cases p.variant <;> cases p.withdrawal_amount <;>
    simp [FIw_CoefficientMeaning.scalar,List.ofFn_succ]
#print axioms value
end AspisR1.FIz_ScalarList
end
