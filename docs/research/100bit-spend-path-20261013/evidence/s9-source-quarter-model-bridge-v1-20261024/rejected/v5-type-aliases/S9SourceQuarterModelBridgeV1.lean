import S9SourceQuarterInverseV1
import S9WideFieldOperatorBridgesV1
import RoundPairing
set_option autoImplicit false
namespace AspisR1S9SourceQuarterModelBridgeV1
open AspisR1S9WideFieldOperatorBridgesV1
abbrev E := AspisWideTower.WideExact
/-- This projection identity is proved with an abstract Field, before any
concrete tower value is substituted. -/
theorem generic_quarter {K : Type} [Field K] :
    fieldInv (fieldFour : K)=AspisR1.RoundPairing.quarter := by rfl
/-- Source inverse/four operator paths are converted individually. No concrete
inverse or complete field polynomial is normalized. -/
theorem source_quarter_eq_model_quarter :
    AspisR1S9ScalarActualPowerPolynomialV1.quarter=
      (AspisR1.RoundPairing.quarter : E) := by
  have hs := AspisR1S9SourceQuarterInverseV1.source_quarter_eq_inverse_four
  have hi := inv_operator_eq (4 : E)
  have hf := congrArg (fun x : E => fieldInv x) four_operator_eq
  have hg := generic_quarter (K:=E)
  dsimp only [AspisR1S9ScalarActualPowerPolynomialV1.E,
    AspisR1S9SourceQuarterInverseV1.E,AspisR1S9WideFieldOperatorBridgesV1.E,E] at hs hi hf hg ⊢
  exact hs.trans (hi.trans (hf.trans hg))
#print axioms generic_quarter
#print axioms source_quarter_eq_model_quarter
end AspisR1S9SourceQuarterModelBridgeV1
