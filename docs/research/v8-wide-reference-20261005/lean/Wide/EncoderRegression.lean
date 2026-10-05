import Wide.GRSConversion
import AspisFormal.Pool.V7C1ConcreteProjectionBinding
import AspisFormal.K1.V7Tag73ExactOneFoldEncoderBinding

/-! Equality-only regression against frozen V7. The V7 context is confined to
this regression module; the generic encoder modules do not import it. -/
set_option autoImplicit false
namespace AspisWide.EncoderRegression
open AspisV5ComponentCQM31TowerExact

theorem initialEncoder_eq_v7 :
    AspisWide.InitialEncoder.exactInitialEncoder (K := QM31Exact) =
      AspisPool.V7C1ConcreteProjectionBinding.exactInitialEncoder := rfl

theorem finalEncoder_eq_v7 :
    AspisWide.FinalEncoder.exactFinalEncoder (K := QM31Exact) =
      AspisK1.V7Tag73ExactOneFoldEncoderBinding.exactFinalEncoder := rfl

#print axioms initialEncoder_eq_v7
#print axioms finalEncoder_eq_v7
end AspisWide.EncoderRegression
