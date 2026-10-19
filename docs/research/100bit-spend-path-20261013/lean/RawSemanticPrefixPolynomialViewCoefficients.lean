import R1SemanticPayloadView
import RawSemanticPrefixPolynomialRows

set_option autoImplicit false
namespace AspisR1PublicPreparation.RawSemanticPrefixPolynomialViewCoefficients

open AspisR1.SemanticRecordCodec

/-- The lightweight codec projection and the existing semantic-view
coefficient projection select the same vector from each fixed typed row. -/
theorem coefficientsAt_eq_coeffAt (values : AspisR1.SemanticPrefixCodec.Full)
    (j : Fin 10) :
    AspisR1PublicPreparation.RawSemanticPrefixPolynomialRows.coefficientsAt values j =
      AspisR1.SemanticPayloadView.coeffAt values j := by
  have hcodec :=
    AspisR1PublicPreparation.RawSemanticPrefixPolynomialRows.coefficientsAt_payload
      values j
  have hview := AspisR1.SemanticPayloadView.coeffAt_payload values j
  have hconstructors :
      Payload.polynomial
          (AspisR1PublicPreparation.RawSemanticPrefixPolynomialRows.coefficientsAt values j) =
        Payload.polynomial (AspisR1.SemanticPayloadView.coeffAt values j) :=
    hcodec.symm.trans hview
  injection hconstructors with hcoefficients

#print axioms coefficientsAt_eq_coeffAt
end AspisR1PublicPreparation.RawSemanticPrefixPolynomialViewCoefficients
