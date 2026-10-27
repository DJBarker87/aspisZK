import FIp_MaskValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_MaskFormula
open Aeneas Aeneas.Std
open FIp_SemanticArithmetic (MQ mapArray toProbe)
attribute [local irreducible] ExtractedMaskCallerModel.populatedCoefficients
  ExtractedMaskHornerPolynomial.coefficientPolynomial ExtractedMaskHornerCaller.coefficientValue
  ExtractedMaskLinearRecurrence.maskLinear
/-- Definition transport only; every coefficient and recurrence remains opaque. -/
theorem value (c1 : Array MQ 16#usize) (m : Array MQ 10#usize) (g : MQ) (point : Array MQ 10#usize) :
    FIp_MaskValue.value c1 m g point=
      ExtractedMaskHornerPolynomial.coefficientPolynomial
        (ExtractedMaskHornerCaller.coefficientValue
          (ExtractedMaskCallerModel.populatedCoefficients (mapArray c1) (mapArray m)))
        (ExtractedMaskLinearRecurrence.maskLinear 0 (ExtractedMaskLinearsExact.decodedPoint (mapArray point)))+
      (1+(ExtractedMaskLinearRecurrence.maskLinear 16
        (ExtractedMaskLinearsExact.decodedPoint (mapArray point)))^26)*ExtractedMaskQM31Exact.decode (toProbe g) := by
  unfold FIp_MaskValue.value FIp_SemanticValues.decode
  rfl
#print axioms value
end AspisR1.FJn_MaskFormula
end
