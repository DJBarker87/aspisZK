import FIp_MaskValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_MaskFormula
open Aeneas Aeneas.Std Result FIp_SemanticArithmetic
attribute [local irreducible] ExtractedMaskHornerPolynomial.coefficientPolynomial
  ExtractedMaskHornerCaller.coefficientValue ExtractedMaskCallerModel.populatedCoefficients
  ExtractedMaskLinearRecurrence.maskLinear ExtractedMaskLinearsExact.decodedPoint

theorem source (c1 : Array MQ 16#usize) (m : Array MQ 10#usize) (g : MQ) (p : Array MQ 10#usize) :
    ExtractedMaskHornerPolynomial.coefficientPolynomial
      (ExtractedMaskHornerCaller.coefficientValue
        (ExtractedMaskCallerModel.populatedCoefficients (mapArray c1) (mapArray m)))
      (ExtractedMaskLinearRecurrence.maskLinear 0 (ExtractedMaskLinearsExact.decodedPoint (mapArray p))) +
    (1+(ExtractedMaskLinearRecurrence.maskLinear 16 (ExtractedMaskLinearsExact.decodedPoint (mapArray p)))^26)*
      ExtractedMaskCallerModel.decode (toProbe g)=FIp_MaskValue.value c1 m g p := by
  unfold FIp_MaskValue.value
  rfl

#print axioms source
end AspisR1.JFu_MaskFormula
end
