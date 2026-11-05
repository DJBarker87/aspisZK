import NHU_Tower
import NHU_Power
import NHU_Linears
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NHU_Mask
open AspisR1.ExtractedMaskCallerModel
abbrev QM := AspisR1SelectedMaskProbe.field.QM31

/-- Complete SAME-input canonical packet for the retained emitted root.
All loop invariants and intermediate domains are established by the imported
coefficient/Horner/linear inductions and child laws. Native source cuts are
separately required; this theorem is never their substitute. -/
theorem result (c1 : C1) (maskOnly : MaskOnly) (g : QM) (point : Array QM 10#usize)
 (hc1 : ∀ j : Fin 16,CanonicalQM (AspisR1.ExtractedMaskCoefficientStep.c1Cell c1 j))
 (hmask : ∀ j : Fin 10,CanonicalQM (AspisR1.ExtractedMaskCoefficientStep.maskCell maskOnly j))
 (hpoint : ∀ i (hi : i<10),CanonicalQM (AspisR1.ExtractedMaskLinearLoop.pointAtNat point i hi))
 (hg : CanonicalQM g) :
 ∃ out,AspisR1SelectedMaskProbe.state_only_hiding.state_only_selected_mask_value c1 maskOnly g point=ok out ∧
 CanonicalQM out ∧ decode out=
 AspisR1.ExtractedMaskHornerPolynomial.coefficientPolynomial
  (AspisR1.ExtractedMaskHornerCaller.coefficientValue (populatedCoefficients c1 maskOnly))
  (AspisR1.ExtractedMaskLinearRecurrence.maskLinear 0
   (AspisR1.ExtractedMaskLinearsExact.decodedPoint point))+
 (1+(AspisR1.ExtractedMaskLinearRecurrence.maskLinear 16
   (AspisR1.ExtractedMaskLinearsExact.decodedPoint point))^26)*decode g :=
 selected_mask_value_populated_model c1 maskOnly g point hc1 hmask hpoint hg

/-- Nominal carrier transport to the actual adopted finish dictionary. This
is equality of the complete Result, not just an accepted value or component. -/
theorem adopted (seed : AspisR1PublicPreparation.FinishModel.Boundaries)
 (c1 : Array FIp_SemanticArithmetic.MQ 16#usize)
 (maskOnly : Array FIp_SemanticArithmetic.MQ 10#usize)
 (g : FIp_SemanticArithmetic.MQ) (point : Array FIp_SemanticArithmetic.MQ 10#usize) :
 (FIp_SemanticArithmetic.install seed).mask c1 maskOnly g point=
 FIp_SemanticArithmetic.mapResult
  (AspisR1SelectedMaskProbe.state_only_hiding.state_only_selected_mask_value
   (FIp_SemanticArithmetic.mapArray c1) (FIp_SemanticArithmetic.mapArray maskOnly)
   (FIp_SemanticArithmetic.toProbe g) (FIp_SemanticArithmetic.mapArray point)) := rfl

#print axioms result
#print axioms adopted
end AspisR1.NHU_Mask
