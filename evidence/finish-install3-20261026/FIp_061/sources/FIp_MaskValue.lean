import FIp_SemanticValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_MaskValue
open Aeneas Aeneas.Std Result
open FIp_SemanticArithmetic FIp_SemanticValues
open ExtractedMaskCallerModel

def value (c1 : Array MQ 16#usize) (m : Array MQ 10#usize) (g : MQ) (point : Array MQ 10#usize) :=
  ExtractedMaskHornerPolynomial.coefficientPolynomial
    (ExtractedMaskHornerCaller.coefficientValue (populatedCoefficients (mapArray c1) (mapArray m)))
    (ExtractedMaskLinearRecurrence.maskLinear 0 (ExtractedMaskLinearsExact.decodedPoint (mapArray point))) +
  (1+(ExtractedMaskLinearRecurrence.maskLinear 16 (ExtractedMaskLinearsExact.decodedPoint (mapArray point)))^26)*
    FIp_SemanticValues.decode g

theorem source (c1 : Array MQ 16#usize) (m : Array MQ 10#usize) (g : MQ) (point : Array MQ 10#usize)
    (hc : ∀ j : Fin 16,CanonicalQM (ExtractedMaskCoefficientStep.c1Cell (mapArray c1) j))
    (hm : ∀ j : Fin 10,CanonicalQM (ExtractedMaskCoefficientStep.maskCell (mapArray m) j))
    (hp : ∀ i : Nat,∀ hi : i<10,CanonicalQM (ExtractedMaskLinearLoop.pointAtNat (mapArray point) i hi))
    (hg : Canon g) :
    ∃ out,FIp_SemanticArithmetic.mask c1 m g point=ok out ∧ Canon out ∧
      FIp_SemanticValues.decode out=value c1 m g point := by
  obtain ⟨native,hn,hcan,hval⟩ := selected_mask_value_populated_model
    (mapArray c1) (mapArray m) (toProbe g) (mapArray point) hc hm hp hg
  refine ⟨fromProbe native,?_,?_,?_⟩
  · unfold FIp_SemanticArithmetic.mask
    rw [hn]
    rfl
  · simpa only [Canon,to_from] using hcan
  · simpa only [FIp_SemanticValues.decode,to_from,value] using hval

#print axioms source
end AspisR1.FIp_MaskValue
end
