import FIp_SemanticValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_MaskNativeValue
open Aeneas Aeneas.Std Result
open FIp_SemanticArithmetic
open ExtractedMaskCallerModel

theorem source (c1 : Array MQ 16#usize) (m : Array MQ 10#usize) (g : MQ) (point : Array MQ 10#usize)
    (hc : ∀ j : Fin 16,CanonicalQM (ExtractedMaskCoefficientStep.c1Cell (mapArray c1) j))
    (hm : ∀ j : Fin 10,CanonicalQM (ExtractedMaskCoefficientStep.maskCell (mapArray m) j))
    (hp : ∀ i : Nat,∀ hi : i<10,CanonicalQM (ExtractedMaskLinearLoop.pointAtNat (mapArray point) i hi))
    (hg : CanonicalQM (toProbe g)) :
    ∃ native,FIp_SemanticArithmetic.mask c1 m g point=ok (fromProbe native) ∧
      CanonicalQM native ∧
      decode native =
        ExtractedMaskHornerPolynomial.coefficientPolynomial
          (ExtractedMaskHornerCaller.coefficientValue
            (populatedCoefficients (mapArray c1) (mapArray m)))
          (ExtractedMaskLinearRecurrence.maskLinear 0
            (ExtractedMaskLinearsExact.decodedPoint (mapArray point))) +
        (1+(ExtractedMaskLinearRecurrence.maskLinear 16
          (ExtractedMaskLinearsExact.decodedPoint (mapArray point)))^26)*decode (toProbe g) := by
  obtain ⟨native,hn,hcan,hval⟩ := selected_mask_value_populated_model
    (mapArray c1) (mapArray m) (toProbe g) (mapArray point) hc hm hp hg
  refine ⟨native,?_,hcan,hval⟩
  unfold FIp_SemanticArithmetic.mask
  rw [hn]
  rfl

#print axioms source
end AspisR1.FIp_MaskNativeValue
end
