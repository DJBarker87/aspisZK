import NDO_JFu_MaskTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_MaskModel
open Aeneas Aeneas.Std Result FIp_SemanticArithmetic FIp_SemanticValues

/-- Keep the mask model at its source probe carrier; avoid unfolding its
coefficient population while transporting the result. -/
def value (c1 : Array MQ 16#usize) (m point : Array MQ 10#usize) (g : MQ) :=
  ExtractedMaskHornerPolynomial.coefficientPolynomial
    (ExtractedMaskHornerCaller.coefficientValue
      (ExtractedMaskCallerModel.populatedCoefficients (mapArray c1) (mapArray m)))
    (ExtractedMaskLinearRecurrence.maskLinear 0 (ExtractedMaskLinearsExact.decodedPoint (mapArray point))) +
  (1 + (ExtractedMaskLinearRecurrence.maskLinear 16
    (ExtractedMaskLinearsExact.decodedPoint (mapArray point))) ^ 26) *
      ExtractedMaskQM31Exact.decode (toProbe g)

attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
attribute [local irreducible] ExtractedMaskHornerPolynomial.coefficientPolynomial
  ExtractedMaskCallerModel.populatedCoefficients ExtractedMaskHornerCaller.coefficientValue
  ExtractedMaskLinearRecurrence.maskLinear ExtractedMaskLinearsExact.decodedPoint

theorem source (c1 : Array MQ 16#usize) (m point : Array MQ 10#usize) (g : MQ)
    (hc : ∀ j : Fin 16, ExtractedMaskCallerModel.CanonicalQM (ExtractedMaskCoefficientStep.c1Cell (mapArray c1) j))
    (hm : ∀ j : Fin 10, ExtractedMaskCallerModel.CanonicalQM (ExtractedMaskCoefficientStep.maskCell (mapArray m) j))
    (hp : ∀ i : Nat, ∀ hi : i < 10, ExtractedMaskCallerModel.CanonicalQM (ExtractedMaskLinearLoop.pointAtNat (mapArray point) i hi))
    (hg : Canon g) :
    ∃ out, FIp_SemanticArithmetic.mask c1 m g point = ok out ∧ Canon out ∧
      decode out = value c1 m point g := by
  obtain ⟨out,call,hcan,hval⟩ := ExtractedMaskCallerModel.selected_mask_value_populated_model
    (mapArray c1) (mapArray m) (toProbe g) (mapArray point) hc hm hp hg
  refine ⟨fromProbe out, ?_, ?_, ?_⟩
  · unfold FIp_SemanticArithmetic.mask
    rw [call]
    rfl
  · exact hcan
  · dsimp only [value, FIp_SemanticValues.decode, to_from,
      ExtractedMaskCallerModel.decode, ExtractedMaskHornerPolynomial.ExactQM,
      ExtractedMaskQM31Exact.QM31Exact] at hval ⊢
    exact hval
#print axioms source
end AspisR1.JGd_MaskModel
end
