import NDO_JGd_NumericData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_MaskValue
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd

theorem source : JGd_MaskModel.value JFu_MaskInputs.c1 JFu_MaskInputs.maskOnly
    JFu_MaskInputs.point JFu_MaskInputs.g = FIp_SemanticValues.decode JGd_NumericData.mask := by
  unfold JGd_MaskModel.value
  rw [JGd_LinearValue.family0,JGd_LinearValue.family16,JGd_Power1.power26]
  change ExtractedMaskHornerPolynomial.coefficientPolynomial JGd_HornerData.coeff
    (value JGd_Linear00.sum0) + _ = _
  rw [JGd_HornerValue.source]
  change value ((730498243,234698042),(882910042,2122991591)) +
    (value ((1,0),(0,0)) + value ((60053924,1891194216),(2090430923,260852809))) *
      value ((839969315,1393507838),(1451026085,492151165)) = value JGd_NumericData.maskWords
  rw [JGd_NumericData.factor_value,JGd_NumericData.mask_product,JGd_NumericData.mask_sum]; rfl
#print axioms source
end AspisR1.JGd_MaskValue
end
