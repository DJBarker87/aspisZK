import NDO_JGd_Horner04
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Horner03
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open JGd_HornerData
def product : W := ((430536757,584744405),(988070522,807231034))
def r03 : W := ((694422152,1741168382),(1057628232,412117544))
theorem multiplied : value ((469664807,1877661931),(1679954569,1656891307)) * value ((1321832863,1686907802),(476564490,762595566)) = value product := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((469664807,1877661931),(1679954569,1656891307)) ((1321832863,1686907802),(476564490,762595566)) = ((430536757,584744405),(988070522,807231034))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms multiplied
theorem added : value product + value ((263885395,1156423977),(69557710,1752370157)) = value r03 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((430536757,584744405),(988070522,807231034)) ((263885395,1156423977),(69557710,1752370157)) = ((694422152,1741168382),(1057628232,412117544))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added
theorem step : run 4 (value ((1321832863,1686907802),(476564490,762595566))) = run 3 (value r03) := by
  unfold run
  rw [ExtractedMaskHornerPolynomial.hornerLoopModel]
  have hcell := JGd_Coefficients.value ⟨3,by omega⟩
  change coeff 3 = value (JGd_Coefficients.cell ⟨3,by omega⟩) at hcell
  rw [hcell]
  change ExtractedMaskHornerPolynomial.hornerLoopModel coeff (value JGd_Linear00.sum0) 3
    (value ((469664807,1877661931),(1679954569,1656891307)) * value ((1321832863,1686907802),(476564490,762595566)) + value ((263885395,1156423977),(69557710,1752370157))) = _
  rw [multiplied,added]
#print axioms step
end AspisR1.JGd_Horner03
end
