import NDO_JGd_Horner03
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Horner02
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open JGd_HornerData
def product : W := ((1880091812,40065919),(570449217,1910667658))
def r02 : W := ((350980296,162225165),(827189199,1562618718))
theorem multiplied : value ((469664807,1877661931),(1679954569,1656891307)) * value ((694422152,1741168382),(1057628232,412117544)) = value product := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((469664807,1877661931),(1679954569,1656891307)) ((694422152,1741168382),(1057628232,412117544)) = ((1880091812,40065919),(570449217,1910667658))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms multiplied
theorem added : value product + value ((618372131,122159246),(256739982,1799434707)) = value r02 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((1880091812,40065919),(570449217,1910667658)) ((618372131,122159246),(256739982,1799434707)) = ((350980296,162225165),(827189199,1562618718))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added
theorem step : run 3 (value ((694422152,1741168382),(1057628232,412117544))) = run 2 (value r02) := by
  unfold run
  rw [ExtractedMaskHornerPolynomial.hornerLoopModel]
  have hcell := JGd_Coefficients.value ⟨2,by omega⟩
  change coeff 2 = value (JGd_Coefficients.cell ⟨2,by omega⟩) at hcell
  rw [hcell]
  change ExtractedMaskHornerPolynomial.hornerLoopModel coeff (value JGd_Linear00.sum0) 2
    (value ((469664807,1877661931),(1679954569,1656891307)) * value ((694422152,1741168382),(1057628232,412117544)) + value ((618372131,122159246),(256739982,1799434707))) = _
  rw [multiplied,added]
#print axioms step
end AspisR1.JGd_Horner02
end
