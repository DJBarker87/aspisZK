import NDO_JGd_Horner08
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Horner07
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open JGd_HornerData
def product : W := ((628283822,297473315),(1890593181,2009099986))
def r07 : W := ((221460663,1238584373),(1122423444,18036448))
theorem multiplied : value ((469664807,1877661931),(1679954569,1656891307)) * value ((2043513133,2025476135),(1808241230,593119279)) = value product := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((469664807,1877661931),(1679954569,1656891307)) ((2043513133,2025476135),(1808241230,593119279)) = ((628283822,297473315),(1890593181,2009099986))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms multiplied
theorem added : value product + value ((1740660488,941111058),(1379313910,156420109)) = value r07 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((628283822,297473315),(1890593181,2009099986)) ((1740660488,941111058),(1379313910,156420109)) = ((221460663,1238584373),(1122423444,18036448))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added
theorem step : run 8 (value ((2043513133,2025476135),(1808241230,593119279))) = run 7 (value r07) := by
  unfold run
  rw [ExtractedMaskHornerPolynomial.hornerLoopModel]
  have hcell := JGd_Coefficients.value ⟨7,by omega⟩
  change coeff 7 = value (JGd_Coefficients.cell ⟨7,by omega⟩) at hcell
  rw [hcell]
  change ExtractedMaskHornerPolynomial.hornerLoopModel coeff (value JGd_Linear00.sum0) 7
    (value ((469664807,1877661931),(1679954569,1656891307)) * value ((2043513133,2025476135),(1808241230,593119279)) + value ((1740660488,941111058),(1379313910,156420109))) = _
  rw [multiplied,added]
#print axioms step
end AspisR1.JGd_Horner07
end
