import NDO_JGd_Horner07
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Horner06
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open JGd_HornerData
def product : W := ((529799570,335424460),(1203707340,1308516828))
def r06 : W := ((1964697577,1204117337),(1405943572,753417738))
theorem multiplied : value ((469664807,1877661931),(1679954569,1656891307)) * value ((221460663,1238584373),(1122423444,18036448)) = value product := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((469664807,1877661931),(1679954569,1656891307)) ((221460663,1238584373),(1122423444,18036448)) = ((529799570,335424460),(1203707340,1308516828))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms multiplied
theorem added : value product + value ((1434898007,868692877),(202236232,1592384557)) = value r06 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((529799570,335424460),(1203707340,1308516828)) ((1434898007,868692877),(202236232,1592384557)) = ((1964697577,1204117337),(1405943572,753417738))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added
theorem step : run 7 (value ((221460663,1238584373),(1122423444,18036448))) = run 6 (value r06) := by
  unfold run
  rw [ExtractedMaskHornerPolynomial.hornerLoopModel]
  have hcell := JGd_Coefficients.value ⟨6,by omega⟩
  change coeff 6 = value (JGd_Coefficients.cell ⟨6,by omega⟩) at hcell
  rw [hcell]
  change ExtractedMaskHornerPolynomial.hornerLoopModel coeff (value JGd_Linear00.sum0) 6
    (value ((469664807,1877661931),(1679954569,1656891307)) * value ((221460663,1238584373),(1122423444,18036448)) + value ((1434898007,868692877),(202236232,1592384557))) = _
  rw [multiplied,added]
#print axioms step
end AspisR1.JGd_Horner06
end
