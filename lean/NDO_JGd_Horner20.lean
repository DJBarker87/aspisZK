import NDO_JGd_Horner21
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Horner20
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open JGd_HornerData
def product : W := ((147329744,1790799309),(599054994,389192631))
def r20 : W := ((1390485170,2104717644),(1948736392,602693076))
theorem multiplied : value ((469664807,1877661931),(1679954569,1656891307)) * value ((229264195,615091949),(1697162726,1562689920)) = value product := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((469664807,1877661931),(1679954569,1656891307)) ((229264195,615091949),(1697162726,1562689920)) = ((147329744,1790799309),(599054994,389192631))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms multiplied
theorem added : value product + value ((1243155426,313918335),(1349681398,213500445)) = value r20 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((147329744,1790799309),(599054994,389192631)) ((1243155426,313918335),(1349681398,213500445)) = ((1390485170,2104717644),(1948736392,602693076))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added
theorem step : run 21 (value ((229264195,615091949),(1697162726,1562689920))) = run 20 (value r20) := by
  unfold run
  rw [ExtractedMaskHornerPolynomial.hornerLoopModel]
  have hcell := JGd_Coefficients.value ⟨20,by omega⟩
  change coeff 20 = value (JGd_Coefficients.cell ⟨20,by omega⟩) at hcell
  rw [hcell]
  change ExtractedMaskHornerPolynomial.hornerLoopModel coeff (value JGd_Linear00.sum0) 20
    (value ((469664807,1877661931),(1679954569,1656891307)) * value ((229264195,615091949),(1697162726,1562689920)) + value ((1243155426,313918335),(1349681398,213500445))) = _
  rw [multiplied,added]
#print axioms step
end AspisR1.JGd_Horner20
end
