import NDO_JGd_Horner20
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Horner19
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open JGd_HornerData
def product : W := ((1251893604,351844474),(1535927236,1622092168))
def r19 : W := ((1291999144,1924738650),(517303417,926704075))
theorem multiplied : value ((469664807,1877661931),(1679954569,1656891307)) * value ((1390485170,2104717644),(1948736392,602693076)) = value product := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((469664807,1877661931),(1679954569,1656891307)) ((1390485170,2104717644),(1948736392,602693076)) = ((1251893604,351844474),(1535927236,1622092168))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms multiplied
theorem added : value product + value ((40105540,1572894176),(1128859828,1452095554)) = value r19 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((1251893604,351844474),(1535927236,1622092168)) ((40105540,1572894176),(1128859828,1452095554)) = ((1291999144,1924738650),(517303417,926704075))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added
theorem step : run 20 (value ((1390485170,2104717644),(1948736392,602693076))) = run 19 (value r19) := by
  unfold run
  rw [ExtractedMaskHornerPolynomial.hornerLoopModel]
  have hcell := JGd_Coefficients.value ⟨19,by omega⟩
  change coeff 19 = value (JGd_Coefficients.cell ⟨19,by omega⟩) at hcell
  rw [hcell]
  change ExtractedMaskHornerPolynomial.hornerLoopModel coeff (value JGd_Linear00.sum0) 19
    (value ((469664807,1877661931),(1679954569,1656891307)) * value ((1390485170,2104717644),(1948736392,602693076)) + value ((40105540,1572894176),(1128859828,1452095554))) = _
  rw [multiplied,added]
#print axioms step
end AspisR1.JGd_Horner19
end
