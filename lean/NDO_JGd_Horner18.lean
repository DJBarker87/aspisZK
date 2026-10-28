import NDO_JGd_Horner19
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Horner18
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open JGd_HornerData
def product : W := ((1093466263,431457517),(83038682,2077461731))
def r18 : W := ((1223403448,67439174),(1961456849,1815156440))
theorem multiplied : value ((469664807,1877661931),(1679954569,1656891307)) * value ((1291999144,1924738650),(517303417,926704075)) = value product := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((469664807,1877661931),(1679954569,1656891307)) ((1291999144,1924738650),(517303417,926704075)) = ((1093466263,431457517),(83038682,2077461731))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms multiplied
theorem added : value product + value ((129937185,1783465304),(1878418167,1885178356)) = value r18 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((1093466263,431457517),(83038682,2077461731)) ((129937185,1783465304),(1878418167,1885178356)) = ((1223403448,67439174),(1961456849,1815156440))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added
theorem step : run 19 (value ((1291999144,1924738650),(517303417,926704075))) = run 18 (value r18) := by
  unfold run
  rw [ExtractedMaskHornerPolynomial.hornerLoopModel]
  have hcell := JGd_Coefficients.value ⟨18,by omega⟩
  change coeff 18 = value (JGd_Coefficients.cell ⟨18,by omega⟩) at hcell
  rw [hcell]
  change ExtractedMaskHornerPolynomial.hornerLoopModel coeff (value JGd_Linear00.sum0) 18
    (value ((469664807,1877661931),(1679954569,1656891307)) * value ((1291999144,1924738650),(517303417,926704075)) + value ((129937185,1783465304),(1878418167,1885178356))) = _
  rw [multiplied,added]
#print axioms step
end AspisR1.JGd_Horner18
end
