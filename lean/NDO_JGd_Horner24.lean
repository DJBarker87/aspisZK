import NDO_JGd_Horner25
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Horner24
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open JGd_HornerData
def product : W := ((649682756,2011543439),(1620026584,2005086245))
def r24 : W := ((2039247633,354852142),(2118034010,387772028))
theorem multiplied : value ((469664807,1877661931),(1679954569,1656891307)) * value ((1821250639,39259025),(1008944285,1897497192)) = value product := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((469664807,1877661931),(1679954569,1656891307)) ((1821250639,39259025),(1008944285,1897497192)) = ((649682756,2011543439),(1620026584,2005086245))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms multiplied
theorem added : value product + value ((1389564877,490792350),(498007426,530169430)) = value r24 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((649682756,2011543439),(1620026584,2005086245)) ((1389564877,490792350),(498007426,530169430)) = ((2039247633,354852142),(2118034010,387772028))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added
theorem step : run 25 (value ((1821250639,39259025),(1008944285,1897497192))) = run 24 (value r24) := by
  unfold run
  rw [ExtractedMaskHornerPolynomial.hornerLoopModel]
  have hcell := JGd_Coefficients.value ⟨24,by omega⟩
  change coeff 24 = value (JGd_Coefficients.cell ⟨24,by omega⟩) at hcell
  rw [hcell]
  change ExtractedMaskHornerPolynomial.hornerLoopModel coeff (value JGd_Linear00.sum0) 24
    (value ((469664807,1877661931),(1679954569,1656891307)) * value ((1821250639,39259025),(1008944285,1897497192)) + value ((1389564877,490792350),(498007426,530169430))) = _
  rw [multiplied,added]
#print axioms step
end AspisR1.JGd_Horner24
end
