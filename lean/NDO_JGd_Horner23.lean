import NDO_JGd_Horner24
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Horner23
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open JGd_HornerData
def product : W := ((1761097444,422340254),(729975717,1509473805))
def r23 : W := ((1761097444,422340254),(729975717,1509473805))
theorem multiplied : value ((469664807,1877661931),(1679954569,1656891307)) * value ((2039247633,354852142),(2118034010,387772028)) = value product := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((469664807,1877661931),(1679954569,1656891307)) ((2039247633,354852142),(2118034010,387772028)) = ((1761097444,422340254),(729975717,1509473805))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms multiplied
theorem added : value product + value ((0,0),(0,0)) = value r23 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((1761097444,422340254),(729975717,1509473805)) ((0,0),(0,0)) = ((1761097444,422340254),(729975717,1509473805))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added
theorem step : run 24 (value ((2039247633,354852142),(2118034010,387772028))) = run 23 (value r23) := by
  unfold run
  rw [ExtractedMaskHornerPolynomial.hornerLoopModel]
  have hcell := JGd_Coefficients.value ⟨23,by omega⟩
  change coeff 23 = value (JGd_Coefficients.cell ⟨23,by omega⟩) at hcell
  rw [hcell]
  change ExtractedMaskHornerPolynomial.hornerLoopModel coeff (value JGd_Linear00.sum0) 23
    (value ((469664807,1877661931),(1679954569,1656891307)) * value ((2039247633,354852142),(2118034010,387772028)) + value ((0,0),(0,0))) = _
  rw [multiplied,added]
#print axioms step
end AspisR1.JGd_Horner23
end
