import NDO_JGd_HornerData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Horner25
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open JGd_HornerData
def product : W := ((885697728,917836319),(552031280,2116010825))
def r25 : W := ((1821250639,39259025),(1008944285,1897497192))
theorem multiplied : value ((469664807,1877661931),(1679954569,1656891307)) * value ((1794094306,970136214),(692219080,662936248)) = value product := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((469664807,1877661931),(1679954569,1656891307)) ((1794094306,970136214),(692219080,662936248)) = ((885697728,917836319),(552031280,2116010825))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms multiplied
theorem added : value product + value ((935552911,1268906353),(456913005,1928970014)) = value r25 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((885697728,917836319),(552031280,2116010825)) ((935552911,1268906353),(456913005,1928970014)) = ((1821250639,39259025),(1008944285,1897497192))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added
theorem step : run 26 (value ((1794094306,970136214),(692219080,662936248))) = run 25 (value r25) := by
  unfold run
  rw [ExtractedMaskHornerPolynomial.hornerLoopModel]
  have hcell := JGd_Coefficients.value ⟨25,by omega⟩
  change coeff 25 = value (JGd_Coefficients.cell ⟨25,by omega⟩) at hcell
  rw [hcell]
  change ExtractedMaskHornerPolynomial.hornerLoopModel coeff (value JGd_Linear00.sum0) 25
    (value ((469664807,1877661931),(1679954569,1656891307)) * value ((1794094306,970136214),(692219080,662936248)) + value ((935552911,1268906353),(456913005,1928970014))) = _
  rw [multiplied,added]
#print axioms step
end AspisR1.JGd_Horner25
end
