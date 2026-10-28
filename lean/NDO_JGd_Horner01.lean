import NDO_JGd_Horner02
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Horner01
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open JGd_HornerData
def product : W := ((2053838649,550688504),(111777432,422660608))
def r01 : W := ((385912378,868630160),(417736381,1863398263))
theorem multiplied : value ((469664807,1877661931),(1679954569,1656891307)) * value ((350980296,162225165),(827189199,1562618718)) = value product := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((469664807,1877661931),(1679954569,1656891307)) ((350980296,162225165),(827189199,1562618718)) = ((2053838649,550688504),(111777432,422660608))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms multiplied
theorem added : value product + value ((479557376,317941656),(305958949,1440737655)) = value r01 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((2053838649,550688504),(111777432,422660608)) ((479557376,317941656),(305958949,1440737655)) = ((385912378,868630160),(417736381,1863398263))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added
theorem step : run 2 (value ((350980296,162225165),(827189199,1562618718))) = run 1 (value r01) := by
  unfold run
  rw [ExtractedMaskHornerPolynomial.hornerLoopModel]
  have hcell := JGd_Coefficients.value ⟨1,by omega⟩
  change coeff 1 = value (JGd_Coefficients.cell ⟨1,by omega⟩) at hcell
  rw [hcell]
  change ExtractedMaskHornerPolynomial.hornerLoopModel coeff (value JGd_Linear00.sum0) 1
    (value ((469664807,1877661931),(1679954569,1656891307)) * value ((350980296,162225165),(827189199,1562618718)) + value ((479557376,317941656),(305958949,1440737655))) = _
  rw [multiplied,added]
#print axioms step
end AspisR1.JGd_Horner01
end
