import NDO_JGd_Horner10
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Horner09
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open JGd_HornerData
def product : W := ((1338529153,730203998),(2069494456,1600715568))
def r09 : W := ((930486135,1344215832),(2076504029,487813092))
theorem multiplied : value ((469664807,1877661931),(1679954569,1656891307)) * value ((1626205337,483512162),(967873852,15539679)) = value product := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((469664807,1877661931),(1679954569,1656891307)) ((1626205337,483512162),(967873852,15539679)) = ((1338529153,730203998),(2069494456,1600715568))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms multiplied
theorem added : value product + value ((1739440629,614011834),(7009573,1034581171)) = value r09 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((1338529153,730203998),(2069494456,1600715568)) ((1739440629,614011834),(7009573,1034581171)) = ((930486135,1344215832),(2076504029,487813092))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added
theorem step : run 10 (value ((1626205337,483512162),(967873852,15539679))) = run 9 (value r09) := by
  unfold run
  rw [ExtractedMaskHornerPolynomial.hornerLoopModel]
  have hcell := JGd_Coefficients.value ⟨9,by omega⟩
  change coeff 9 = value (JGd_Coefficients.cell ⟨9,by omega⟩) at hcell
  rw [hcell]
  change ExtractedMaskHornerPolynomial.hornerLoopModel coeff (value JGd_Linear00.sum0) 9
    (value ((469664807,1877661931),(1679954569,1656891307)) * value ((1626205337,483512162),(967873852,15539679)) + value ((1739440629,614011834),(7009573,1034581171))) = _
  rw [multiplied,added]
#print axioms step
end AspisR1.JGd_Horner09
end
