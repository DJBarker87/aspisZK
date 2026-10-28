import NDO_JGd_Horner09
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Horner08
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open JGd_HornerData
def product : W := ((1390888837,1449801874),(68334176,611857429))
def r08 : W := ((2043513133,2025476135),(1808241230,593119279))
theorem multiplied : value ((469664807,1877661931),(1679954569,1656891307)) * value ((930486135,1344215832),(2076504029,487813092)) = value product := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((469664807,1877661931),(1679954569,1656891307)) ((930486135,1344215832),(2076504029,487813092)) = ((1390888837,1449801874),(68334176,611857429))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms multiplied
theorem added : value product + value ((652624296,575674261),(1739907054,2128745497)) = value r08 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((1390888837,1449801874),(68334176,611857429)) ((652624296,575674261),(1739907054,2128745497)) = ((2043513133,2025476135),(1808241230,593119279))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added
theorem step : run 9 (value ((930486135,1344215832),(2076504029,487813092))) = run 8 (value r08) := by
  unfold run
  rw [ExtractedMaskHornerPolynomial.hornerLoopModel]
  have hcell := JGd_Coefficients.value ⟨8,by omega⟩
  change coeff 8 = value (JGd_Coefficients.cell ⟨8,by omega⟩) at hcell
  rw [hcell]
  change ExtractedMaskHornerPolynomial.hornerLoopModel coeff (value JGd_Linear00.sum0) 8
    (value ((469664807,1877661931),(1679954569,1656891307)) * value ((930486135,1344215832),(2076504029,487813092)) + value ((652624296,575674261),(1739907054,2128745497))) = _
  rw [multiplied,added]
#print axioms step
end AspisR1.JGd_Horner08
end
