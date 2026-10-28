import NDO_JGd_Horner16
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Horner15
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open JGd_HornerData
def product : W := ((1984196919,529704294),(1250452271,761220750))
def r15 : W := ((2020342205,1200719544),(922953732,389034965))
theorem multiplied : value ((469664807,1877661931),(1679954569,1656891307)) * value ((1660949729,1502283359),(1020615360,1891933949)) = value product := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((469664807,1877661931),(1679954569,1656891307)) ((1660949729,1502283359),(1020615360,1891933949)) = ((1984196919,529704294),(1250452271,761220750))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms multiplied
theorem added : value product + value ((36145286,671015250),(1819985108,1775297862)) = value r15 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((1984196919,529704294),(1250452271,761220750)) ((36145286,671015250),(1819985108,1775297862)) = ((2020342205,1200719544),(922953732,389034965))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added
theorem step : run 16 (value ((1660949729,1502283359),(1020615360,1891933949))) = run 15 (value r15) := by
  unfold run
  rw [ExtractedMaskHornerPolynomial.hornerLoopModel]
  have hcell := JGd_Coefficients.value ⟨15,by omega⟩
  change coeff 15 = value (JGd_Coefficients.cell ⟨15,by omega⟩) at hcell
  rw [hcell]
  change ExtractedMaskHornerPolynomial.hornerLoopModel coeff (value JGd_Linear00.sum0) 15
    (value ((469664807,1877661931),(1679954569,1656891307)) * value ((1660949729,1502283359),(1020615360,1891933949)) + value ((36145286,671015250),(1819985108,1775297862))) = _
  rw [multiplied,added]
#print axioms step
end AspisR1.JGd_Horner15
end
