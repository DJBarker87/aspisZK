import NDO_JGd_Horner13
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Horner12
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open JGd_HornerData
def product : W := ((1606089999,570014095),(457905813,36676785))
def r12 : W := ((1275648678,1172189779),(1977691098,454519906))
theorem multiplied : value ((469664807,1877661931),(1679954569,1656891307)) * value ((525372466,2128502753),(1682718843,1963387864)) = value product := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((469664807,1877661931),(1679954569,1656891307)) ((525372466,2128502753),(1682718843,1963387864)) = ((1606089999,570014095),(457905813,36676785))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms multiplied
theorem added : value product + value ((1817042326,602175684),(1519785285,417843121)) = value r12 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((1606089999,570014095),(457905813,36676785)) ((1817042326,602175684),(1519785285,417843121)) = ((1275648678,1172189779),(1977691098,454519906))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added
theorem step : run 13 (value ((525372466,2128502753),(1682718843,1963387864))) = run 12 (value r12) := by
  unfold run
  rw [ExtractedMaskHornerPolynomial.hornerLoopModel]
  have hcell := JGd_Coefficients.value ⟨12,by omega⟩
  change coeff 12 = value (JGd_Coefficients.cell ⟨12,by omega⟩) at hcell
  rw [hcell]
  change ExtractedMaskHornerPolynomial.hornerLoopModel coeff (value JGd_Linear00.sum0) 12
    (value ((469664807,1877661931),(1679954569,1656891307)) * value ((525372466,2128502753),(1682718843,1963387864)) + value ((1817042326,602175684),(1519785285,417843121))) = _
  rw [multiplied,added]
#print axioms step
end AspisR1.JGd_Horner12
end
