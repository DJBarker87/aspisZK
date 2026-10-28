import NDO_JGd_Horner15
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Horner14
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open JGd_HornerData
def product : W := ((1977212217,1098963259),(393014220,1442479746))
def r14 : W := ((1242777076,1749228193),(723796383,139084810))
theorem multiplied : value ((469664807,1877661931),(1679954569,1656891307)) * value ((2020342205,1200719544),(922953732,389034965)) = value product := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((469664807,1877661931),(1679954569,1656891307)) ((2020342205,1200719544),(922953732,389034965)) = ((1977212217,1098963259),(393014220,1442479746))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms multiplied
theorem added : value product + value ((1413048506,650264934),(330782163,844088711)) = value r14 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((1977212217,1098963259),(393014220,1442479746)) ((1413048506,650264934),(330782163,844088711)) = ((1242777076,1749228193),(723796383,139084810))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added
theorem step : run 15 (value ((2020342205,1200719544),(922953732,389034965))) = run 14 (value r14) := by
  unfold run
  rw [ExtractedMaskHornerPolynomial.hornerLoopModel]
  have hcell := JGd_Coefficients.value ⟨14,by omega⟩
  change coeff 14 = value (JGd_Coefficients.cell ⟨14,by omega⟩) at hcell
  rw [hcell]
  change ExtractedMaskHornerPolynomial.hornerLoopModel coeff (value JGd_Linear00.sum0) 14
    (value ((469664807,1877661931),(1679954569,1656891307)) * value ((2020342205,1200719544),(922953732,389034965)) + value ((1413048506,650264934),(330782163,844088711))) = _
  rw [multiplied,added]
#print axioms step
end AspisR1.JGd_Horner14
end
