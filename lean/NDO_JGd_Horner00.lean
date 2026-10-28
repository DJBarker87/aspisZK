import NDO_JGd_Horner01
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Horner00
open JGd_ExactWords
open JGd_HornerData
def product : W := ((1615308192,649996109),(1524680159,1524393093))
def r00 : W := ((730498243,234698042),(882910042,2122991591))
theorem multiplied : value ((469664807,1877661931),(1679954569,1656891307)) * value ((385912378,868630160),(417736381,1863398263)) = value product := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((469664807,1877661931),(1679954569,1656891307)) ((385912378,868630160),(417736381,1863398263)) = ((1615308192,649996109),(1524680159,1524393093))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms multiplied
theorem added : value product + value ((1262673698,1732185580),(1505713530,598598498)) = value r00 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((1615308192,649996109),(1524680159,1524393093)) ((1262673698,1732185580),(1505713530,598598498)) = ((730498243,234698042),(882910042,2122991591))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added
theorem step : run 1 (value ((385912378,868630160),(417736381,1863398263))) = run 0 (value r00) := by
  unfold run
  conv_lhs => rw [ExtractedMaskHornerPolynomial.hornerLoopModel]
  have hcell := JGd_Coefficients.value ⟨0,by omega⟩
  change coeff 0 = value (JGd_Coefficients.cell ⟨0,by omega⟩) at hcell
  rw [hcell]
  change ExtractedMaskHornerPolynomial.hornerLoopModel coeff (value JGd_Linear00.sum0) 0
    (value ((469664807,1877661931),(1679954569,1656891307)) * value ((385912378,868630160),(417736381,1863398263)) + value ((1262673698,1732185580),(1505713530,598598498))) = _
  rw [multiplied,added]
#print axioms step
end AspisR1.JGd_Horner00
end
