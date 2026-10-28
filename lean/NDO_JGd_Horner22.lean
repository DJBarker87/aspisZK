import NDO_JGd_Horner23
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Horner22
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open JGd_HornerData
def product : W := ((2036115703,1508357552),(864332402,194218939))
def r22 : W := ((930292465,1445556103),(992330015,305690399))
theorem multiplied : value ((469664807,1877661931),(1679954569,1656891307)) * value ((1761097444,422340254),(729975717,1509473805)) = value product := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((469664807,1877661931),(1679954569,1656891307)) ((1761097444,422340254),(729975717,1509473805)) = ((2036115703,1508357552),(864332402,194218939))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms multiplied
theorem added : value product + value ((1041660409,2084682198),(127997613,111471460)) = value r22 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((2036115703,1508357552),(864332402,194218939)) ((1041660409,2084682198),(127997613,111471460)) = ((930292465,1445556103),(992330015,305690399))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added
theorem step : run 23 (value ((1761097444,422340254),(729975717,1509473805))) = run 22 (value r22) := by
  unfold run
  rw [ExtractedMaskHornerPolynomial.hornerLoopModel]
  have hcell := JGd_Coefficients.value ⟨22,by omega⟩
  change coeff 22 = value (JGd_Coefficients.cell ⟨22,by omega⟩) at hcell
  rw [hcell]
  change ExtractedMaskHornerPolynomial.hornerLoopModel coeff (value JGd_Linear00.sum0) 22
    (value ((469664807,1877661931),(1679954569,1656891307)) * value ((1761097444,422340254),(729975717,1509473805)) + value ((1041660409,2084682198),(127997613,111471460))) = _
  rw [multiplied,added]
#print axioms step
end AspisR1.JGd_Horner22
end
