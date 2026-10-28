import NDO_JGd_Horner22
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Horner21
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open JGd_HornerData
def product : W := ((1370869718,583384832),(225178470,6997038))
def r21 : W := ((229264195,615091949),(1697162726,1562689920))
theorem multiplied : value ((469664807,1877661931),(1679954569,1656891307)) * value ((930292465,1445556103),(992330015,305690399)) = value product := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((469664807,1877661931),(1679954569,1656891307)) ((930292465,1445556103),(992330015,305690399)) = ((1370869718,583384832),(225178470,6997038))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms multiplied
theorem added : value product + value ((1005878124,31707117),(1471984256,1555692882)) = value r21 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((1370869718,583384832),(225178470,6997038)) ((1005878124,31707117),(1471984256,1555692882)) = ((229264195,615091949),(1697162726,1562689920))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added
theorem step : run 22 (value ((930292465,1445556103),(992330015,305690399))) = run 21 (value r21) := by
  unfold run
  rw [ExtractedMaskHornerPolynomial.hornerLoopModel]
  have hcell := JGd_Coefficients.value ⟨21,by omega⟩
  change coeff 21 = value (JGd_Coefficients.cell ⟨21,by omega⟩) at hcell
  rw [hcell]
  change ExtractedMaskHornerPolynomial.hornerLoopModel coeff (value JGd_Linear00.sum0) 21
    (value ((469664807,1877661931),(1679954569,1656891307)) * value ((930292465,1445556103),(992330015,305690399)) + value ((1005878124,31707117),(1471984256,1555692882))) = _
  rw [multiplied,added]
#print axioms step
end AspisR1.JGd_Horner21
end
