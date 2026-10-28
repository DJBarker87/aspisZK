import NDO_JGd_Horner11
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Horner10
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open JGd_HornerData
def product : W := ((912533032,222510860),(615996922,69790775))
def r10 : W := ((1626205337,483512162),(967873852,15539679))
theorem multiplied : value ((469664807,1877661931),(1679954569,1656891307)) * value ((1539335187,563520647),(1169848937,615332853)) = value product := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((469664807,1877661931),(1679954569,1656891307)) ((1539335187,563520647),(1169848937,615332853)) = ((912533032,222510860),(615996922,69790775))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms multiplied
theorem added : value product + value ((713672305,261001302),(351876930,2093232551)) = value r10 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((912533032,222510860),(615996922,69790775)) ((713672305,261001302),(351876930,2093232551)) = ((1626205337,483512162),(967873852,15539679))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added
theorem step : run 11 (value ((1539335187,563520647),(1169848937,615332853))) = run 10 (value r10) := by
  unfold run
  rw [ExtractedMaskHornerPolynomial.hornerLoopModel]
  have hcell := JGd_Coefficients.value ⟨10,by omega⟩
  change coeff 10 = value (JGd_Coefficients.cell ⟨10,by omega⟩) at hcell
  rw [hcell]
  change ExtractedMaskHornerPolynomial.hornerLoopModel coeff (value JGd_Linear00.sum0) 10
    (value ((469664807,1877661931),(1679954569,1656891307)) * value ((1539335187,563520647),(1169848937,615332853)) + value ((713672305,261001302),(351876930,2093232551))) = _
  rw [multiplied,added]
#print axioms step
end AspisR1.JGd_Horner10
end
