import NDO_JGd_Horner05
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Horner04
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open JGd_HornerData
def product : W := ((593303217,22980093),(2025989694,400792478))
def r04 : W := ((1321832863,1686907802),(476564490,762595566))
theorem multiplied : value ((469664807,1877661931),(1679954569,1656891307)) * value ((2054300134,433335707),(567630864,504667434)) = value product := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((469664807,1877661931),(1679954569,1656891307)) ((2054300134,433335707),(567630864,504667434)) = ((593303217,22980093),(2025989694,400792478))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms multiplied
theorem added : value product + value ((728529646,1663927709),(598058443,361803088)) = value r04 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((593303217,22980093),(2025989694,400792478)) ((728529646,1663927709),(598058443,361803088)) = ((1321832863,1686907802),(476564490,762595566))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added
theorem step : run 5 (value ((2054300134,433335707),(567630864,504667434))) = run 4 (value r04) := by
  unfold run
  rw [ExtractedMaskHornerPolynomial.hornerLoopModel]
  have hcell := JGd_Coefficients.value ⟨4,by omega⟩
  change coeff 4 = value (JGd_Coefficients.cell ⟨4,by omega⟩) at hcell
  rw [hcell]
  change ExtractedMaskHornerPolynomial.hornerLoopModel coeff (value JGd_Linear00.sum0) 4
    (value ((469664807,1877661931),(1679954569,1656891307)) * value ((2054300134,433335707),(567630864,504667434)) + value ((728529646,1663927709),(598058443,361803088))) = _
  rw [multiplied,added]
#print axioms step
end AspisR1.JGd_Horner04
end
