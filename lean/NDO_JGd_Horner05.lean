import NDO_JGd_Horner06
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Horner05
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open JGd_HornerData
def product : W := ((958183041,1450212922),(185553575,1268164959))
def r05 : W := ((2054300134,433335707),(567630864,504667434))
theorem multiplied : value ((469664807,1877661931),(1679954569,1656891307)) * value ((1964697577,1204117337),(1405943572,753417738)) = value product := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((469664807,1877661931),(1679954569,1656891307)) ((1964697577,1204117337),(1405943572,753417738)) = ((958183041,1450212922),(185553575,1268164959))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms multiplied
theorem added : value product + value ((1096117093,1130606432),(382077289,1383986122)) = value r05 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((958183041,1450212922),(185553575,1268164959)) ((1096117093,1130606432),(382077289,1383986122)) = ((2054300134,433335707),(567630864,504667434))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added
theorem step : run 6 (value ((1964697577,1204117337),(1405943572,753417738))) = run 5 (value r05) := by
  unfold run
  rw [ExtractedMaskHornerPolynomial.hornerLoopModel]
  have hcell := JGd_Coefficients.value ⟨5,by omega⟩
  change coeff 5 = value (JGd_Coefficients.cell ⟨5,by omega⟩) at hcell
  rw [hcell]
  change ExtractedMaskHornerPolynomial.hornerLoopModel coeff (value JGd_Linear00.sum0) 5
    (value ((469664807,1877661931),(1679954569,1656891307)) * value ((1964697577,1204117337),(1405943572,753417738)) + value ((1096117093,1130606432),(382077289,1383986122))) = _
  rw [multiplied,added]
#print axioms step
end AspisR1.JGd_Horner05
end
