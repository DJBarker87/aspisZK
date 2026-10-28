import NDO_JGd_Horner12
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Horner11
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open JGd_HornerData
def product : W := ((239679670,669395545),(713442031,1064697585))
def r11 : W := ((1539335187,563520647),(1169848937,615332853))
theorem multiplied : value ((469664807,1877661931),(1679954569,1656891307)) * value ((1275648678,1172189779),(1977691098,454519906)) = value product := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((469664807,1877661931),(1679954569,1656891307)) ((1275648678,1172189779),(1977691098,454519906)) = ((239679670,669395545),(713442031,1064697585))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms multiplied
theorem added : value product + value ((1299655517,2041608749),(456406906,1698118915)) = value r11 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((239679670,669395545),(713442031,1064697585)) ((1299655517,2041608749),(456406906,1698118915)) = ((1539335187,563520647),(1169848937,615332853))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added
theorem step : run 12 (value ((1275648678,1172189779),(1977691098,454519906))) = run 11 (value r11) := by
  unfold run
  rw [ExtractedMaskHornerPolynomial.hornerLoopModel]
  have hcell := JGd_Coefficients.value ⟨11,by omega⟩
  change coeff 11 = value (JGd_Coefficients.cell ⟨11,by omega⟩) at hcell
  rw [hcell]
  change ExtractedMaskHornerPolynomial.hornerLoopModel coeff (value JGd_Linear00.sum0) 11
    (value ((469664807,1877661931),(1679954569,1656891307)) * value ((1275648678,1172189779),(1977691098,454519906)) + value ((1299655517,2041608749),(456406906,1698118915))) = _
  rw [multiplied,added]
#print axioms step
end AspisR1.JGd_Horner11
end
