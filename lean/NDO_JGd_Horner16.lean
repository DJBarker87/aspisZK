import NDO_JGd_Horner17
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Horner16
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open JGd_HornerData
def product : W := ((2049972755,1938142748),(1234581590,300694555))
def r16 : W := ((1660949729,1502283359),(1020615360,1891933949))
theorem multiplied : value ((469664807,1877661931),(1679954569,1656891307)) * value ((1338339918,1712498283),(232266419,674753779)) = value product := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((469664807,1877661931),(1679954569,1656891307)) ((1338339918,1712498283),(232266419,674753779)) = ((2049972755,1938142748),(1234581590,300694555))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms multiplied
theorem added : value product + value ((1758460621,1711624258),(1933517417,1591239394)) = value r16 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((2049972755,1938142748),(1234581590,300694555)) ((1758460621,1711624258),(1933517417,1591239394)) = ((1660949729,1502283359),(1020615360,1891933949))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added
theorem step : run 17 (value ((1338339918,1712498283),(232266419,674753779))) = run 16 (value r16) := by
  unfold run
  rw [ExtractedMaskHornerPolynomial.hornerLoopModel]
  have hcell := JGd_Coefficients.value ⟨16,by omega⟩
  change coeff 16 = value (JGd_Coefficients.cell ⟨16,by omega⟩) at hcell
  rw [hcell]
  change ExtractedMaskHornerPolynomial.hornerLoopModel coeff (value JGd_Linear00.sum0) 16
    (value ((469664807,1877661931),(1679954569,1656891307)) * value ((1338339918,1712498283),(232266419,674753779)) + value ((1758460621,1711624258),(1933517417,1591239394))) = _
  rw [multiplied,added]
#print axioms step
end AspisR1.JGd_Horner16
end
