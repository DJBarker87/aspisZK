import NDO_JGd_Horner14
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Horner13
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open JGd_HornerData
def product : W := ((242342877,1889412379),(802582190,891841705))
def r13 : W := ((525372466,2128502753),(1682718843,1963387864))
theorem multiplied : value ((469664807,1877661931),(1679954569,1656891307)) * value ((1242777076,1749228193),(723796383,139084810)) = value product := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((469664807,1877661931),(1679954569,1656891307)) ((1242777076,1749228193),(723796383,139084810)) = ((242342877,1889412379),(802582190,891841705))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms multiplied
theorem added : value product + value ((283029589,239090374),(880136653,1071546159)) = value r13 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((242342877,1889412379),(802582190,891841705)) ((283029589,239090374),(880136653,1071546159)) = ((525372466,2128502753),(1682718843,1963387864))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added
theorem step : run 14 (value ((1242777076,1749228193),(723796383,139084810))) = run 13 (value r13) := by
  unfold run
  rw [ExtractedMaskHornerPolynomial.hornerLoopModel]
  have hcell := JGd_Coefficients.value ⟨13,by omega⟩
  change coeff 13 = value (JGd_Coefficients.cell ⟨13,by omega⟩) at hcell
  rw [hcell]
  change ExtractedMaskHornerPolynomial.hornerLoopModel coeff (value JGd_Linear00.sum0) 13
    (value ((469664807,1877661931),(1679954569,1656891307)) * value ((1242777076,1749228193),(723796383,139084810)) + value ((283029589,239090374),(880136653,1071546159))) = _
  rw [multiplied,added]
#print axioms step
end AspisR1.JGd_Horner13
end
