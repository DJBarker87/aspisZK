import NDO_JGd_Horner18
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Horner17
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open JGd_HornerData
def product : W := ((24124051,388625302),(44807530,98722919))
def r17 : W := ((1338339918,1712498283),(232266419,674753779))
theorem multiplied : value ((469664807,1877661931),(1679954569,1656891307)) * value ((1223403448,67439174),(1961456849,1815156440)) = value product := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((469664807,1877661931),(1679954569,1656891307)) ((1223403448,67439174),(1961456849,1815156440)) = ((24124051,388625302),(44807530,98722919))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms multiplied
theorem added : value product + value ((1314215867,1323872981),(187458889,576030860)) = value r17 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((24124051,388625302),(44807530,98722919)) ((1314215867,1323872981),(187458889,576030860)) = ((1338339918,1712498283),(232266419,674753779))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added
theorem step : run 18 (value ((1223403448,67439174),(1961456849,1815156440))) = run 17 (value r17) := by
  unfold run
  rw [ExtractedMaskHornerPolynomial.hornerLoopModel]
  have hcell := JGd_Coefficients.value ⟨17,by omega⟩
  change coeff 17 = value (JGd_Coefficients.cell ⟨17,by omega⟩) at hcell
  rw [hcell]
  change ExtractedMaskHornerPolynomial.hornerLoopModel coeff (value JGd_Linear00.sum0) 17
    (value ((469664807,1877661931),(1679954569,1656891307)) * value ((1223403448,67439174),(1961456849,1815156440)) + value ((1314215867,1323872981),(187458889,576030860))) = _
  rw [multiplied,added]
#print axioms step
end AspisR1.JGd_Horner17
end
