import NDO_JGd_Linear05
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Linear04
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd

def term0 : W := ((1900399392,1130914827),(2014881777,1992083753))
def sum0 : W := ((203281056,1978590317),(1544233862,721123663))
theorem weighted0 : (91:Q) * value (JGd_LinearInputs.point ⟨4,by omega⟩) = value term0 := by
  change value ((91,0),(0,0)) * value (JGd_LinearInputs.point ⟨4,by omega⟩) = value term0
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((91,0),(0,0)) ((1106424694,342809735),(1036886578,305075687)) = ((1900399392,1130914827),(2014881777,1992083753))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms weighted0
theorem added0 : value term0 + value ((450365311,847675490),(1676835732,876523557)) = value sum0 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((1900399392,1130914827),(2014881777,1992083753)) ((450365311,847675490),(1676835732,876523557)) = ((203281056,1978590317),(1544233862,721123663))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added0

def term16 : W := ((1753966100,1458291192),(1037656716,653253897))
def sum16 : W := ((1683832568,993537226),(871779918,2027383855))
theorem weighted16 : (875:Q) * value (JGd_LinearInputs.point ⟨4,by omega⟩) = value term16 := by
  change value ((875,0),(0,0)) * value (JGd_LinearInputs.point ⟨4,by omega⟩) = value term16
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((875,0),(0,0)) ((1106424694,342809735),(1036886578,305075687)) = ((1753966100,1458291192),(1037656716,653253897))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms weighted16
theorem added16 : value term16 + value ((2077350115,1682729681),(1981606849,1374129958)) = value sum16 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((1753966100,1458291192),(1037656716,653253897)) ((2077350115,1682729681),(1981606849,1374129958)) = ((1683832568,993537226),(871779918,2027383855))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added16
end AspisR1.JGd_Linear04
end
