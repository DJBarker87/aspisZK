import NDO_JGd_Linear01
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Linear00
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd

def term0 : W := ((2116030338,1550861857),(465531605,609926115))
def sum0 : W := ((469664807,1877661931),(1679954569,1656891307))
theorem weighted0 : (3:Q) * value (JGd_LinearInputs.point ⟨0,by omega⟩) = value term0 := by
  change value ((3,0),(0,0)) * value (JGd_LinearInputs.point ⟨0,by omega⟩) = value term0
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((3,0),(0,0)) ((705343446,1948609717),(871005084,203308705)) = ((2116030338,1550861857),(465531605,609926115))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms weighted0
theorem added0 : value term0 + value ((501118116,326800074),(1214422964,1046965192)) = value sum0 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((2116030338,1550861857),(465531605,609926115)) ((501118116,326800074),(1214422964,1046965192)) = ((469664807,1877661931),(1679954569,1656891307))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added0

def term16 : W := ((695919420,1144244072),(1155713283,75319053))
def sum16 : W := ((533099968,803914706),(1501807103,1266007432))
theorem weighted16 : (275:Q) * value (JGd_LinearInputs.point ⟨0,by omega⟩) = value term16 := by
  change value ((275,0),(0,0)) * value (JGd_LinearInputs.point ⟨0,by omega⟩) = value term16
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((275,0),(0,0)) ((705343446,1948609717),(871005084,203308705)) = ((695919420,1144244072),(1155713283,75319053))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms weighted16
theorem added16 : value term16 + value ((1984664195,1807154281),(346093820,1190688379)) = value sum16 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((695919420,1144244072),(1155713283,75319053)) ((1984664195,1807154281),(346093820,1190688379)) = ((533099968,803914706),(1501807103,1266007432))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added16
end AspisR1.JGd_Linear00
end
