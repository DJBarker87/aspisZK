import NDO_JGd_Linear02
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Linear01
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd

def term0 : W := ((334689768,1011293432),(1794921867,925452393))
def sum0 : W := ((501118116,326800074),(1214422964,1046965192))
theorem weighted0 : (25:Q) * value (JGd_LinearInputs.point ⟨1,by omega⟩) = value term0 := by
  change value ((25,0),(0,0)) * value (JGd_LinearInputs.point ⟨1,by omega⟩) = value term0
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((25,0),(0,0)) ((528783666,1672539309),(1274387717,552414171)) = ((334689768,1011293432),(1794921867,925452393))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms weighted0
theorem added0 : value term0 + value ((166428348,1462990289),(1566984744,121512799)) = value sum0 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((334689768,1011293432),(1794921867,925452393)) ((166428348,1462990289),(1566984744,121512799)) = ((501118116,326800074),(1214422964,1046965192))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added0

def term16 : W := ((1394758762,12119168),(448900681,700305152))
def sum16 : W := ((1984664195,1807154281),(346093820,1190688379))
theorem weighted16 : (425:Q) * value (JGd_LinearInputs.point ⟨1,by omega⟩) = value term16 := by
  change value ((425,0),(0,0)) * value (JGd_LinearInputs.point ⟨1,by omega⟩) = value term16
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((425,0),(0,0)) ((528783666,1672539309),(1274387717,552414171)) = ((1394758762,12119168),(448900681,700305152))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms weighted16
theorem added16 : value term16 + value ((589905433,1795035113),(2044676786,490383227)) = value sum16 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((1394758762,12119168),(448900681,700305152)) ((589905433,1795035113),(2044676786,490383227)) = ((1984664195,1807154281),(346093820,1190688379))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added16
end AspisR1.JGd_Linear01
end
