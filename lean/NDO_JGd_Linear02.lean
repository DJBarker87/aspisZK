import NDO_JGd_Linear03
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Linear02
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd

def term0 : W := ((593539297,647546798),(1751825285,201397535))
def sum0 : W := ((166428348,1462990289),(1566984744,121512799))
theorem weighted0 : (47:Q) * value (JGd_LinearInputs.point ⟨2,by omega⟩) = value term0 := by
  change value ((47,0),(0,0)) * value (JGd_LinearInputs.point ⟨2,by omega⟩) = value term0
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((47,0),(0,0)) ((1657509587,287924440),(1819227394,1192254731)) = ((593539297,647546798),(1751825285,201397535))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms weighted0
theorem added0 : value term0 + value ((1720372698,815443491),(1962643106,2067598911)) = value sum0 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((593539297,647546798),(1751825285,201397535)) ((1720372698,815443491),(1962643106,2067598911)) = ((166428348,1462990289),(1566984744,121512799))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added0

def term16 : W := ((1732756904,200312181),(231215461,499186932))
def sum16 : W := ((589905433,1795035113),(2044676786,490383227))
theorem weighted16 : (575:Q) * value (JGd_LinearInputs.point ⟨2,by omega⟩) = value term16 := by
  change value ((575,0),(0,0)) * value (JGd_LinearInputs.point ⟨2,by omega⟩) = value term16
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((575,0),(0,0)) ((1657509587,287924440),(1819227394,1192254731)) = ((1732756904,200312181),(231215461,499186932))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms weighted16
theorem added16 : value term16 + value ((1004632176,1594722932),(1813461325,2138679942)) = value sum16 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((1732756904,200312181),(231215461,499186932)) ((1004632176,1594722932),(1813461325,2138679942)) = ((589905433,1795035113),(2044676786,490383227))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added16
end AspisR1.JGd_Linear02
end
