import NDO_JGd_Linear06
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Linear05
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd

def term0 : W := ((1428239137,1822020959),(976236891,1280522748))
def sum0 : W := ((450365311,847675490),(1676835732,876523557))
theorem weighted0 : (113:Q) * value (JGd_LinearInputs.point ⟨5,by omega⟩) = value term0 := by
  change value ((113,0),(0,0)) * value (JGd_LinearInputs.point ⟨5,by omega⟩) = value term0
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((113,0),(0,0)) ((810819047,1156380883),(768810467,1018558903)) = ((1428239137,1822020959),(976236891,1280522748))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms weighted0
theorem added0 : value term0 + value ((1169609821,1173138178),(700598841,1743484456)) = value sum0 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((1428239137,1822020959),(976236891,1280522748)) ((1169609821,1173138178),(700598841,1743484456)) = ((450365311,847675490),(1676835732,876523557))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added0

def term16 : W := ((13351786,2026915578),(2051713873,345823133))
def sum16 : W := ((2077350115,1682729681),(1981606849,1374129958))
theorem weighted16 : (1025:Q) * value (JGd_LinearInputs.point ⟨5,by omega⟩) = value term16 := by
  change value ((1025,0),(0,0)) * value (JGd_LinearInputs.point ⟨5,by omega⟩) = value term16
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((1025,0),(0,0)) ((810819047,1156380883),(768810467,1018558903)) = ((13351786,2026915578),(2051713873,345823133))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms weighted16
theorem added16 : value term16 + value ((2063998329,1803297750),(2077376623,1028306825)) = value sum16 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((13351786,2026915578),(2051713873,345823133)) ((2063998329,1803297750),(2077376623,1028306825)) = ((2077350115,1682729681),(1981606849,1374129958))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added16
end AspisR1.JGd_Linear05
end
