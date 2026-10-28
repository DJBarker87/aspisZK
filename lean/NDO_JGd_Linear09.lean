import NDO_JGd_LinearInputs
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Linear09
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd

def term0 : W := ((53762813,24735024),(57103820,1876665400))
def sum0 : W := ((53762813,24735024),(57103820,1876665400))
theorem weighted0 : (201:Q) * value (JGd_LinearInputs.point ⟨9,by omega⟩) = value term0 := by
  change value ((201,0),(0,0)) * value (JGd_LinearInputs.point ⟨9,by omega⟩) = value term0
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((201,0),(0,0)) ((2030227143,1410410828),(1902035786,62756635)) = ((53762813,24735024),(57103820,1876665400))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms weighted0
theorem added0 : value term0 + value ((0,0),(0,0)) = value sum0 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((53762813,24735024),(57103820,1876665400)) ((0,0),(0,0)) = ((53762813,24735024),(57103820,1876665400))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added0

def term16 : W := ((584225583,552544151),(579184217,1047800466))
def sum16 : W := ((584225583,552544151),(579184217,1047800466))
theorem weighted16 : (1625:Q) * value (JGd_LinearInputs.point ⟨9,by omega⟩) = value term16 := by
  change value ((1625,0),(0,0)) * value (JGd_LinearInputs.point ⟨9,by omega⟩) = value term16
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((1625,0),(0,0)) ((2030227143,1410410828),(1902035786,62756635)) = ((584225583,552544151),(579184217,1047800466))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms weighted16
theorem added16 : value term16 + value ((0,0),(0,0)) = value sum16 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((584225583,552544151),(579184217,1047800466)) ((0,0),(0,0)) = ((584225583,552544151),(579184217,1047800466))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added16
end AspisR1.JGd_Linear09
end
