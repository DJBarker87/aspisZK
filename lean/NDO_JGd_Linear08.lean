import NDO_JGd_Linear09
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Linear08
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd

def term0 : W := ((1880522660,110045880),(817070051,891461882))
def sum0 : W := ((1934285473,134780904),(874173871,620643635))
theorem weighted0 : (179:Q) * value (JGd_LinearInputs.point ⟨8,by omega⟩) = value term0 := by
  change value ((179,0),(0,0)) * value (JGd_LinearInputs.point ⟨8,by omega⟩) = value term0
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((179,0),(0,0)) ((454398981,504493626),(2008082900,1252680230)) = ((1880522660,110045880),(817070051,891461882))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms weighted0
theorem added0 : value term0 + value ((53762813,24735024),(57103820,1876665400)) = value sum0 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((1880522660,110045880),(817070051,891461882)) ((53762813,24735024),(57103820,1876665400)) = ((1934285473,134780904),(874173871,620643635))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added0

def term16 : W := ((223599111,1098756488),(542328287,867402830))
def sum16 : W := ((807824694,1651300639),(1121512504,1915203296))
theorem weighted16 : (1475:Q) * value (JGd_LinearInputs.point ⟨8,by omega⟩) = value term16 := by
  change value ((1475,0),(0,0)) * value (JGd_LinearInputs.point ⟨8,by omega⟩) = value term16
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((1475,0),(0,0)) ((454398981,504493626),(2008082900,1252680230)) = ((223599111,1098756488),(542328287,867402830))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms weighted16
theorem added16 : value term16 + value ((584225583,552544151),(579184217,1047800466)) = value sum16 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((223599111,1098756488),(542328287,867402830)) ((584225583,552544151),(579184217,1047800466)) = ((807824694,1651300639),(1121512504,1915203296))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added16
end AspisR1.JGd_Linear08
end
