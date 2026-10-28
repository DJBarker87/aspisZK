import NDO_JGd_Linear08
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Linear07
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd

def term0 : W := ((2066617203,1872414487),(1580058634,1821004282))
def sum0 : W := ((1853419029,2007195391),(306748858,294164270))
theorem weighted0 : (157:Q) * value (JGd_LinearInputs.point ⟨7,by omega⟩) = value term0 := by
  change value ((157,0),(0,0)) * value (JGd_LinearInputs.point ⟨7,by omega⟩) = value term0
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((157,0),(0,0)) ((2023864416,983081232),(187881185,1338388013)) = ((2066617203,1872414487),(1580058634,1821004282))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms weighted0
theorem added0 : value term0 + value ((1934285473,134780904),(874173871,620643635)) = value sum0 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((2066617203,1872414487),(1580058634,1821004282)) ((1934285473,134780904),(874173871,620643635)) = ((1853419029,2007195391),(306748858,294164270))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added0

def term16 : W := ((1560759744,1207542318),(1981950720,1690108450))
def sum16 : W := ((221100791,711359310),(955979577,1457828099))
theorem weighted16 : (1325:Q) * value (JGd_LinearInputs.point ⟨7,by omega⟩) = value term16 := by
  change value ((1325,0),(0,0)) * value (JGd_LinearInputs.point ⟨7,by omega⟩) = value term16
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((1325,0),(0,0)) ((2023864416,983081232),(187881185,1338388013)) = ((1560759744,1207542318),(1981950720,1690108450))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms weighted16
theorem added16 : value term16 + value ((807824694,1651300639),(1121512504,1915203296)) = value sum16 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((1560759744,1207542318),(1981950720,1690108450)) ((807824694,1651300639),(1121512504,1915203296)) = ((221100791,711359310),(955979577,1457828099))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added16
end AspisR1.JGd_Linear07
end
