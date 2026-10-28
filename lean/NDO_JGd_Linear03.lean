import NDO_JGd_Linear04
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Linear03
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd

def term0 : W := ((1517091642,984336821),(418409244,1346475248))
def sum0 : W := ((1720372698,815443491),(1962643106,2067598911))
theorem weighted0 : (69:Q) * value (JGd_LinearInputs.point ⟨3,by omega⟩) = value term0 := by
  change value ((69,0),(0,0)) * value (JGd_LinearInputs.point ⟨3,by omega⟩) = value term0
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((69,0),(0,0)) ((1142413086,2006134641),(1686703278,2011383024)) = ((1517091642,984336821),(418409244,1346475248))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms weighted0
theorem added0 : value term0 + value ((203281056,1978590317),(1544233862,721123663)) = value sum0 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((1517091642,984336821),(418409244,1346475248)) ((203281056,1978590317),(1544233862,721123663)) = ((1720372698,815443491),(1962643106,2067598911))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added0

def term16 : W := ((1468283255,601185706),(941681407,111296087))
def sum16 : W := ((1004632176,1594722932),(1813461325,2138679942))
theorem weighted16 : (725:Q) * value (JGd_LinearInputs.point ⟨3,by omega⟩) = value term16 := by
  change value ((725,0),(0,0)) * value (JGd_LinearInputs.point ⟨3,by omega⟩) = value term16
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((725,0),(0,0)) ((1142413086,2006134641),(1686703278,2011383024)) = ((1468283255,601185706),(941681407,111296087))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms weighted16
theorem added16 : value term16 + value ((1683832568,993537226),(871779918,2027383855)) = value sum16 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((1468283255,601185706),(941681407,111296087)) ((1683832568,993537226),(871779918,2027383855)) = ((1004632176,1594722932),(1813461325,2138679942))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added16
end AspisR1.JGd_Linear03
end
