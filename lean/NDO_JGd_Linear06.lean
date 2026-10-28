import NDO_JGd_Linear07
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Linear06
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd

def term0 : W := ((1463674439,1313426434),(393849983,1449320186))
def sum0 : W := ((1169609821,1173138178),(700598841,1743484456))
theorem weighted0 : (135:Q) * value (JGd_LinearInputs.point ⟨6,by omega⟩) = value term0 := by
  change value ((135,0),(0,0)) * value (JGd_LinearInputs.point ⟨6,by omega⟩) = value term0
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((135,0),(0,0)) ((1410683225,375596669),(973261870,122086709)) = ((1463674439,1313426434),(393849983,1449320186))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms weighted0
theorem added0 : value term0 + value ((1853419029,2007195391),(306748858,294164270)) = value sum0 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((1463674439,1313426434),(393849983,1449320186)) ((1853419029,2007195391),(306748858,294164270)) = ((1169609821,1173138178),(700598841,1743484456))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added0

def term16 : W := ((1842897538,1091938440),(1121397046,1717962373))
def sum16 : W := ((2063998329,1803297750),(2077376623,1028306825))
theorem weighted16 : (1175:Q) * value (JGd_LinearInputs.point ⟨6,by omega⟩) = value term16 := by
  change value ((1175,0),(0,0)) * value (JGd_LinearInputs.point ⟨6,by omega⟩) = value term16
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((1175,0),(0,0)) ((1410683225,375596669),(973261870,122086709)) = ((1842897538,1091938440),(1121397046,1717962373))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms weighted16
theorem added16 : value term16 + value ((221100791,711359310),(955979577,1457828099)) = value sum16 := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((1842897538,1091938440),(1121397046,1717962373)) ((221100791,711359310),(955979577,1457828099)) = ((2063998329,1803297750),(2077376623,1028306825))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms added16
end AspisR1.JGd_Linear06
end
