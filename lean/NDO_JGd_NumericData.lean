import NDO_JGd_HornerValue
import NDO_JGb_MaskedArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_NumericData
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open Aeneas Aeneas.Std Result
def factor : W := ((60053925,1891194216),(2090430923,260852809))
def weightedMask : W := ((1458369550,1316359454),(1385711809,768552005))
def maskWords : W := ((41384146,1551057496),(121138204,744059949))
def neededWords : W := ((1711374173,2026192144),(428817833,318295749))
def weightedTerminal : W := ((1574260507,1154902378),(1324960351,336188747))
def partialWords : W := ((1615644653,558476227),(1446098555,1080248696))
def mask : FIp_SemanticArithmetic.MQ := ⟨⟨41384146#u32,1551057496#u32⟩,⟨121138204#u32,744059949#u32⟩⟩
theorem mask_canonical : FIp_SemanticValues.Canon mask := by
  change (41384146<2147483647 ∧ 1551057496<2147483647) ∧ (121138204<2147483647 ∧ 744059949<2147483647)
  omega
#print axioms mask_canonical
def neededTerminal : FIp_SemanticArithmetic.MQ := ⟨⟨1711374173#u32,2026192144#u32⟩,⟨428817833#u32,318295749#u32⟩⟩
theorem neededTerminal_canonical : FIp_SemanticValues.Canon neededTerminal := by
  change (1711374173<2147483647 ∧ 2026192144<2147483647) ∧ (428817833<2147483647 ∧ 318295749<2147483647)
  omega
#print axioms neededTerminal_canonical
def running : FIp_SemanticArithmetic.MQ := ⟨⟨1645475237#u32,1054917232#u32⟩,⟨2009538975#u32,558867101#u32⟩⟩
theorem running_canonical : FIp_SemanticValues.Canon running := by
  change (1645475237<2147483647 ∧ 1054917232<2147483647) ∧ (2009538975<2147483647 ∧ 558867101<2147483647)
  omega
#print axioms running_canonical
theorem factor_value : value ((1,0),(0,0)) + value ((60053924,1891194216),(2090430923,260852809)) = value ((60053925,1891194216),(2090430923,260852809)) := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((1,0),(0,0)) ((60053924,1891194216),(2090430923,260852809)) = ((60053925,1891194216),(2090430923,260852809))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms factor_value
theorem mask_product : value ((60053925,1891194216),(2090430923,260852809)) * value ((839969315,1393507838),(1451026085,492151165)) = value ((1458369550,1316359454),(1385711809,768552005)) := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((60053925,1891194216),(2090430923,260852809)) ((839969315,1393507838),(1451026085,492151165)) = ((1458369550,1316359454),(1385711809,768552005))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms mask_product
theorem mask_sum : value ((730498243,234698042),(882910042,2122991591)) + value ((1458369550,1316359454),(1385711809,768552005)) = value ((41384146,1551057496),(121138204,744059949)) := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((730498243,234698042),(882910042,2122991591)) ((1458369550,1316359454),(1385711809,768552005)) = ((41384146,1551057496),(121138204,744059949))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms mask_sum
theorem terminal_product : value ((1518895880,1177859893),(464691262,913595700)) * value ((1711374173,2026192144),(428817833,318295749)) = value ((1574260507,1154902378),(1324960351,336188747)) := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((1518895880,1177859893),(464691262,913595700)) ((1711374173,2026192144),(428817833,318295749)) = ((1574260507,1154902378),(1324960351,336188747))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms terminal_product
theorem partial_value : value ((41384146,1551057496),(121138204,744059949)) + value ((1574260507,1154902378),(1324960351,336188747)) = value ((1615644653,558476227),(1446098555,1080248696)) := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((41384146,1551057496),(121138204,744059949)) ((1574260507,1154902378),(1324960351,336188747)) = ((1615644653,558476227),(1446098555,1080248696))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms partial_value
theorem running_value : value ((1615644653,558476227),(1446098555,1080248696)) + value ((29830584,496441005),(563440420,1626102052)) = value ((1645475237,1054917232),(2009538975,558867101)) := by
  apply add
  change AspisV8R17.GeneratedQM31Linear.qmAddWords ((1615644653,558476227),(1446098555,1080248696)) ((29830584,496441005),(563440420,1626102052)) = ((1645475237,1054917232),(2009538975,558867101))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms running_value
end AspisR1.JGd_NumericData
end
