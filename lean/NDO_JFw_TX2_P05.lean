import NDO_JFw_TX2_P04
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P05
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨1554033304#u32,67370206#u32⟩,⟨1410213748#u32,1369248953#u32⟩⟩,⟨⟨1419170319#u32,1866942376#u32⟩,⟨1271796599#u32,2073962627#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1554033304<2147483647 ∧ 67370206<2147483647) ∧ (1410213748<2147483647 ∧ 1369248953<2147483647)) ∧
    ((1419170319<2147483647 ∧ 1866942376<2147483647) ∧ (1271796599<2147483647 ∧ 2073962627<2147483647))
  omega
theorem lane0 : (-3274474887921322567 : ZMod 2147483647)=1554033304 := by decide
theorem lane1 : (24939305871369801660 : ZMod 2147483647)=67370206 := by decide
theorem lane2 : (4090491803135211061 : ZMod 2147483647)=1410213748 := by decide
theorem lane3 : (15108001040920233705 : ZMod 2147483647)=1369248953 := by decide
theorem lane4 : (1717505573444597151 : ZMod 2147483647)=1419170319 := by decide
theorem lane5 : (20724073229643276810 : ZMod 2147483647)=1866942376 := by decide
theorem lane6 : (1655217659792133141 : ZMod 2147483647)=1271796599 := by decide
theorem lane7 : (11500487230609836057 : ZMod 2147483647)=2073962627 := by decide
theorem step : decode JFw_TX2_P04.value * decode gamma=decode value := by
  change (⟨⟨⟨1106523000,729079828⟩,⟨1074182998,246996287⟩⟩,⟨⟨634588140,1559245386⟩,⟨1947503436,547797802⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩=⟨⟨⟨1554033304,67370206⟩,⟨1410213748,1369248953⟩⟩,⟨⟨1419170319,1866942376⟩,⟨1271796599,2073962627⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^5 := by
  rw [show 5=(4:Nat)+1 from rfl,pow_succ,← JFw_TX2_P04.meaning]
  exact step.symm
theorem source : entry 5=value := identify 5 value canonical meaning
#print axioms canonical
#print axioms lane0
#print axioms lane1
#print axioms lane2
#print axioms lane3
#print axioms lane4
#print axioms lane5
#print axioms lane6
#print axioms lane7
#print axioms step
#print axioms meaning
#print axioms source
end AspisR1.JFw_TX2_P05
end
