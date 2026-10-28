import NDO_JFw_TX2_P05
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P06
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨1430280692#u32,1685049618#u32⟩,⟨1182702806#u32,1132591724#u32⟩⟩,⟨⟨1702860885#u32,1973593402#u32⟩,⟨1660157177#u32,897270857#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1430280692<2147483647 ∧ 1685049618<2147483647) ∧ (1182702806<2147483647 ∧ 1132591724<2147483647)) ∧
    ((1702860885<2147483647 ∧ 1973593402<2147483647) ∧ (1660157177<2147483647 ∧ 897270857<2147483647))
  omega
theorem lane0 : (-13276168532707691559 : ZMod 2147483647)=1430280692 := by decide
theorem lane1 : (29679762458362276771 : ZMod 2147483647)=1685049618 := by decide
theorem lane2 : (-1179664140365684375 : ZMod 2147483647)=1182702806 := by decide
theorem lane3 : (21055638259407301511 : ZMod 2147483647)=1132591724 := by decide
theorem lane4 : (-8149062146392708599 : ZMod 2147483647)=1702860885 := by decide
theorem lane5 : (25965614550427491196 : ZMod 2147483647)=1973593402 := by decide
theorem lane6 : (-808610881588591718 : ZMod 2147483647)=1660157177 := by decide
theorem lane7 : (14662411553928941831 : ZMod 2147483647)=897270857 := by decide
theorem step : decode JFw_TX2_P05.value * decode gamma=decode value := by
  change (⟨⟨⟨1554033304,67370206⟩,⟨1410213748,1369248953⟩⟩,⟨⟨1419170319,1866942376⟩,⟨1271796599,2073962627⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩=⟨⟨⟨1430280692,1685049618⟩,⟨1182702806,1132591724⟩⟩,⟨⟨1702860885,1973593402⟩,⟨1660157177,897270857⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^6 := by
  rw [show 6=(5:Nat)+1 from rfl,pow_succ,← JFw_TX2_P05.meaning]
  exact step.symm
theorem source : entry 6=value := identify 6 value canonical meaning
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
end AspisR1.JFw_TX2_P06
end
