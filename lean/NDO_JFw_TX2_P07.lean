import NDO_JFw_TX2_P06
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P07
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨1491718280#u32,385547620#u32⟩,⟨321711020#u32,92744917#u32⟩⟩,⟨⟨710076517#u32,47019780#u32⟩,⟨564707688#u32,1582958967#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1491718280<2147483647 ∧ 385547620<2147483647) ∧ (321711020<2147483647 ∧ 92744917<2147483647)) ∧
    ((710076517<2147483647 ∧ 47019780<2147483647) ∧ (564707688<2147483647 ∧ 1582958967<2147483647))
  omega
theorem lane0 : (-8556630757275577032 : ZMod 2147483647)=1491718280 := by decide
theorem lane1 : (31576644404659449803 : ZMod 2147483647)=385547620 := by decide
theorem lane2 : (288289200211263660 : ZMod 2147483647)=321711020 := by decide
theorem lane3 : (21191055819778271956 : ZMod 2147483647)=92744917 := by decide
theorem lane4 : (-3873120942170106278 : ZMod 2147483647)=710076517 := by decide
theorem lane5 : (26556926550114248450 : ZMod 2147483647)=47019780 := by decide
theorem lane6 : (877488956479754827 : ZMod 2147483647)=564707688 := by decide
theorem lane7 : (17209792328536890258 : ZMod 2147483647)=1582958967 := by decide
theorem step : decode JFw_TX2_P06.value * decode gamma=decode value := by
  change (⟨⟨⟨1430280692,1685049618⟩,⟨1182702806,1132591724⟩⟩,⟨⟨1702860885,1973593402⟩,⟨1660157177,897270857⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩=⟨⟨⟨1491718280,385547620⟩,⟨321711020,92744917⟩⟩,⟨⟨710076517,47019780⟩,⟨564707688,1582958967⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^7 := by
  rw [show 7=(6:Nat)+1 from rfl,pow_succ,← JFw_TX2_P06.meaning]
  exact step.symm
theorem source : entry 7=value := identify 7 value canonical meaning
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
end AspisR1.JFw_TX2_P07
end
