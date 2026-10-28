import NDO_JFw_TX2_P07
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P08
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨118514350#u32,1786803209#u32⟩,⟨2062791928#u32,1719480363#u32⟩⟩,⟨⟨1256487405#u32,1353487525#u32⟩,⟨1858113864#u32,49892701#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((118514350<2147483647 ∧ 1786803209<2147483647) ∧ (2062791928<2147483647 ∧ 1719480363<2147483647)) ∧
    ((1256487405<2147483647 ∧ 1353487525<2147483647) ∧ (1858113864<2147483647 ∧ 49892701<2147483647))
  omega
theorem lane0 : (-4207433992118992760 : ZMod 2147483647)=118514350 := by decide
theorem lane1 : (9912700985667385850 : ZMod 2147483647)=1786803209 := by decide
theorem lane2 : (566191553869819017 : ZMod 2147483647)=2062791928 := by decide
theorem lane3 : (12046563139532174710 : ZMod 2147483647)=1719480363 := by decide
theorem lane4 : (-5457211470001714235 : ZMod 2147483647)=1256487405 := by decide
theorem lane5 : (11610346682179132173 : ZMod 2147483647)=1353487525 := by decide
theorem lane6 : (2169653164075663659 : ZMod 2147483647)=1858113864 := by decide
theorem lane7 : (5609575103202779056 : ZMod 2147483647)=49892701 := by decide
theorem step : decode JFw_TX2_P07.value * decode gamma=decode value := by
  change (⟨⟨⟨1491718280,385547620⟩,⟨321711020,92744917⟩⟩,⟨⟨710076517,47019780⟩,⟨564707688,1582958967⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩=⟨⟨⟨118514350,1786803209⟩,⟨2062791928,1719480363⟩⟩,⟨⟨1256487405,1353487525⟩,⟨1858113864,49892701⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^8 := by
  rw [show 8=(7:Nat)+1 from rfl,pow_succ,← JFw_TX2_P07.meaning]
  exact step.symm
theorem source : entry 8=value := identify 8 value canonical meaning
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
end AspisR1.JFw_TX2_P08
end
