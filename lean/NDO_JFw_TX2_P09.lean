import NDO_JFw_TX2_P08
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P09
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨1675652887#u32,779721715#u32⟩,⟨1188803754#u32,1266677922#u32⟩⟩,⟨⟨1114745059#u32,1840161555#u32⟩,⟨1015817431#u32,1256824732#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1675652887<2147483647 ∧ 779721715<2147483647) ∧ (1188803754<2147483647 ∧ 1266677922<2147483647)) ∧
    ((1114745059<2147483647 ∧ 1840161555<2147483647) ∧ (1015817431<2147483647 ∧ 1256824732<2147483647))
  omega
theorem lane0 : (-7124048481364486196 : ZMod 2147483647)=1675652887 := by decide
theorem lane1 : (33141425997428399415 : ZMod 2147483647)=779721715 := by decide
theorem lane2 : (1022725296932572720 : ZMod 2147483647)=1188803754 := by decide
theorem lane3 : (17041451598380870846 : ZMod 2147483647)=1266677922 := by decide
theorem lane4 : (1449633127347873175 : ZMod 2147483647)=1114745059 := by decide
theorem lane5 : (26846511393105687375 : ZMod 2147483647)=1840161555 := by decide
theorem lane6 : (72798889195266159 : ZMod 2147483647)=1015817431 := by decide
theorem lane7 : (16647324414263379172 : ZMod 2147483647)=1256824732 := by decide
theorem step : decode JFw_TX2_P08.value * decode gamma=decode value := by
  change (⟨⟨⟨118514350,1786803209⟩,⟨2062791928,1719480363⟩⟩,⟨⟨1256487405,1353487525⟩,⟨1858113864,49892701⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩=⟨⟨⟨1675652887,779721715⟩,⟨1188803754,1266677922⟩⟩,⟨⟨1114745059,1840161555⟩,⟨1015817431,1256824732⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^9 := by
  rw [show 9=(8:Nat)+1 from rfl,pow_succ,← JFw_TX2_P08.meaning]
  exact step.symm
theorem source : entry 9=value := identify 9 value canonical meaning
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
end AspisR1.JFw_TX2_P09
end
