import NDO_JFw_TX2_P09
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P10
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨1364884909#u32,594709522#u32⟩,⟨2038502201#u32,377386917#u32⟩⟩,⟨⟨1137838899#u32,2003659556#u32⟩,⟨1264608004#u32,1435903714#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1364884909<2147483647 ∧ 594709522<2147483647) ∧ (2038502201<2147483647 ∧ 377386917<2147483647)) ∧
    ((1137838899<2147483647 ∧ 2003659556<2147483647) ∧ (1264608004<2147483647 ∧ 1435903714<2147483647))
  omega
theorem lane0 : (-11270215577212669850 : ZMod 2147483647)=1364884909 := by decide
theorem lane1 : (26573954395175599768 : ZMod 2147483647)=594709522 := by decide
theorem lane2 : (-1241593665911578381 : ZMod 2147483647)=2038502201 := by decide
theorem lane3 : (18291945019642896760 : ZMod 2147483647)=377386917 := by decide
theorem lane4 : (-5885589719170044790 : ZMod 2147483647)=1137838899 := by decide
theorem lane5 : (22550727314601467161 : ZMod 2147483647)=2003659556 := by decide
theorem lane6 : (-480795420210453301 : ZMod 2147483647)=1264608004 := by decide
theorem lane7 : (13818574874186827163 : ZMod 2147483647)=1435903714 := by decide
theorem step : decode JFw_TX2_P09.value * decode gamma=decode value := by
  change (⟨⟨⟨1675652887,779721715⟩,⟨1188803754,1266677922⟩⟩,⟨⟨1114745059,1840161555⟩,⟨1015817431,1256824732⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩=⟨⟨⟨1364884909,594709522⟩,⟨2038502201,377386917⟩⟩,⟨⟨1137838899,2003659556⟩,⟨1264608004,1435903714⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^10 := by
  rw [show 10=(9:Nat)+1 from rfl,pow_succ,← JFw_TX2_P09.meaning]
  exact step.symm
theorem source : entry 10=value := identify 10 value canonical meaning
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
end AspisR1.JFw_TX2_P10
end
