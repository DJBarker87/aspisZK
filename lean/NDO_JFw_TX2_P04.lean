import NDO_JFw_TX2_P03
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P04
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨1106523000#u32,729079828#u32⟩,⟨1074182998#u32,246996287#u32⟩⟩,⟨⟨634588140#u32,1559245386#u32⟩,⟨1947503436#u32,547797802#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1106523000<2147483647 ∧ 729079828<2147483647) ∧ (1074182998<2147483647 ∧ 246996287<2147483647)) ∧
    ((634588140<2147483647 ∧ 1559245386<2147483647) ∧ (1947503436<2147483647 ∧ 547797802<2147483647))
  omega
theorem lane0 : (-16218710225264504442 : ZMod 2147483647)=1106523000 := by decide
theorem lane1 : (23920701904496496837 : ZMod 2147483647)=729079828 := by decide
theorem lane2 : (-3586923464003069155 : ZMod 2147483647)=1074182998 := by decide
theorem lane3 : (15241252039317078343 : ZMod 2147483647)=246996287 := by decide
theorem lane4 : (-8947161690963151811 : ZMod 2147483647)=634588140 := by decide
theorem lane5 : (22109565238838184291 : ZMod 2147483647)=1559245386 := by decide
theorem lane6 : (-4276802153084285670 : ZMod 2147483647)=1947503436 := by decide
theorem lane7 : (11672743925418485157 : ZMod 2147483647)=547797802 := by decide
theorem step : decode JFw_TX2_P03.value * decode gamma=decode value := by
  change (⟨⟨⟨352063,39062738⟩,⟨1313565596,1840648083⟩⟩,⟨⟨752376469,1317611639⟩,⟨1258713036,1674326661⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩=⟨⟨⟨1106523000,729079828⟩,⟨1074182998,246996287⟩⟩,⟨⟨634588140,1559245386⟩,⟨1947503436,547797802⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^4 := by
  rw [show 4=(3:Nat)+1 from rfl,pow_succ,← JFw_TX2_P03.meaning]
  exact step.symm
theorem source : entry 4=value := identify 4 value canonical meaning
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
end AspisR1.JFw_TX2_P04
end
