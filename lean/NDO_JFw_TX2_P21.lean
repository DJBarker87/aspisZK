import NDO_JFw_TX2_P20
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P21
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨235809508#u32,1485990146#u32⟩,⟨1085624123#u32,82870699#u32⟩⟩,⟨⟨1751078325#u32,1425322328#u32⟩,⟨826458039#u32,863066484#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((235809508<2147483647 ∧ 1485990146<2147483647) ∧ (1085624123<2147483647 ∧ 82870699<2147483647)) ∧
    ((1751078325<2147483647 ∧ 1425322328<2147483647) ∧ (826458039<2147483647 ∧ 863066484<2147483647))
  omega
theorem lane0 : (-21616596125910216140 : ZMod 2147483647)=235809508 := by decide
theorem lane1 : (24328500668190032914 : ZMod 2147483647)=1485990146 := by decide
theorem lane2 : (-8817086155734484601 : ZMod 2147483647)=1085624123 := by decide
theorem lane3 : (15421644704917692762 : ZMod 2147483647)=82870699 := by decide
theorem lane4 : (-12687692817652854653 : ZMod 2147483647)=1751078325 := by decide
theorem lane5 : (19991609075238683715 : ZMod 2147483647)=1425322328 := by decide
theorem lane6 : (-6739165478619486639 : ZMod 2147483647)=826458039 := by decide
theorem lane7 : (12467701176674353438 : ZMod 2147483647)=863066484 := by decide
theorem step : decode JFw_TX2_P20.value * decode gamma=decode value := by
  change (⟨⟨⟨497936241,185008025⟩,⟨1865917845,2145463598⟩⟩,⟨⟨293456010,1948677857⟩,⟨177052717,1956713516⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩=⟨⟨⟨235809508,1485990146⟩,⟨1085624123,82870699⟩⟩,⟨⟨1751078325,1425322328⟩,⟨826458039,863066484⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^21 := by
  rw [show 21=(20:Nat)+1 from rfl,pow_succ,← JFw_TX2_P20.meaning]
  exact step.symm
theorem source : entry 21=value := identify 21 value canonical meaning
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
end AspisR1.JFw_TX2_P21
end
