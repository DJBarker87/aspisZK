import NDO_JFw_TX2_P19
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P20
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨497936241#u32,185008025#u32⟩,⟨1865917845#u32,2145463598#u32⟩⟩,⟨⟨293456010#u32,1948677857#u32⟩,⟨177052717#u32,1956713516#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((497936241<2147483647 ∧ 185008025<2147483647) ∧ (1865917845<2147483647 ∧ 2145463598<2147483647)) ∧
    ((293456010<2147483647 ∧ 1948677857<2147483647) ∧ (177052717<2147483647 ∧ 1956713516<2147483647))
  omega
theorem lane0 : (-5018880740960816555 : ZMod 2147483647)=497936241 := by decide
theorem lane1 : (25326790117728277690 : ZMod 2147483647)=185008025 := by decide
theorem lane2 : (-3234574912031117548 : ZMod 2147483647)=1865917845 := by decide
theorem lane3 : (22126963827662365806 : ZMod 2147483647)=2145463598 := by decide
theorem lane4 : (-7325207319672880374 : ZMod 2147483647)=293456010 := by decide
theorem lane5 : (19959754782958674027 : ZMod 2147483647)=1948677857 := by decide
theorem lane6 : (3185716184328813617 : ZMod 2147483647)=177052717 := by decide
theorem lane7 : (15686088544617543505 : ZMod 2147483647)=1956713516 := by decide
theorem step : decode JFw_TX2_P19.value * decode gamma=decode value := by
  change (⟨⟨⟨2005758375,2005073905⟩,⟨1602919019,185546252⟩⟩,⟨⟨2023391453,1199631211⟩,⟨239612482,1982757556⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩=⟨⟨⟨497936241,185008025⟩,⟨1865917845,2145463598⟩⟩,⟨⟨293456010,1948677857⟩,⟨177052717,1956713516⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^20 := by
  rw [show 20=(19:Nat)+1 from rfl,pow_succ,← JFw_TX2_P19.meaning]
  exact step.symm
theorem source : entry 20=value := identify 20 value canonical meaning
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
end AspisR1.JFw_TX2_P20
end
