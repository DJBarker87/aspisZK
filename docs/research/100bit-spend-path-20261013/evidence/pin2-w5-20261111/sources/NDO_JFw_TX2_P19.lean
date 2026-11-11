import NDO_JFw_TX2_P18
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P19
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨1716214232#u32,778082931#u32⟩,⟨1737360950#u32,470464536#u32⟩⟩,⟨⟨1420768076#u32,505932394#u32⟩,⟨1510834162#u32,87008139#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1716214232<2147483647 ∧ 778082931<2147483647) ∧ (1737360950<2147483647 ∧ 470464536<2147483647)) ∧
    ((1420768076<2147483647 ∧ 505932394<2147483647) ∧ (1510834162<2147483647 ∧ 87008139<2147483647))
  omega
theorem lane0 : (-17168520717494319329 : ZMod 2147483647)=1716214232 := by decide
theorem lane1 : (23770935331999314675 : ZMod 2147483647)=778082931 := by decide
theorem lane2 : (-7316699267192435544 : ZMod 2147483647)=1737360950 := by decide
theorem lane3 : (13450007191951682438 : ZMod 2147483647)=470464536 := by decide
theorem lane4 : (-10098634357897277390 : ZMod 2147483647)=1420768076 := by decide
theorem lane5 : (16710236566154021672 : ZMod 2147483647)=505932394 := by decide
theorem lane6 : (176849628495669337 : ZMod 2147483647)=1510834162 := by decide
theorem lane7 : (16027054805681213611 : ZMod 2147483647)=87008139 := by decide
theorem step : decode JFw_TX2_P18.value * decode gamma=decode value := by
  change (⟨⟨⟨2090762636,1506327751⟩,⟨1519455049,1311763271⟩⟩,⟨⟨1622623315,1039659929⟩,⟨182058433,1841500245⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩=⟨⟨⟨1716214232,778082931⟩,⟨1737360950,470464536⟩⟩,⟨⟨1420768076,505932394⟩,⟨1510834162,87008139⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^19 := by
  rw [show 19=(18:Nat)+1 from rfl,pow_succ,← JFw_TX2_P18.meaning]
  exact step.symm
theorem source : entry 19=value := identify 19 value canonical meaning
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
end AspisR1.JFw_TX2_P19
end
