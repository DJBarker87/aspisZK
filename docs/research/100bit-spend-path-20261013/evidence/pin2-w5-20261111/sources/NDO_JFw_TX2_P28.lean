import NDO_JFw_TX2_P27
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P28
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨712327709#u32,1775336892#u32⟩,⟨1587425776#u32,1405355058#u32⟩⟩,⟨⟨1036928861#u32,56026765#u32⟩,⟨518602670#u32,1725995968#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((712327709<2147483647 ∧ 1775336892<2147483647) ∧ (1587425776<2147483647 ∧ 1405355058<2147483647)) ∧
    ((1036928861<2147483647 ∧ 56026765<2147483647) ∧ (518602670<2147483647 ∧ 1725995968<2147483647))
  omega
theorem lane0 : (-16565646314889592515 : ZMod 2147483647)=712327709 := by decide
theorem lane1 : (22942193319565551405 : ZMod 2147483647)=1775336892 := by decide
theorem lane2 : (-6109499864986366602 : ZMod 2147483647)=1587425776 := by decide
theorem lane3 : (13185533406253623972 : ZMod 2147483647)=1405355058 := by decide
theorem lane4 : (-9707751366981582786 : ZMod 2147483647)=1036928861 := by decide
theorem lane5 : (15431399507623425626 : ZMod 2147483647)=56026765 := by decide
theorem lane6 : (-2550867131500183561 : ZMod 2147483647)=518602670 := by decide
theorem lane7 : (12323646804117935307 : ZMod 2147483647)=1725995968 := by decide
theorem step : decode JFw_TX2_P27.value * decode gamma=decode value := by
  change (⟨⟨⟨476910301,1477068078⟩,⟨1284387695,977602599⟩⟩,⟨⟨1686214252,1757260182⟩,⟨556660887,1234719231⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩=⟨⟨⟨712327709,1775336892⟩,⟨1587425776,1405355058⟩⟩,⟨⟨1036928861,56026765⟩,⟨518602670,1725995968⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^28 := by
  rw [show 28=(27:Nat)+1 from rfl,pow_succ,← JFw_TX2_P27.meaning]
  exact step.symm
theorem source : entry 28=value := identify 28 value canonical meaning
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
end AspisR1.JFw_TX2_P28
end
