import NDO_JFw_TX2_P14
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P15
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨2002812837#u32,1496182417#u32⟩,⟨1984673415#u32,1484932522#u32⟩⟩,⟨⟨1919977198#u32,1583134462#u32⟩,⟨1393716461#u32,820218084#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((2002812837<2147483647 ∧ 1496182417<2147483647) ∧ (1984673415<2147483647 ∧ 1484932522<2147483647)) ∧
    ((1919977198<2147483647 ∧ 1583134462<2147483647) ∧ (1393716461<2147483647 ∧ 820218084<2147483647))
  omega
theorem lane0 : (-15682832760028153275 : ZMod 2147483647)=2002812837 := by decide
theorem lane1 : (16496534581031141621 : ZMod 2147483647)=1496182417 := by decide
theorem lane2 : (-159034366952621988 : ZMod 2147483647)=1984673415 := by decide
theorem lane3 : (12448022496148570276 : ZMod 2147483647)=1484932522 := by decide
theorem lane4 : (-7730468212726247756 : ZMod 2147483647)=1919977198 := by decide
theorem lane5 : (16618471558748004176 : ZMod 2147483647)=1583134462 := by decide
theorem lane6 : (-284437652215203327 : ZMod 2147483647)=1393716461 := by decide
theorem lane7 : (10780502369153807695 : ZMod 2147483647)=820218084 := by decide
theorem step : decode JFw_TX2_P14.value * decode gamma=decode value := by
  change (⟨⟨⟨629381172,26948775⟩,⟨1813584096,1883992904⟩⟩,⟨⟨635633555,1959546889⟩,⟨749931315,118355649⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩=⟨⟨⟨2002812837,1496182417⟩,⟨1984673415,1484932522⟩⟩,⟨⟨1919977198,1583134462⟩,⟨1393716461,820218084⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^15 := by
  rw [show 15=(14:Nat)+1 from rfl,pow_succ,← JFw_TX2_P14.meaning]
  exact step.symm
theorem source : entry 15=value := identify 15 value canonical meaning
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
end AspisR1.JFw_TX2_P15
end
