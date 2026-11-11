import NDO_JFw_TX2_P19
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P20
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨1705929849#u32,1096894582#u32⟩,⟨69514131#u32,929080030#u32⟩⟩,⟨⟨1509582677#u32,602776328#u32⟩,⟨1155656318#u32,1014406283#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1705929849<2147483647 ∧ 1096894582<2147483647) ∧ (69514131<2147483647 ∧ 929080030<2147483647)) ∧
    ((1509582677<2147483647 ∧ 602776328<2147483647) ∧ (1155656318<2147483647 ∧ 1014406283<2147483647))
  omega
theorem lane0 : (1293688019454670765 : ZMod 2147483647)=1705929849 := by decide
theorem lane1 : (23942251306261502725 : ZMod 2147483647)=1096894582 := by decide
theorem lane2 : (4324064241492451465 : ZMod 2147483647)=69514131 := by decide
theorem lane3 : (15472711445982767281 : ZMod 2147483647)=929080030 := by decide
theorem lane4 : (1920209490585484958 : ZMod 2147483647)=1509582677 := by decide
theorem lane5 : (20645791410721945398 : ZMod 2147483647)=602776328 := by decide
theorem lane6 : (5357981308262492996 : ZMod 2147483647)=1155656318 := by decide
theorem lane7 : (11215338043742148474 : ZMod 2147483647)=1014406283 := by decide
theorem step : decode JFw_TX2_P19.value * decode gamma=decode value := by
  change (⟨⟨⟨1716214232,778082931⟩,⟨1737360950,470464536⟩⟩,⟨⟨1420768076,505932394⟩,⟨1510834162,87008139⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩=⟨⟨⟨1705929849,1096894582⟩,⟨69514131,929080030⟩⟩,⟨⟨1509582677,602776328⟩,⟨1155656318,1014406283⟩⟩⟩
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
