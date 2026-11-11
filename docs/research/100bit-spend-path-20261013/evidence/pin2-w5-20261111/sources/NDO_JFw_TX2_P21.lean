import NDO_JFw_TX2_P20
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P21
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨1413143069#u32,1899656567#u32⟩,⟨318649997#u32,1630510080#u32⟩⟩,⟨⟨659265014#u32,1182526578#u32⟩,⟨539833553#u32,779389523#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1413143069<2147483647 ∧ 1899656567<2147483647) ∧ (318649997<2147483647 ∧ 1630510080<2147483647)) ∧
    ((659265014<2147483647 ∧ 1182526578<2147483647) ∧ (539833553<2147483647 ∧ 779389523<2147483647))
  omega
theorem lane0 : (-6472455428631401994 : ZMod 2147483647)=1413143069 := by decide
theorem lane1 : (18382884734502974698 : ZMod 2147483647)=1899656567 := by decide
theorem lane2 : (-2735891526701947840 : ZMod 2147483647)=318649997 := by decide
theorem lane3 : (14592948327061813662 : ZMod 2147483647)=1630510080 := by decide
theorem lane4 : (-6038321541909548834 : ZMod 2147483647)=659265014 := by decide
theorem lane5 : (11741142480653522606 : ZMod 2147483647)=1182526578 := by decide
theorem lane6 : (-240796290678773064 : ZMod 2147483647)=539833553 := by decide
theorem lane7 : (11213205794109123532 : ZMod 2147483647)=779389523 := by decide
theorem step : decode JFw_TX2_P20.value * decode gamma=decode value := by
  change (⟨⟨⟨1705929849,1096894582⟩,⟨69514131,929080030⟩⟩,⟨⟨1509582677,602776328⟩,⟨1155656318,1014406283⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩=⟨⟨⟨1413143069,1899656567⟩,⟨318649997,1630510080⟩⟩,⟨⟨659265014,1182526578⟩,⟨539833553,779389523⟩⟩⟩
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
