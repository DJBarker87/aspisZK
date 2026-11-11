import NDO_JFw_TX2_P21
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P22
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨1412738318#u32,1124254223#u32⟩,⟨748787032#u32,1932125153#u32⟩⟩,⟨⟨178117781#u32,1159531233#u32⟩,⟨1869641102#u32,57480830#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1412738318<2147483647 ∧ 1124254223<2147483647) ∧ (748787032<2147483647 ∧ 1932125153<2147483647)) ∧
    ((178117781<2147483647 ∧ 1159531233<2147483647) ∧ (1869641102<2147483647 ∧ 57480830<2147483647))
  omega
theorem lane0 : (-14399402297293630140 : ZMod 2147483647)=1412738318 := by decide
theorem lane1 : (12439808390165469800 : ZMod 2147483647)=1124254223 := by decide
theorem lane2 : (-6390733291296491139 : ZMod 2147483647)=748787032 := by decide
theorem lane3 : (12263436510380486351 : ZMod 2147483647)=1932125153 := by decide
theorem lane4 : (-10915681178776866563 : ZMod 2147483647)=178117781 := by decide
theorem lane5 : (12305245228781208625 : ZMod 2147483647)=1159531233 := by decide
theorem lane6 : (-4643089273370732608 : ZMod 2147483647)=1869641102 := by decide
theorem lane7 : (12015757517166214882 : ZMod 2147483647)=57480830 := by decide
theorem step : decode JFw_TX2_P21.value * decode gamma=decode value := by
  change (⟨⟨⟨1413143069,1899656567⟩,⟨318649997,1630510080⟩⟩,⟨⟨659265014,1182526578⟩,⟨539833553,779389523⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩=⟨⟨⟨1412738318,1124254223⟩,⟨748787032,1932125153⟩⟩,⟨⟨178117781,1159531233⟩,⟨1869641102,57480830⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^22 := by
  rw [show 22=(21:Nat)+1 from rfl,pow_succ,← JFw_TX2_P21.meaning]
  exact step.symm
theorem source : entry 22=value := identify 22 value canonical meaning
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
end AspisR1.JFw_TX2_P22
end
