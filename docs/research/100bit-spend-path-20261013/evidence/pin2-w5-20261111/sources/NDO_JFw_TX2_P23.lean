import NDO_JFw_TX2_P22
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P23
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨1204116711#u32,507096257#u32⟩,⟨1354323135#u32,741379903#u32⟩⟩,⟨⟨450640961#u32,1221504423#u32⟩,⟨769193840#u32,1560859272#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1204116711<2147483647 ∧ 507096257<2147483647) ∧ (1354323135<2147483647 ∧ 741379903<2147483647)) ∧
    ((450640961<2147483647 ∧ 1221504423<2147483647) ∧ (769193840<2147483647 ∧ 1560859272<2147483647))
  omega
theorem lane0 : (-8337438093851333515 : ZMod 2147483647)=1204116711 := by decide
theorem lane1 : (15469820994848947271 : ZMod 2147483647)=507096257 := by decide
theorem lane2 : (-1152042773882136999 : ZMod 2147483647)=1354323135 := by decide
theorem lane3 : (17496508463601181629 : ZMod 2147483647)=741379903 := by decide
theorem lane4 : (-8551695493003497537 : ZMod 2147483647)=450640961 := by decide
theorem lane5 : (18706953650530797357 : ZMod 2147483647)=1221504423 := by decide
theorem lane6 : (-1575082731357824451 : ZMod 2147483647)=769193840 := by decide
theorem lane7 : (11345109561953810547 : ZMod 2147483647)=1560859272 := by decide
theorem step : decode JFw_TX2_P22.value * decode gamma=decode value := by
  change (⟨⟨⟨1412738318,1124254223⟩,⟨748787032,1932125153⟩⟩,⟨⟨178117781,1159531233⟩,⟨1869641102,57480830⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩=⟨⟨⟨1204116711,507096257⟩,⟨1354323135,741379903⟩⟩,⟨⟨450640961,1221504423⟩,⟨769193840,1560859272⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^23 := by
  rw [show 23=(22:Nat)+1 from rfl,pow_succ,← JFw_TX2_P22.meaning]
  exact step.symm
theorem source : entry 23=value := identify 23 value canonical meaning
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
end AspisR1.JFw_TX2_P23
end
