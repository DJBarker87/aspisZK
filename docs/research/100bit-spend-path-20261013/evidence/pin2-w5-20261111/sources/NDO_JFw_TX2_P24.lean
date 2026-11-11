import NDO_JFw_TX2_P23
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P24
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨391568943#u32,1006575155#u32⟩,⟨990907796#u32,1343747376#u32⟩⟩,⟨⟨1263573490#u32,408284389#u32⟩,⟨792956610#u32,952882229#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((391568943<2147483647 ∧ 1006575155<2147483647) ∧ (990907796<2147483647 ∧ 1343747376<2147483647)) ∧
    ((1263573490<2147483647 ∧ 408284389<2147483647) ∧ (792956610<2147483647 ∧ 952882229<2147483647))
  omega
theorem lane0 : (-13701655795213337370 : ZMod 2147483647)=391568943 := by decide
theorem lane1 : (18182856639165638306 : ZMod 2147483647)=1006575155 := by decide
theorem lane2 : (-7013717710786034744 : ZMod 2147483647)=990907796 := by decide
theorem lane3 : (12045438469758253118 : ZMod 2147483647)=1343747376 := by decide
theorem lane4 : (-7890642129484841888 : ZMod 2147483647)=1263573490 := by decide
theorem lane5 : (14350313036999872904 : ZMod 2147483647)=408284389 := by decide
theorem lane6 : (650923979488524016 : ZMod 2147483647)=792956610 := by decide
theorem lane7 : (9745841754569667922 : ZMod 2147483647)=952882229 := by decide
theorem step : decode JFw_TX2_P23.value * decode gamma=decode value := by
  change (⟨⟨⟨1204116711,507096257⟩,⟨1354323135,741379903⟩⟩,⟨⟨450640961,1221504423⟩,⟨769193840,1560859272⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩=⟨⟨⟨391568943,1006575155⟩,⟨990907796,1343747376⟩⟩,⟨⟨1263573490,408284389⟩,⟨792956610,952882229⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^24 := by
  rw [show 24=(23:Nat)+1 from rfl,pow_succ,← JFw_TX2_P23.meaning]
  exact step.symm
theorem source : entry 24=value := identify 24 value canonical meaning
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
end AspisR1.JFw_TX2_P24
end
