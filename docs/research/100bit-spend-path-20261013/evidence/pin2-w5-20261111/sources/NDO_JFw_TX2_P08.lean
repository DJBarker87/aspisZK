import NDO_JFw_TX2_P07
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P08
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨803384121#u32,1332142427#u32⟩,⟨387819137#u32,1488822400#u32⟩⟩,⟨⟨1775426482#u32,1276020657#u32⟩,⟨1492984079#u32,1978943953#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((803384121<2147483647 ∧ 1332142427<2147483647) ∧ (387819137<2147483647 ∧ 1488822400<2147483647)) ∧
    ((1775426482<2147483647 ∧ 1276020657<2147483647) ∧ (1492984079<2147483647 ∧ 1978943953<2147483647))
  omega
theorem lane0 : (-8993809590420011117 : ZMod 2147483647)=803384121 := by decide
theorem lane1 : (21201578621884471933 : ZMod 2147483647)=1332142427 := by decide
theorem lane2 : (-5194925877731929694 : ZMod 2147483647)=387819137 := by decide
theorem lane3 : (11687887716897665174 : ZMod 2147483647)=1488822400 := by decide
theorem lane4 : (-7909630658268616177 : ZMod 2147483647)=1775426482 := by decide
theorem lane5 : (19482421600518641979 : ZMod 2147483647)=1276020657 := by decide
theorem lane6 : (1818490002028624644 : ZMod 2147483647)=1492984079 := by decide
theorem lane7 : (10969937116904698480 : ZMod 2147483647)=1978943953 := by decide
theorem step : decode JFw_TX2_P07.value * decode gamma=decode value := by
  change (⟨⟨⟨995644922,1350557097⟩,⟨2039696097,901577836⟩⟩,⟨⟨506310784,419635324⟩,⟨923539768,1229247375⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩=⟨⟨⟨803384121,1332142427⟩,⟨387819137,1488822400⟩⟩,⟨⟨1775426482,1276020657⟩,⟨1492984079,1978943953⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^8 := by
  rw [show 8=(7:Nat)+1 from rfl,pow_succ,← JFw_TX2_P07.meaning]
  exact step.symm
theorem source : entry 8=value := identify 8 value canonical meaning
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
end AspisR1.JFw_TX2_P08
end
