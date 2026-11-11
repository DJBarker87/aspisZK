import NDO_JFw_TX2_P12
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P13
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨638162575#u32,2016473025#u32⟩,⟨565373723#u32,982732691#u32⟩⟩,⟨⟨624784875#u32,1681603673#u32⟩,⟨957645249#u32,459094604#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((638162575<2147483647 ∧ 2016473025<2147483647) ∧ (565373723<2147483647 ∧ 982732691<2147483647)) ∧
    ((624784875<2147483647 ∧ 1681603673<2147483647) ∧ (957645249<2147483647 ∧ 459094604<2147483647))
  omega
theorem lane0 : (-5632819119764984613 : ZMod 2147483647)=638162575 := by decide
theorem lane1 : (18667613627813433437 : ZMod 2147483647)=2016473025 := by decide
theorem lane2 : (-624822197016687600 : ZMod 2147483647)=565373723 := by decide
theorem lane3 : (8616859255764998116 : ZMod 2147483647)=982732691 := by decide
theorem lane4 : (-6470482892675546690 : ZMod 2147483647)=624784875 := by decide
theorem lane5 : (12792765216646048760 : ZMod 2147483647)=1681603673 := by decide
theorem lane6 : (457213120673468399 : ZMod 2147483647)=957645249 := by decide
theorem lane7 : (9213362996139808929 : ZMod 2147483647)=459094604 := by decide
theorem step : decode JFw_TX2_P12.value * decode gamma=decode value := by
  change (⟨⟨⟨165022405,1151288564⟩,⟨1187929565,975586913⟩⟩,⟨⟨1580123087,208006299⟩,⟨605264612,565298516⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩=⟨⟨⟨638162575,2016473025⟩,⟨565373723,982732691⟩⟩,⟨⟨624784875,1681603673⟩,⟨957645249,459094604⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^13 := by
  rw [show 13=(12:Nat)+1 from rfl,pow_succ,← JFw_TX2_P12.meaning]
  exact step.symm
theorem source : entry 13=value := identify 13 value canonical meaning
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
end AspisR1.JFw_TX2_P13
end
