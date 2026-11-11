import NDO_JFw_TX2_P13
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P14
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨629381172#u32,26948775#u32⟩,⟨1813584096#u32,1883992904#u32⟩⟩,⟨⟨635633555#u32,1959546889#u32⟩,⟨749931315#u32,118355649#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((629381172<2147483647 ∧ 26948775<2147483647) ∧ (1813584096<2147483647 ∧ 1883992904<2147483647)) ∧
    ((635633555<2147483647 ∧ 1959546889<2147483647) ∧ (749931315<2147483647 ∧ 118355649<2147483647))
  omega
theorem lane0 : (-12104721609286430578 : ZMod 2147483647)=629381172 := by decide
theorem lane1 : (14659606898613448456 : ZMod 2147483647)=26948775 := by decide
theorem lane2 : (-5529827282495675875 : ZMod 2147483647)=1813584096 := by decide
theorem lane3 : (13397953733802672999 : ZMod 2147483647)=1883992904 := by decide
theorem lane4 : (-8236956404716267520 : ZMod 2147483647)=635633555 := by decide
theorem lane5 : (14535132984519818022 : ZMod 2147483647)=1959546889 := by decide
theorem lane6 : (-4884325200708746499 : ZMod 2147483647)=749931315 := by decide
theorem lane7 : (9947361204705277471 : ZMod 2147483647)=118355649 := by decide
theorem step : decode JFw_TX2_P13.value * decode gamma=decode value := by
  change (⟨⟨⟨638162575,2016473025⟩,⟨565373723,982732691⟩⟩,⟨⟨624784875,1681603673⟩,⟨957645249,459094604⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩=⟨⟨⟨629381172,26948775⟩,⟨1813584096,1883992904⟩⟩,⟨⟨635633555,1959546889⟩,⟨749931315,118355649⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^14 := by
  rw [show 14=(13:Nat)+1 from rfl,pow_succ,← JFw_TX2_P13.meaning]
  exact step.symm
theorem source : entry 14=value := identify 14 value canonical meaning
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
end AspisR1.JFw_TX2_P14
end
