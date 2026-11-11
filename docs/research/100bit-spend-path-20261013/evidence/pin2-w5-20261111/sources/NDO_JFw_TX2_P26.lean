import NDO_JFw_TX2_P25
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P26
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨1081127453#u32,1223560779#u32⟩,⟨492705188#u32,302580972#u32⟩⟩,⟨⟨1322442357#u32,534886635#u32⟩,⟨1640616452#u32,536904083#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1081127453<2147483647 ∧ 1223560779<2147483647) ∧ (492705188<2147483647 ∧ 302580972<2147483647)) ∧
    ((1322442357<2147483647 ∧ 534886635<2147483647) ∧ (1640616452<2147483647 ∧ 536904083<2147483647))
  omega
theorem lane0 : (-9840337411030089830 : ZMod 2147483647)=1081127453 := by decide
theorem lane1 : (22519076802183717938 : ZMod 2147483647)=1223560779 := by decide
theorem lane2 : (-574162482331008739 : ZMod 2147483647)=492705188 := by decide
theorem lane3 : (12544456787880528625 : ZMod 2147483647)=302580972 := by decide
theorem lane4 : (-11043983857285392364 : ZMod 2147483647)=1322442357 := by decide
theorem lane5 : (17995084357977175332 : ZMod 2147483647)=534886635 := by decide
theorem lane6 : (2449519889934511947 : ZMod 2147483647)=1640616452 := by decide
theorem lane7 : (12926873007308508299 : ZMod 2147483647)=536904083 := by decide
theorem step : decode JFw_TX2_P25.value * decode gamma=decode value := by
  change (⟨⟨⟨875085308,526331536⟩,⟨1793465312,2138906138⟩⟩,⟨⟨1321124323,119982949⟩,⟨1044440065,867672856⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩=⟨⟨⟨1081127453,1223560779⟩,⟨492705188,302580972⟩⟩,⟨⟨1322442357,534886635⟩,⟨1640616452,536904083⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^26 := by
  rw [show 26=(25:Nat)+1 from rfl,pow_succ,← JFw_TX2_P25.meaning]
  exact step.symm
theorem source : entry 26=value := identify 26 value canonical meaning
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
end AspisR1.JFw_TX2_P26
end
