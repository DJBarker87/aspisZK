import NDO_JFw_TX2_P04
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P05
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨847245657#u32,358841845#u32⟩,⟨1504508321#u32,1122660832#u32⟩⟩,⟨⟨1310745621#u32,1588676106#u32⟩,⟨99351805#u32,1666544273#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((847245657<2147483647 ∧ 358841845<2147483647) ∧ (1504508321<2147483647 ∧ 1122660832<2147483647)) ∧
    ((1310745621<2147483647 ∧ 1588676106<2147483647) ∧ (99351805<2147483647 ∧ 1666544273<2147483647))
  omega
theorem lane0 : (-16561507780906940282 : ZMod 2147483647)=847245657 := by decide
theorem lane1 : (23340524802791118502 : ZMod 2147483647)=358841845 := by decide
theorem lane2 : (-9659361814700958099 : ZMod 2147483647)=1504508321 := by decide
theorem lane3 : (14936377933619075245 : ZMod 2147483647)=1122660832 := by decide
theorem lane4 : (-18052619692904810489 : ZMod 2147483647)=1310745621 := by decide
theorem lane5 : (20367706115658482797 : ZMod 2147483647)=1588676106 := by decide
theorem lane6 : (-1464511620837148644 : ZMod 2147483647)=99351805 := by decide
theorem lane7 : (11424767963979028146 : ZMod 2147483647)=1666544273 := by decide
theorem step : decode JFw_TX2_P04.value * decode gamma=decode value := by
  change (⟨⟨⟨46530699,1176229749⟩,⟨1759211712,1927035533⟩⟩,⟨⟨258016984,720994932⟩,⟨1637998205,1813172101⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩=⟨⟨⟨847245657,358841845⟩,⟨1504508321,1122660832⟩⟩,⟨⟨1310745621,1588676106⟩,⟨99351805,1666544273⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^5 := by
  rw [show 5=(4:Nat)+1 from rfl,pow_succ,← JFw_TX2_P04.meaning]
  exact step.symm
theorem source : entry 5=value := identify 5 value canonical meaning
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
end AspisR1.JFw_TX2_P05
end
