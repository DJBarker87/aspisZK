import NDO_JFw_TX2_P05
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P06
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨1950868962#u32,2061174938#u32⟩,⟨258644308#u32,915368944#u32⟩⟩,⟨⟨2094690493#u32,11221900#u32⟩,⟨2080583196#u32,694755488#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1950868962<2147483647 ∧ 2061174938<2147483647) ∧ (258644308<2147483647 ∧ 915368944<2147483647)) ∧
    ((2094690493<2147483647 ∧ 11221900<2147483647) ∧ (2080583196<2147483647 ∧ 694755488<2147483647))
  omega
theorem lane0 : (-19258636228415668959 : ZMod 2147483647)=1950868962 := by decide
theorem lane1 : (20139012550973111849 : ZMod 2147483647)=2061174938 := by decide
theorem lane2 : (-6787439689653665227 : ZMod 2147483647)=258644308 := by decide
theorem lane3 : (10359116904627009549 : ZMod 2147483647)=915368944 := by decide
theorem lane4 : (-10014230220454898840 : ZMod 2147483647)=2094690493 := by decide
theorem lane5 : (12376891861986713700 : ZMod 2147483647)=11221900 := by decide
theorem lane6 : (-321143047613249046 : ZMod 2147483647)=2080583196 := by decide
theorem lane7 : (11508157869019021158 : ZMod 2147483647)=694755488 := by decide
theorem step : decode JFw_TX2_P05.value * decode gamma=decode value := by
  change (⟨⟨⟨847245657,358841845⟩,⟨1504508321,1122660832⟩⟩,⟨⟨1310745621,1588676106⟩,⟨99351805,1666544273⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩=⟨⟨⟨1950868962,2061174938⟩,⟨258644308,915368944⟩⟩,⟨⟨2094690493,11221900⟩,⟨2080583196,694755488⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^6 := by
  rw [show 6=(5:Nat)+1 from rfl,pow_succ,← JFw_TX2_P05.meaning]
  exact step.symm
theorem source : entry 6=value := identify 6 value canonical meaning
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
end AspisR1.JFw_TX2_P06
end
