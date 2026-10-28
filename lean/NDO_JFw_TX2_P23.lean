import NDO_JFw_TX2_P22
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P23
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨1858903615#u32,1018329259#u32⟩,⟨1550509101#u32,1843639311#u32⟩⟩,⟨⟨1749638204#u32,702011012#u32⟩,⟨1014161165#u32,1343575777#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1858903615<2147483647 ∧ 1018329259<2147483647) ∧ (1550509101<2147483647 ∧ 1843639311<2147483647)) ∧
    ((1749638204<2147483647 ∧ 702011012<2147483647) ∧ (1014161165<2147483647 ∧ 1343575777<2147483647))
  omega
theorem lane0 : (-7038907852011138803 : ZMod 2147483647)=1858903615 := by decide
theorem lane1 : (34587090174688520733 : ZMod 2147483647)=1018329259 := by decide
theorem lane2 : (3465994449102275840 : ZMod 2147483647)=1550509101 := by decide
theorem lane3 : (20274023505465186847 : ZMod 2147483647)=1843639311 := by decide
theorem lane4 : (893718954021427950 : ZMod 2147483647)=1749638204 := by decide
theorem lane5 : (29421083389079746449 : ZMod 2147483647)=702011012 := by decide
theorem lane6 : (2176888089325545135 : ZMod 2147483647)=1014161165 := by decide
theorem lane7 : (16755260223803362833 : ZMod 2147483647)=1343575777 := by decide
theorem step : decode JFw_TX2_P22.value * decode gamma=decode value := by
  change (⟨⟨⟨1478307182,1255280192⟩,⟨1837870964,1625323762⟩⟩,⟨⟨1423042536,1466877680⟩,⟨1923715623,522298462⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩=⟨⟨⟨1858903615,1018329259⟩,⟨1550509101,1843639311⟩⟩,⟨⟨1749638204,702011012⟩,⟨1014161165,1343575777⟩⟩⟩
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
