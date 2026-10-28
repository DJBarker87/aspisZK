import NDO_JFw_TX2_P16
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P17
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨1003904973#u32,1147694576#u32⟩,⟨1474177753#u32,1511477847#u32⟩⟩,⟨⟨1335902916#u32,995962325#u32⟩,⟨94118806#u32,2068940067#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1003904973<2147483647 ∧ 1147694576<2147483647) ∧ (1474177753<2147483647 ∧ 1511477847<2147483647)) ∧
    ((1335902916<2147483647 ∧ 995962325<2147483647) ∧ (94118806<2147483647 ∧ 2068940067<2147483647))
  omega
theorem lane0 : (-13700373654521945519 : ZMod 2147483647)=1003904973 := by decide
theorem lane1 : (34194301936026733831 : ZMod 2147483647)=1147694576 := by decide
theorem lane2 : (-220793789537648534 : ZMod 2147483647)=1474177753 := by decide
theorem lane3 : (23367453177282794651 : ZMod 2147483647)=1511477847 := by decide
theorem lane4 : (-6483989700815632555 : ZMod 2147483647)=1335902916 := by decide
theorem lane5 : (30871142851240297494 : ZMod 2147483647)=995962325 := by decide
theorem lane6 : (-489662029172087391 : ZMod 2147483647)=94118806 := by decide
theorem lane7 : (17283669251845630439 : ZMod 2147483647)=2068940067 := by decide
theorem step : decode JFw_TX2_P16.value * decode gamma=decode value := by
  change (⟨⟨⟨1385409049,1086671526⟩,⟨1659116453,1624084534⟩⟩,⟨⟨1305878831,1685894190⟩,⟨1921581249,1695663205⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩=⟨⟨⟨1003904973,1147694576⟩,⟨1474177753,1511477847⟩⟩,⟨⟨1335902916,995962325⟩,⟨94118806,2068940067⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^17 := by
  rw [show 17=(16:Nat)+1 from rfl,pow_succ,← JFw_TX2_P16.meaning]
  exact step.symm
theorem source : entry 17=value := identify 17 value canonical meaning
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
end AspisR1.JFw_TX2_P17
end
