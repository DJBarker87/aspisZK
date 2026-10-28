import NDO_JFw_TX2_P15
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P16
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨1385409049#u32,1086671526#u32⟩,⟨1659116453#u32,1624084534#u32⟩⟩,⟨⟨1305878831#u32,1685894190#u32⟩,⟨1921581249#u32,1695663205#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1385409049<2147483647 ∧ 1086671526<2147483647) ∧ (1659116453<2147483647 ∧ 1624084534<2147483647)) ∧
    ((1305878831<2147483647 ∧ 1685894190<2147483647) ∧ (1921581249<2147483647 ∧ 1695663205<2147483647))
  omega
theorem lane0 : (-3367847294525396827 : ZMod 2147483647)=1385409049 := by decide
theorem lane1 : (20955254288753705250 : ZMod 2147483647)=1086671526 := by decide
theorem lane2 : (427934413083603836 : ZMod 2147483647)=1659116453 := by decide
theorem lane3 : (18606024494357270221 : ZMod 2147483647)=1624084534 := by decide
theorem lane4 : (-3735300083969488778 : ZMod 2147483647)=1305878831 := by decide
theorem lane5 : (19980800981429949160 : ZMod 2147483647)=1685894190 := by decide
theorem lane6 : (4258096118394087689 : ZMod 2147483647)=1921581249 := by decide
theorem lane7 : (12650620540318495661 : ZMod 2147483647)=1695663205 := by decide
theorem step : decode JFw_TX2_P15.value * decode gamma=decode value := by
  change (⟨⟨⟨1752653420,2102463508⟩,⟨1225424092,618598847⟩⟩,⟨⟨1536678585,34285357⟩,⟨792206628,1259751297⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩=⟨⟨⟨1385409049,1086671526⟩,⟨1659116453,1624084534⟩⟩,⟨⟨1305878831,1685894190⟩,⟨1921581249,1695663205⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^16 := by
  rw [show 16=(15:Nat)+1 from rfl,pow_succ,← JFw_TX2_P15.meaning]
  exact step.symm
theorem source : entry 16=value := identify 16 value canonical meaning
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
end AspisR1.JFw_TX2_P16
end
