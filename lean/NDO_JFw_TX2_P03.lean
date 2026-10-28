import NDO_JFw_TX2_P02
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P03
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨352063#u32,39062738#u32⟩,⟨1313565596#u32,1840648083#u32⟩⟩,⟨⟨752376469#u32,1317611639#u32⟩,⟨1258713036#u32,1674326661#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((352063<2147483647 ∧ 39062738<2147483647) ∧ (1313565596<2147483647 ∧ 1840648083<2147483647)) ∧
    ((752376469<2147483647 ∧ 1317611639<2147483647) ∧ (1258713036<2147483647 ∧ 1674326661<2147483647))
  omega
theorem lane0 : (-8161584674996688053 : ZMod 2147483647)=352063 := by decide
theorem lane1 : (23681506432797692810 : ZMod 2147483647)=39062738 := by decide
theorem lane2 : (-479251980714723869 : ZMod 2147483647)=1313565596 := by decide
theorem lane3 : (17837477639621650624 : ZMod 2147483647)=1840648083 := by decide
theorem lane4 : (-6050108553421326864 : ZMod 2147483647)=752376469 := by decide
theorem lane5 : (21100375201567340940 : ZMod 2147483647)=1317611639 := by decide
theorem lane6 : (202700012036434592 : ZMod 2147483647)=1258713036 := by decide
theorem lane7 : (12464047506790666284 : ZMod 2147483647)=1674326661 := by decide
theorem step : decode JFw_TX2_P02.value * decode gamma=decode value := by
  change (⟨⟨⟨867568255,655227887⟩,⟨1032732628,656039795⟩⟩,⟨⟨1345999435,1253123171⟩,⟨1353876630,1675147475⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩=⟨⟨⟨352063,39062738⟩,⟨1313565596,1840648083⟩⟩,⟨⟨752376469,1317611639⟩,⟨1258713036,1674326661⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^3 := by
  rw [show 3=(2:Nat)+1 from rfl,pow_succ,← JFw_TX2_P02.meaning]
  exact step.symm
theorem source : entry 3=value := identify 3 value canonical meaning
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
end AspisR1.JFw_TX2_P03
end
