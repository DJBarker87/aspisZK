import NDO_JFw_TX2_P24
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P25
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨1244951250#u32,1511904630#u32⟩,⟨2066655336#u32,1645120956#u32⟩⟩,⟨⟨1284924881#u32,455802666#u32⟩,⟨786325583#u32,157728743#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1244951250<2147483647 ∧ 1511904630<2147483647) ∧ (2066655336<2147483647 ∧ 1645120956<2147483647)) ∧
    ((1284924881<2147483647 ∧ 455802666<2147483647) ∧ (786325583<2147483647 ∧ 157728743<2147483647))
  omega
theorem lane0 : (-8202341095873604002 : ZMod 2147483647)=1244951250 := by decide
theorem lane1 : (27485604098082660054 : ZMod 2147483647)=1511904630 := by decide
theorem lane2 : (1043023822195492641 : ZMod 2147483647)=2066655336 := by decide
theorem lane3 : (15796644756254925901 : ZMod 2147483647)=1645120956 := by decide
theorem lane4 : (-1613110805054866104 : ZMod 2147483647)=1284924881 := by decide
theorem lane5 : (23814615028797930178 : ZMod 2147483647)=455802666 := by decide
theorem lane6 : (395413336472472484 : ZMod 2147483647)=786325583 := by decide
theorem lane7 : (13194316903032520002 : ZMod 2147483647)=157728743 := by decide
theorem step : decode JFw_TX2_P24.value * decode gamma=decode value := by
  change (⟨⟨⟨628035096,570157693⟩,⟨1661725734,1777269271⟩⟩,⟨⟨1345811362,937706871⟩,⟨1341609618,771712139⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩=⟨⟨⟨1244951250,1511904630⟩,⟨2066655336,1645120956⟩⟩,⟨⟨1284924881,455802666⟩,⟨786325583,157728743⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^25 := by
  rw [show 25=(24:Nat)+1 from rfl,pow_succ,← JFw_TX2_P24.meaning]
  exact step.symm
theorem source : entry 25=value := identify 25 value canonical meaning
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
end AspisR1.JFw_TX2_P25
end
