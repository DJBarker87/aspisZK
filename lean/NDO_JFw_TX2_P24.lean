import NDO_JFw_TX2_P23
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P24
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨628035096#u32,570157693#u32⟩,⟨1661725734#u32,1777269271#u32⟩⟩,⟨⟨1345811362#u32,937706871#u32⟩,⟨1341609618#u32,771712139#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((628035096<2147483647 ∧ 570157693<2147483647) ∧ (1661725734<2147483647 ∧ 1777269271<2147483647)) ∧
    ((1345811362<2147483647 ∧ 937706871<2147483647) ∧ (1341609618<2147483647 ∧ 771712139<2147483647))
  omega
theorem lane0 : (-9286447824974693301 : ZMod 2147483647)=628035096 := by decide
theorem lane1 : (28217674774117697295 : ZMod 2147483647)=570157693 := by decide
theorem lane2 : (632475794454473058 : ZMod 2147483647)=1661725734 := by decide
theorem lane3 : (20267102580068879678 : ZMod 2147483647)=1777269271 := by decide
theorem lane4 : (-4733372149294164628 : ZMod 2147483647)=1345811362 := by decide
theorem lane5 : (26121376763136227816 : ZMod 2147483647)=937706871 := by decide
theorem lane6 : (2302678020165325735 : ZMod 2147483647)=1341609618 := by decide
theorem lane7 : (14710977484890807391 : ZMod 2147483647)=771712139 := by decide
theorem step : decode JFw_TX2_P23.value * decode gamma=decode value := by
  change (⟨⟨⟨1858903615,1018329259⟩,⟨1550509101,1843639311⟩⟩,⟨⟨1749638204,702011012⟩,⟨1014161165,1343575777⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩=⟨⟨⟨628035096,570157693⟩,⟨1661725734,1777269271⟩⟩,⟨⟨1345811362,937706871⟩,⟨1341609618,771712139⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^24 := by
  rw [show 24=(23:Nat)+1 from rfl,pow_succ,← JFw_TX2_P23.meaning]
  exact step.symm
theorem source : entry 24=value := identify 24 value canonical meaning
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
end AspisR1.JFw_TX2_P24
end
