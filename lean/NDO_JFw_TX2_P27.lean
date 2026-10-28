import NDO_JFw_TX2_P26
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P27
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨509504871#u32,562297437#u32⟩,⟨830444110#u32,750558315#u32⟩⟩,⟨⟨1775007834#u32,1847964904#u32⟩,⟨2126955715#u32,1829355625#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((509504871<2147483647 ∧ 562297437<2147483647) ∧ (830444110<2147483647 ∧ 750558315<2147483647)) ∧
    ((1775007834<2147483647 ∧ 1847964904<2147483647) ∧ (2126955715<2147483647 ∧ 1829355625<2147483647))
  omega
theorem lane0 : (-4346913967281202214 : ZMod 2147483647)=509504871 := by decide
theorem lane1 : (19015689876935368694 : ZMod 2147483647)=562297437 := by decide
theorem lane2 : (2542633931802219040 : ZMod 2147483647)=830444110 := by decide
theorem lane3 : (12085656768391862992 : ZMod 2147483647)=750558315 := by decide
theorem lane4 : (750037723090985391 : ZMod 2147483647)=1775007834 := by decide
theorem lane5 : (16968049555640710798 : ZMod 2147483647)=1847964904 := by decide
theorem lane6 : (2997732900261238882 : ZMod 2147483647)=2126955715 := by decide
theorem lane7 : (8445595144398319701 : ZMod 2147483647)=1829355625 := by decide
theorem step : decode JFw_TX2_P26.value * decode gamma=decode value := by
  change (⟨⟨⟨1906135911,366206321⟩,⟨1502152916,1309564201⟩⟩,⟨⟨644775892,239709031⟩,⟨459845291,570718651⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩=⟨⟨⟨509504871,562297437⟩,⟨830444110,750558315⟩⟩,⟨⟨1775007834,1847964904⟩,⟨2126955715,1829355625⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^27 := by
  rw [show 27=(26:Nat)+1 from rfl,pow_succ,← JFw_TX2_P26.meaning]
  exact step.symm
theorem source : entry 27=value := identify 27 value canonical meaning
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
end AspisR1.JFw_TX2_P27
end
