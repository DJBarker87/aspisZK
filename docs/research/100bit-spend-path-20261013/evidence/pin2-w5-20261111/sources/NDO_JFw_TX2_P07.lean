import NDO_JFw_TX2_P06
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P07
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨995644922#u32,1350557097#u32⟩,⟨2039696097#u32,901577836#u32⟩⟩,⟨⟨506310784#u32,419635324#u32⟩,⟨923539768#u32,1229247375#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((995644922<2147483647 ∧ 1350557097<2147483647) ∧ (2039696097<2147483647 ∧ 901577836<2147483647)) ∧
    ((506310784<2147483647 ∧ 419635324<2147483647) ∧ (923539768<2147483647 ∧ 1229247375<2147483647))
  omega
theorem lane0 : (954012664065796877 : ZMod 2147483647)=995644922 := by decide
theorem lane1 : (26137224121269598189 : ZMod 2147483647)=1350557097 := by decide
theorem lane2 : (260718026605119374 : ZMod 2147483647)=2039696097 := by decide
theorem lane3 : (19776997837583218408 : ZMod 2147483647)=901577836 := by decide
theorem lane4 : (-4600261860185570283 : ZMod 2147483647)=506310784 := by decide
theorem lane5 : (18900160633883158669 : ZMod 2147483647)=419635324 := by decide
theorem lane6 : (1176673253949920522 : ZMod 2147483647)=923539768 := by decide
theorem lane7 : (13869233222938918728 : ZMod 2147483647)=1229247375 := by decide
theorem step : decode JFw_TX2_P06.value * decode gamma=decode value := by
  change (⟨⟨⟨1950868962,2061174938⟩,⟨258644308,915368944⟩⟩,⟨⟨2094690493,11221900⟩,⟨2080583196,694755488⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩=⟨⟨⟨995644922,1350557097⟩,⟨2039696097,901577836⟩⟩,⟨⟨506310784,419635324⟩,⟨923539768,1229247375⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^7 := by
  rw [show 7=(6:Nat)+1 from rfl,pow_succ,← JFw_TX2_P06.meaning]
  exact step.symm
theorem source : entry 7=value := identify 7 value canonical meaning
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
end AspisR1.JFw_TX2_P07
end
