import NDO_JFw_TX2_P25
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P26
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨1906135911#u32,366206321#u32⟩,⟨1502152916#u32,1309564201#u32⟩⟩,⟨⟨644775892#u32,239709031#u32⟩,⟨459845291#u32,570718651#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1906135911<2147483647 ∧ 366206321<2147483647) ∧ (1502152916<2147483647 ∧ 1309564201<2147483647)) ∧
    ((644775892<2147483647 ∧ 239709031<2147483647) ∧ (459845291<2147483647 ∧ 570718651<2147483647))
  omega
theorem lane0 : (-3799686960275801670 : ZMod 2147483647)=1906135911 := by decide
theorem lane1 : (26606373375017891375 : ZMod 2147483647)=366206321 := by decide
theorem lane2 : (1646467188146974326 : ZMod 2147483647)=1502152916 := by decide
theorem lane3 : (15080720037821769524 : ZMod 2147483647)=1309564201 := by decide
theorem lane4 : (2072795330338252566 : ZMod 2147483647)=644775892 := by decide
theorem lane5 : (21816652342128347124 : ZMod 2147483647)=239709031 := by decide
theorem lane6 : (3034769361495480667 : ZMod 2147483647)=459845291 := by decide
theorem lane7 : (13388481143467776100 : ZMod 2147483647)=570718651 := by decide
theorem step : decode JFw_TX2_P25.value * decode gamma=decode value := by
  change (⟨⟨⟨1244951250,1511904630⟩,⟨2066655336,1645120956⟩⟩,⟨⟨1284924881,455802666⟩,⟨786325583,157728743⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩=⟨⟨⟨1906135911,366206321⟩,⟨1502152916,1309564201⟩⟩,⟨⟨644775892,239709031⟩,⟨459845291,570718651⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^26 := by
  rw [show 26=(25:Nat)+1 from rfl,pow_succ,← JFw_TX2_P25.meaning]
  exact step.symm
theorem source : entry 26=value := identify 26 value canonical meaning
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
end AspisR1.JFw_TX2_P26
end
