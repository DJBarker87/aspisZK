import NDO_JFw_TX2_P14
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P15
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨1752653420#u32,2102463508#u32⟩,⟨1225424092#u32,618598847#u32⟩⟩,⟨⟨1536678585#u32,34285357#u32⟩,⟨792206628#u32,1259751297#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1752653420<2147483647 ∧ 2102463508<2147483647) ∧ (1225424092<2147483647 ∧ 618598847<2147483647)) ∧
    ((1536678585<2147483647 ∧ 34285357<2147483647) ∧ (792206628<2147483647 ∧ 1259751297<2147483647))
  omega
theorem lane0 : (-13219951720506538360 : ZMod 2147483647)=1752653420 := by decide
theorem lane1 : (16235322354512831678 : ZMod 2147483647)=2102463508 := by decide
theorem lane2 : (-6266123621614880426 : ZMod 2147483647)=1225424092 := by decide
theorem lane3 : (11365459734525812458 : ZMod 2147483647)=618598847 := by decide
theorem lane4 : (-7474866583365486121 : ZMod 2147483647)=1536678585 := by decide
theorem lane5 : (13567055454835272974 : ZMod 2147483647)=34285357 := by decide
theorem lane6 : (-3429941114756706384 : ZMod 2147483647)=792206628 := by decide
theorem lane7 : (10379331638839521595 : ZMod 2147483647)=1259751297 := by decide
theorem step : decode JFw_TX2_P14.value * decode gamma=decode value := by
  change (⟨⟨⟨824208172,1852498770⟩,⟨950153811,1379836302⟩⟩,⟨⟨171986381,1296497964⟩,⟨109088572,518661610⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩=⟨⟨⟨1752653420,2102463508⟩,⟨1225424092,618598847⟩⟩,⟨⟨1536678585,34285357⟩,⟨792206628,1259751297⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^15 := by
  rw [show 15=(14:Nat)+1 from rfl,pow_succ,← JFw_TX2_P14.meaning]
  exact step.symm
theorem source : entry 15=value := identify 15 value canonical meaning
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
end AspisR1.JFw_TX2_P15
end
