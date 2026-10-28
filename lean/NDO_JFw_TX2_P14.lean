import NDO_JFw_TX2_P13
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P14
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨824208172#u32,1852498770#u32⟩,⟨950153811#u32,1379836302#u32⟩⟩,⟨⟨171986381#u32,1296497964#u32⟩,⟨109088572#u32,518661610#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((824208172<2147483647 ∧ 1852498770<2147483647) ∧ (950153811<2147483647 ∧ 1379836302<2147483647)) ∧
    ((171986381<2147483647 ∧ 1296497964<2147483647) ∧ (109088572<2147483647 ∧ 518661610<2147483647))
  omega
theorem lane0 : (-3527870913103301892 : ZMod 2147483647)=824208172 := by decide
theorem lane1 : (22546988431604246084 : ZMod 2147483647)=1852498770 := by decide
theorem lane2 : (3534586274482975576 : ZMod 2147483647)=950153811 := by decide
theorem lane3 : (11268863270850169515 : ZMod 2147483647)=1379836302 := by decide
theorem lane4 : (3206900064676866192 : ZMod 2147483647)=171986381 := by decide
theorem lane5 : (16556934843325932576 : ZMod 2147483647)=1296497964 := by decide
theorem lane6 : (844951825698050257 : ZMod 2147483647)=109088572 := by decide
theorem lane7 : (9632366736100561122 : ZMod 2147483647)=518661610 := by decide
theorem step : decode JFw_TX2_P13.value * decode gamma=decode value := by
  change (⟨⟨⟨1465393816,184076238⟩,⟨1052874750,451889791⟩⟩,⟨⟨274378589,2023650872⟩,⟨1297524163,13407412⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩=⟨⟨⟨824208172,1852498770⟩,⟨950153811,1379836302⟩⟩,⟨⟨171986381,1296497964⟩,⟨109088572,518661610⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^14 := by
  rw [show 14=(13:Nat)+1 from rfl,pow_succ,← JFw_TX2_P13.meaning]
  exact step.symm
theorem source : entry 14=value := identify 14 value canonical meaning
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
end AspisR1.JFw_TX2_P14
end
