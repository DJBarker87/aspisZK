import NDO_JFw_TX2_P12
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P13
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨1465393816#u32,184076238#u32⟩,⟨1052874750#u32,451889791#u32⟩⟩,⟨⟨274378589#u32,2023650872#u32⟩,⟨1297524163#u32,13407412#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1465393816<2147483647 ∧ 184076238<2147483647) ∧ (1052874750<2147483647 ∧ 451889791<2147483647)) ∧
    ((274378589<2147483647 ∧ 2023650872<2147483647) ∧ (1297524163<2147483647 ∧ 13407412<2147483647))
  omega
theorem lane0 : (-6371256968963775612 : ZMod 2147483647)=1465393816 := by decide
theorem lane1 : (14936796286117246368 : ZMod 2147483647)=184076238 := by decide
theorem lane2 : (-3460341232305386488 : ZMod 2147483647)=1052874750 := by decide
theorem lane3 : (12598301989835831466 : ZMod 2147483647)=451889791 := by decide
theorem lane4 : (-6709476564996431323 : ZMod 2147483647)=274378589 := by decide
theorem lane5 : (12762894964998841219 : ZMod 2147483647)=2023650872 := by decide
theorem lane6 : (-128204712298833721 : ZMod 2147483647)=1297524163 := by decide
theorem lane7 : (8420685309382230873 : ZMod 2147483647)=13407412 := by decide
theorem step : decode JFw_TX2_P12.value * decode gamma=decode value := by
  change (⟨⟨⟨304762092,526756808⟩,⟨1330533011,465096431⟩⟩,⟨⟨1038210451,334988447⟩,⟨221696734,1789294768⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩=⟨⟨⟨1465393816,184076238⟩,⟨1052874750,451889791⟩⟩,⟨⟨274378589,2023650872⟩,⟨1297524163,13407412⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^13 := by
  rw [show 13=(12:Nat)+1 from rfl,pow_succ,← JFw_TX2_P12.meaning]
  exact step.symm
theorem source : entry 13=value := identify 13 value canonical meaning
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
end AspisR1.JFw_TX2_P13
end
