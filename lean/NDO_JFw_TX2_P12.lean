import NDO_JFw_TX2_P11
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P12
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨304762092#u32,526756808#u32⟩,⟨1330533011#u32,465096431#u32⟩⟩,⟨⟨1038210451#u32,334988447#u32⟩,⟨221696734#u32,1789294768#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((304762092<2147483647 ∧ 526756808<2147483647) ∧ (1330533011<2147483647 ∧ 465096431<2147483647)) ∧
    ((1038210451<2147483647 ∧ 334988447<2147483647) ∧ (221696734<2147483647 ∧ 1789294768<2147483647))
  omega
theorem lane0 : (-1842778014508644709 : ZMod 2147483647)=304762092 := by decide
theorem lane1 : (15314502687468656041 : ZMod 2147483647)=526756808 := by decide
theorem lane2 : (2512283825092131051 : ZMod 2147483647)=1330533011 := by decide
theorem lane3 : (11328905673607485325 : ZMod 2147483647)=465096431 := by decide
theorem lane4 : (-864271094245303926 : ZMod 2147483647)=1038210451 := by decide
theorem lane5 : (14377576419862032756 : ZMod 2147483647)=334988447 := by decide
theorem lane6 : (2981699579289047789 : ZMod 2147483647)=221696734 := by decide
theorem lane7 : (7665416369070172553 : ZMod 2147483647)=1789294768 := by decide
theorem step : decode JFw_TX2_P11.value * decode gamma=decode value := by
  change (⟨⟨⟨1135303194,338788461⟩,⟨735931834,735227219⟩⟩,⟨⟨1254184109,200559114⟩,⟨735383960,742583315⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩=⟨⟨⟨304762092,526756808⟩,⟨1330533011,465096431⟩⟩,⟨⟨1038210451,334988447⟩,⟨221696734,1789294768⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^12 := by
  rw [show 12=(11:Nat)+1 from rfl,pow_succ,← JFw_TX2_P11.meaning]
  exact step.symm
theorem source : entry 12=value := identify 12 value canonical meaning
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
end AspisR1.JFw_TX2_P12
end
