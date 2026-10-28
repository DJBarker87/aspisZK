import NDO_JFw_TX2_P10
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P11
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨1135303194#u32,338788461#u32⟩,⟨735931834#u32,735227219#u32⟩⟩,⟨⟨1254184109#u32,200559114#u32⟩,⟨735383960#u32,742583315#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1135303194<2147483647 ∧ 338788461<2147483647) ∧ (735931834<2147483647 ∧ 735227219<2147483647)) ∧
    ((1254184109<2147483647 ∧ 200559114<2147483647) ∧ (735383960<2147483647 ∧ 742583315<2147483647))
  omega
theorem lane0 : (-5726891319756890948 : ZMod 2147483647)=1135303194 := by decide
theorem lane1 : (30821677997873450681 : ZMod 2147483647)=338788461 := by decide
theorem lane2 : (620046140999973982 : ZMod 2147483647)=735931834 := by decide
theorem lane3 : (19338000197980908509 : ZMod 2147483647)=735227219 := by decide
theorem lane4 : (-1490185424484844499 : ZMod 2147483647)=1254184109 := by decide
theorem lane5 : (23078014017916707601 : ZMod 2147483647)=200559114 := by decide
theorem lane6 : (1256977773381137496 : ZMod 2147483647)=735383960 := by decide
theorem lane7 : (14761098934991389060 : ZMod 2147483647)=742583315 := by decide
theorem step : decode JFw_TX2_P10.value * decode gamma=decode value := by
  change (⟨⟨⟨1364884909,594709522⟩,⟨2038502201,377386917⟩⟩,⟨⟨1137838899,2003659556⟩,⟨1264608004,1435903714⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩=⟨⟨⟨1135303194,338788461⟩,⟨735931834,735227219⟩⟩,⟨⟨1254184109,200559114⟩,⟨735383960,742583315⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^11 := by
  rw [show 11=(10:Nat)+1 from rfl,pow_succ,← JFw_TX2_P10.meaning]
  exact step.symm
theorem source : entry 11=value := identify 11 value canonical meaning
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
end AspisR1.JFw_TX2_P11
end
