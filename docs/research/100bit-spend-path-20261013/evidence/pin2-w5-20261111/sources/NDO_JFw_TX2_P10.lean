import NDO_JFw_TX2_P09
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P10
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨1406118#u32,2097040101#u32⟩,⟨648438797#u32,831220367#u32⟩⟩,⟨⟨775089091#u32,1112063832#u32⟩,⟨823850592#u32,71121305#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1406118<2147483647 ∧ 2097040101<2147483647) ∧ (648438797<2147483647 ∧ 831220367<2147483647)) ∧
    ((775089091<2147483647 ∧ 1112063832<2147483647) ∧ (823850592<2147483647 ∧ 71121305<2147483647))
  omega
theorem lane0 : (-11111152353901088499 : ZMod 2147483647)=1406118 := by decide
theorem lane1 : (26045558443241469967 : ZMod 2147483647)=2097040101 := by decide
theorem lane2 : (-1234526116083254790 : ZMod 2147483647)=648438797 := by decide
theorem lane3 : (18024940673093894774 : ZMod 2147483647)=831220367 := by decide
theorem lane4 : (-7674333141662411153 : ZMod 2147483647)=775089091 := by decide
theorem lane5 : (20307487491149225669 : ZMod 2147483647)=1112063832 := by decide
theorem lane6 : (-1830965245465804606 : ZMod 2147483647)=823850592 := by decide
theorem lane7 : (13154714452636949348 : ZMod 2147483647)=71121305 := by decide
theorem step : decode JFw_TX2_P09.value * decode gamma=decode value := by
  change (⟨⟨⟨498811878,1576902255⟩,⟨1278812500,1262498881⟩⟩,⟨⟨1852080514,1795303126⟩,⟨1519238227,407841680⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩=⟨⟨⟨1406118,2097040101⟩,⟨648438797,831220367⟩⟩,⟨⟨775089091,1112063832⟩,⟨823850592,71121305⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^10 := by
  rw [show 10=(9:Nat)+1 from rfl,pow_succ,← JFw_TX2_P09.meaning]
  exact step.symm
theorem source : entry 10=value := identify 10 value canonical meaning
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
end AspisR1.JFw_TX2_P10
end
