import NDO_JFw_TX2_P02
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P03
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨658110426#u32,1790040855#u32⟩,⟨598652022#u32,49316637#u32⟩⟩,⟨⟨503185052#u32,1277459006#u32⟩,⟨1692452649#u32,1165546036#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((658110426<2147483647 ∧ 1790040855<2147483647) ∧ (598652022<2147483647 ∧ 49316637<2147483647)) ∧
    ((503185052<2147483647 ∧ 1277459006<2147483647) ∧ (1692452649<2147483647 ∧ 1165546036<2147483647))
  omega
theorem lane0 : (-12233626477684908853 : ZMod 2147483647)=658110426 := by decide
theorem lane1 : (19538802959550926729 : ZMod 2147483647)=1790040855 := by decide
theorem lane2 : (-2328300070819183201 : ZMod 2147483647)=598652022 := by decide
theorem lane3 : (16488787897399943331 : ZMod 2147483647)=49316637 := by decide
theorem lane4 : (-4326552755707314117 : ZMod 2147483647)=503185052 := by decide
theorem lane5 : (13955692812990894307 : ZMod 2147483647)=1277459006 := by decide
theorem lane6 : (-1324921821377140245 : ZMod 2147483647)=1692452649 := by decide
theorem lane7 : (13183158291247716597 : ZMod 2147483647)=1165546036 := by decide
theorem step : decode JFw_TX2_P02.value * decode gamma=decode value := by
  change (⟨⟨⟨2000426900,1068506882⟩,⟨462294053,953096761⟩⟩,⟨⟨1646200311,1903282404⟩,⟨849779435,716750434⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩=⟨⟨⟨658110426,1790040855⟩,⟨598652022,49316637⟩⟩,⟨⟨503185052,1277459006⟩,⟨1692452649,1165546036⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^3 := by
  rw [show 3=(2:Nat)+1 from rfl,pow_succ,← JFw_TX2_P02.meaning]
  exact step.symm
theorem source : entry 3=value := identify 3 value canonical meaning
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
end AspisR1.JFw_TX2_P03
end
