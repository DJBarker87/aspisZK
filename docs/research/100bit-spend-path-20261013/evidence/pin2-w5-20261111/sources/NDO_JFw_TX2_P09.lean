import NDO_JFw_TX2_P08
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P09
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨498811878#u32,1576902255#u32⟩,⟨1278812500#u32,1262498881#u32⟩⟩,⟨⟨1852080514#u32,1795303126#u32⟩,⟨1519238227#u32,407841680#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((498811878<2147483647 ∧ 1576902255<2147483647) ∧ (1278812500<2147483647 ∧ 1262498881<2147483647)) ∧
    ((1852080514<2147483647 ∧ 1795303126<2147483647) ∧ (1519238227<2147483647 ∧ 407841680<2147483647))
  omega
theorem lane0 : (-16665159536926500731 : ZMod 2147483647)=498811878 := by decide
theorem lane1 : (25728611172346812243 : ZMod 2147483647)=1576902255 := by decide
theorem lane2 : (-8759548362046736643 : ZMod 2147483647)=1278812500 := by decide
theorem lane3 : (18017872847428879477 : ZMod 2147483647)=1262498881 := by decide
theorem lane4 : (-15166161878476484282 : ZMod 2147483647)=1852080514 := by decide
theorem lane5 : (15042320455866255696 : ZMod 2147483647)=1795303126 := by decide
theorem lane6 : (-3067675356666076852 : ZMod 2147483647)=1519238227 := by decide
theorem lane7 : (13463507515339649548 : ZMod 2147483647)=407841680 := by decide
theorem step : decode JFw_TX2_P08.value * decode gamma=decode value := by
  change (⟨⟨⟨803384121,1332142427⟩,⟨387819137,1488822400⟩⟩,⟨⟨1775426482,1276020657⟩,⟨1492984079,1978943953⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩=⟨⟨⟨498811878,1576902255⟩,⟨1278812500,1262498881⟩⟩,⟨⟨1852080514,1795303126⟩,⟨1519238227,407841680⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P]
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
theorem meaning : decode value=decode gamma^9 := by
  rw [show 9=(8:Nat)+1 from rfl,pow_succ,← JFw_TX2_P08.meaning]
  exact step.symm
theorem source : entry 9=value := identify 9 value canonical meaning
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
end AspisR1.JFw_TX2_P09
end
