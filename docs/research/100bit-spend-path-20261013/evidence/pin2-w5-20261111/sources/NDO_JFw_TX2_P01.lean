import NDO_JFw_TX2_P00
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P01
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨855536485#u32,461474173#u32⟩,⟨798342634#u32,1775607996#u32⟩⟩,⟨⟨2127456138#u32,1342862068#u32⟩,⟨1305843559#u32,1845381817#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((855536485<2147483647 ∧ 461474173<2147483647) ∧ (798342634<2147483647 ∧ 1775607996<2147483647)) ∧
    ((2127456138<2147483647 ∧ 1342862068<2147483647) ∧ (1305843559<2147483647 ∧ 1845381817<2147483647))
  omega
theorem step : decode JFw_TX2_P00.value * decode gamma=decode value := by
  change (⟨⟨⟨1,0⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨0,0⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩=⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R]
theorem meaning : decode value=decode gamma^1 := by
  rw [show 1=(0:Nat)+1 from rfl,pow_succ,← JFw_TX2_P00.meaning]
  exact step.symm
theorem source : entry 1=value := identify 1 value canonical meaning
#print axioms canonical
#print axioms step
#print axioms meaning
#print axioms source
end AspisR1.JFw_TX2_P01
end
