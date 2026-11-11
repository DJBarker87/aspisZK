import NDO_JFw_TX2_P01
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P02
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨2000426900#u32,1068506882#u32⟩,⟨462294053#u32,953096761#u32⟩⟩,⟨⟨1646200311#u32,1903282404#u32⟩,⟨849779435#u32,716750434#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((2000426900<2147483647 ∧ 1068506882<2147483647) ∧ (462294053<2147483647 ∧ 953096761<2147483647)) ∧
    ((1646200311<2147483647 ∧ 1903282404<2147483647) ∧ (849779435<2147483647 ∧ 716750434<2147483647))
  omega
theorem step : decode JFw_TX2_P01.value * decode gamma=decode value := by
  change (⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855536485,461474173⟩,⟨798342634,1775607996⟩⟩,⟨⟨2127456138,1342862068⟩,⟨1305843559,1845381817⟩⟩⟩=⟨⟨⟨2000426900,1068506882⟩,⟨462294053,953096761⟩⟩,⟨⟨1646200311,1903282404⟩,⟨849779435,716750434⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R, AspisV8R15.ExactTowerBase.M31Exact, AspisV8R15.ExactTowerBase.P] <;> decide
theorem meaning : decode value=decode gamma^2 := by
  rw [show 2=(1:Nat)+1 from rfl,pow_succ,← JFw_TX2_P01.meaning]
  exact step.symm
theorem source : entry 2=value := identify 2 value canonical meaning
#print axioms canonical
#print axioms step
#print axioms meaning
#print axioms source
end AspisR1.JFw_TX2_P02
end
