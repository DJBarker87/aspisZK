import NDO_JFw_TX2_P00
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P01
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨855639275#u32,1483149559#u32⟩,⟨1898717401#u32,1849775942#u32⟩⟩,⟨⟨1112406525#u32,1796814865#u32⟩,⟨1838939499#u32,418714188#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((855639275<2147483647 ∧ 1483149559<2147483647) ∧ (1898717401<2147483647 ∧ 1849775942<2147483647)) ∧
    ((1112406525<2147483647 ∧ 1796814865<2147483647) ∧ (1838939499<2147483647 ∧ 418714188<2147483647))
  omega
theorem step : decode JFw_TX2_P00.value * decode gamma=decode value := by
  change (⟨⟨⟨1,0⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨0,0⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩=⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩
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
