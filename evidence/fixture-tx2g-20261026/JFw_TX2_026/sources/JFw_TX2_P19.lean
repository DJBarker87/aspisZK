import JFw_TX2_P18
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P19
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨2005758375#u32,2005073905#u32⟩,⟨1602919019#u32,185546252#u32⟩⟩,⟨⟨2023391453#u32,1199631211#u32⟩,⟨239612482#u32,1982757556#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((2005758375<2147483647 ∧ 2005073905<2147483647) ∧ (1602919019<2147483647 ∧ 185546252<2147483647)) ∧
    ((2023391453<2147483647 ∧ 1199631211<2147483647) ∧ (239612482<2147483647 ∧ 1982757556<2147483647))
  omega
theorem step : decode JFw_TX2_P18.value * decode gamma=decode value := by
  change (⟨⟨⟨1298953245,1504805752⟩,⟨2073609211,1840812326⟩⟩,⟨⟨1755193245,1295624230⟩,⟨476103426,940478841⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩=⟨⟨⟨2005758375,2005073905⟩,⟨1602919019,185546252⟩⟩,⟨⟨2023391453,1199631211⟩,⟨239612482,1982757556⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU, AspisV8R15.ExactTowerBase.qm31R]
theorem meaning : decode value=decode gamma^19 := by
  rw [show 19=(18:Nat)+1 from rfl,pow_succ,← JFw_TX2_P18.meaning]
  exact step.symm
theorem source : entry 19=value := identify 19 value canonical meaning
#print axioms canonical
#print axioms step
#print axioms meaning
#print axioms source
end AspisR1.JFw_TX2_P19
end
