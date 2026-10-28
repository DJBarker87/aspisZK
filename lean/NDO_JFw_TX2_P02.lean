import NDO_JFw_TX2_P01
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P02
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨867568255#u32,655227887#u32⟩,⟨1032732628#u32,656039795#u32⟩⟩,⟨⟨1345999435#u32,1253123171#u32⟩,⟨1353876630#u32,1675147475#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((867568255<2147483647 ∧ 655227887<2147483647) ∧ (1032732628<2147483647 ∧ 656039795<2147483647)) ∧
    ((1345999435<2147483647 ∧ 1253123171<2147483647) ∧ (1353876630<2147483647 ∧ 1675147475<2147483647))
  omega
theorem step : decode JFw_TX2_P01.value * decode gamma=decode value := by
  change (⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩ : AspisWideTower.WideExact)*⟨⟨⟨855639275,1483149559⟩,⟨1898717401,1849775942⟩⟩,⟨⟨1112406525,1796814865⟩,⟨1838939499,418714188⟩⟩⟩=⟨⟨⟨867568255,655227887⟩,⟨1032732628,656039795⟩⟩,⟨⟨1345999435,1253123171⟩,⟨1353876630,1675147475⟩⟩⟩
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
