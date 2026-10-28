import NDO_JHm_Dots
import RPt_JFq_Claim
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHm_Weighted0
open JHm_Arithmetic
def value : FE := ⟨⟨⟨1601557143,1452416229⟩,⟨1050842712,1241115319⟩⟩,⟨⟨397817978,167756708⟩,⟨2093719752,1754141354⟩⟩⟩
def product : FE := ⟨⟨⟨1601557143,1452416229⟩,⟨1050842712,1241115319⟩⟩,⟨⟨397817978,167756708⟩,⟨2093719752,1754141354⟩⟩⟩
theorem term : JHm_Dots.term 0=product := by
  change (⟨⟨⟨1116662073,1579954339⟩,⟨1176243488,728698552⟩⟩,⟨⟨640606056,1197281433⟩,⟨2141139535,1224613133⟩⟩⟩ : FE)*⟨⟨⟨1590890973,1111194882⟩,⟨243528882,1146003763⟩⟩,⟨⟨1031698620,1797768879⟩,⟨1713917058,1018629224⟩⟩⟩=⟨⟨⟨1601557143,1452416229⟩,⟨1050842712,1241115319⟩⟩,⟨⟨397817978,167756708⟩,⟨2093719752,1754141354⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms term
theorem add : 0+product=value := by
  change (⟨⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨0,0⟩⟩⟩ : FE)+⟨⟨⟨1601557143,1452416229⟩,⟨1050842712,1241115319⟩⟩,⟨⟨397817978,167756708⟩,⟨2093719752,1754141354⟩⟩⟩=⟨⟨⟨1601557143,1452416229⟩,⟨1050842712,1241115319⟩⟩,⟨⟨397817978,167756708⟩,⟨2093719752,1754141354⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms add
theorem source : ∑ j∈Finset.range 1,JHm_Dots.term j=value := by
  rw [Finset.sum_range_succ,Finset.sum_range_zero,term,add]
#print axioms source
end AspisR1.JHm_Weighted0
end
