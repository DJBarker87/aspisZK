import NDO_JHm_Dots
import NDO_JHm_Weighted4
import RPt_JFq_Claim
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHm_Weighted5
open JHm_Arithmetic
def value : FE := ⟨⟨⟨1653632192,1119241674⟩,⟨1504411203,1216841972⟩⟩,⟨⟨2000740570,1632264801⟩,⟨1558325561,1283233474⟩⟩⟩
def product : FE := ⟨⟨⟨2067256402,220474358⟩,⟨1085500953,302792174⟩⟩,⟨⟨772484083,1587704659⟩,⟨646079291,1581739977⟩⟩⟩
theorem term : JHm_Dots.term 5=product := by
  change (⟨⟨⟨1669677601,1938847927⟩,⟨2006801723,1268458862⟩⟩,⟨⟨480042823,1027734773⟩,⟨1137142088,282041615⟩⟩⟩ : FE)*⟨⟨⟨1353662995,664871591⟩,⟨1002743767,768126861⟩⟩,⟨⟨817465324,932172597⟩,⟨1176156737,1286428944⟩⟩⟩=⟨⟨⟨2067256402,220474358⟩,⟨1085500953,302792174⟩⟩,⟨⟨772484083,1587704659⟩,⟨646079291,1581739977⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms term
theorem add : JHm_Weighted4.value+product=value := by
  change (⟨⟨⟨1733859437,898767316⟩,⟨418910250,914049798⟩⟩,⟨⟨1228256487,44560142⟩,⟨912246270,1848977144⟩⟩⟩ : FE)+⟨⟨⟨2067256402,220474358⟩,⟨1085500953,302792174⟩⟩,⟨⟨772484083,1587704659⟩,⟨646079291,1581739977⟩⟩⟩=⟨⟨⟨1653632192,1119241674⟩,⟨1504411203,1216841972⟩⟩,⟨⟨2000740570,1632264801⟩,⟨1558325561,1283233474⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms add
theorem source : ∑ j∈Finset.range 6,JHm_Dots.term j=value := by
  rw [Finset.sum_range_succ,JHm_Weighted4.source,term,add]
#print axioms source
theorem retained : value=CheckpointBytes5Output.ofE JFq_Claim.scalar := rfl
#print axioms retained
end AspisR1.JHm_Weighted5
end
