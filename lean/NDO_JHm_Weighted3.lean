import NDO_JHm_Dots
import NDO_JHm_Weighted2
import RPt_JFq_Claim
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHm_Weighted3
open JHm_Arithmetic
def value : FE := ⟨⟨⟨1149982643,428377799⟩,⟨625282821,1429023422⟩⟩,⟨⟨732987081,1931482374⟩,⟨374087808,1203955296⟩⟩⟩
def product : FE := ⟨⟨⟨1363951776,971393720⟩,⟨1638991440,976459759⟩⟩,⟨⟨1290558237,1026446948⟩,⟨829522529,1222768301⟩⟩⟩
theorem term : JHm_Dots.term 3=product := by
  change (⟨⟨⟨2006370403,841359646⟩,⟨376899686,2013808952⟩⟩,⟨⟨1241193111,1543519322⟩,⟨400137173,1242945666⟩⟩⟩ : FE)*⟨⟨⟨2025241423,225103310⟩,⟨1071023879,381223699⟩⟩,⟨⟨1327952494,1657160323⟩,⟨1939282226,1031746705⟩⟩⟩=⟨⟨⟨1363951776,971393720⟩,⟨1638991440,976459759⟩⟩,⟨⟨1290558237,1026446948⟩,⟨829522529,1222768301⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms term
theorem add : JHm_Weighted2.value+product=value := by
  change (⟨⟨⟨1933514514,1604467726⟩,⟨1133775028,452563663⟩⟩,⟨⟨1589912491,905035426⟩,⟨1692048926,2128670642⟩⟩⟩ : FE)+⟨⟨⟨1363951776,971393720⟩,⟨1638991440,976459759⟩⟩,⟨⟨1290558237,1026446948⟩,⟨829522529,1222768301⟩⟩⟩=⟨⟨⟨1149982643,428377799⟩,⟨625282821,1429023422⟩⟩,⟨⟨732987081,1931482374⟩,⟨374087808,1203955296⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms add
theorem source : ∑ j∈Finset.range 4,JHm_Dots.term j=value := by
  rw [Finset.sum_range_succ,JHm_Weighted2.source,term,add]
#print axioms source
end AspisR1.JHm_Weighted3
end
