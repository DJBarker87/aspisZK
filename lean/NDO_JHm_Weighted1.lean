import NDO_JHm_Dots
import NDO_JHm_Weighted0
import RPt_JFq_Claim
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHm_Weighted1
open JHm_Arithmetic
def value : FE := ⟨⟨⟨2088789282,706366318⟩,⟨1931021435,608291850⟩⟩,⟨⟨1516325395,1452600344⟩,⟨1920193449,827680738⟩⟩⟩
def product : FE := ⟨⟨⟨487232139,1401433736⟩,⟨880178723,1514660178⟩⟩,⟨⟨1118507417,1284843636⟩,⟨1973957344,1221023031⟩⟩⟩
theorem term : JHm_Dots.term 1=product := by
  change (⟨⟨⟨194086607,1888419081⟩,⟨1301861674,1187144623⟩⟩,⟨⟨855257644,590989944⟩,⟨1958695353,1064062444⟩⟩⟩ : FE)*⟨⟨⟨707208785,896043035⟩,⟨591874583,2130241614⟩⟩,⟨⟨1043700919,1701660885⟩,⟨648978545,236843822⟩⟩⟩=⟨⟨⟨487232139,1401433736⟩,⟨880178723,1514660178⟩⟩,⟨⟨1118507417,1284843636⟩,⟨1973957344,1221023031⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms term
theorem add : JHm_Weighted0.value+product=value := by
  change (⟨⟨⟨1601557143,1452416229⟩,⟨1050842712,1241115319⟩⟩,⟨⟨397817978,167756708⟩,⟨2093719752,1754141354⟩⟩⟩ : FE)+⟨⟨⟨487232139,1401433736⟩,⟨880178723,1514660178⟩⟩,⟨⟨1118507417,1284843636⟩,⟨1973957344,1221023031⟩⟩⟩=⟨⟨⟨2088789282,706366318⟩,⟨1931021435,608291850⟩⟩,⟨⟨1516325395,1452600344⟩,⟨1920193449,827680738⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms add
theorem source : ∑ j∈Finset.range 2,JHm_Dots.term j=value := by
  rw [Finset.sum_range_succ,JHm_Weighted0.source,term,add]
#print axioms source
end AspisR1.JHm_Weighted1
end
