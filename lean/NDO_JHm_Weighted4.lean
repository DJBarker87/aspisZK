import NDO_JHm_Dots
import NDO_JHm_Weighted3
import RPt_JFq_Claim
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHm_Weighted4
open JHm_Arithmetic
def value : FE := ⟨⟨⟨1733859437,898767316⟩,⟨418910250,914049798⟩⟩,⟨⟨1228256487,44560142⟩,⟨912246270,1848977144⟩⟩⟩
def product : FE := ⟨⟨⟨583876794,470389517⟩,⟨1941111076,1632510023⟩⟩,⟨⟨495269406,260561415⟩,⟨538158462,645021848⟩⟩⟩
theorem term : JHm_Dots.term 4=product := by
  change (⟨⟨⟨1376226683,1712321640⟩,⟨190663200,1810133619⟩⟩,⟨⟨1051832243,1950132196⟩,⟨483065632,20684665⟩⟩⟩ : FE)*⟨⟨⟨965218714,1979752929⟩,⟨138221679,1136390224⟩⟩,⟨⟨322737617,334708618⟩,⟨147022100,1949617474⟩⟩⟩=⟨⟨⟨583876794,470389517⟩,⟨1941111076,1632510023⟩⟩,⟨⟨495269406,260561415⟩,⟨538158462,645021848⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms term
theorem add : JHm_Weighted3.value+product=value := by
  change (⟨⟨⟨1149982643,428377799⟩,⟨625282821,1429023422⟩⟩,⟨⟨732987081,1931482374⟩,⟨374087808,1203955296⟩⟩⟩ : FE)+⟨⟨⟨583876794,470389517⟩,⟨1941111076,1632510023⟩⟩,⟨⟨495269406,260561415⟩,⟨538158462,645021848⟩⟩⟩=⟨⟨⟨1733859437,898767316⟩,⟨418910250,914049798⟩⟩,⟨⟨1228256487,44560142⟩,⟨912246270,1848977144⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms add
theorem source : ∑ j∈Finset.range 5,JHm_Dots.term j=value := by
  rw [Finset.sum_range_succ,JHm_Weighted3.source,term,add]
#print axioms source
end AspisR1.JHm_Weighted4
end
