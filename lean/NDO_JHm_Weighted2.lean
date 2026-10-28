import NDO_JHm_Dots
import NDO_JHm_Weighted1
import RPt_JFq_Claim
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHm_Weighted2
open JHm_Arithmetic
def value : FE := ⟨⟨⟨1933514514,1604467726⟩,⟨1133775028,452563663⟩⟩,⟨⟨1589912491,905035426⟩,⟨1692048926,2128670642⟩⟩⟩
def product : FE := ⟨⟨⟨1992208879,898101408⟩,⟨1350237240,1991755460⟩⟩,⟨⟨73587096,1599918729⟩,⟨1919339124,1300989904⟩⟩⟩
theorem term : JHm_Dots.term 2=product := by
  change (⟨⟨⟨1266306440,1524792638⟩,⟨36588852,1044096672⟩⟩,⟨⟨2018106446,381171209⟩,⟨1489892152,1479239577⟩⟩⟩ : FE)*⟨⟨⟨1924539489,275728125⟩,⟨2036691133,1877811594⟩⟩,⟨⟨1167901874,145250939⟩,⟨1866931257,1550516676⟩⟩⟩=⟨⟨⟨1992208879,898101408⟩,⟨1350237240,1991755460⟩⟩,⟨⟨73587096,1599918729⟩,⟨1919339124,1300989904⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms term
theorem add : JHm_Weighted1.value+product=value := by
  change (⟨⟨⟨2088789282,706366318⟩,⟨1931021435,608291850⟩⟩,⟨⟨1516325395,1452600344⟩,⟨1920193449,827680738⟩⟩⟩ : FE)+⟨⟨⟨1992208879,898101408⟩,⟨1350237240,1991755460⟩⟩,⟨⟨73587096,1599918729⟩,⟨1919339124,1300989904⟩⟩⟩=⟨⟨⟨1933514514,1604467726⟩,⟨1133775028,452563663⟩⟩,⟨⟨1589912491,905035426⟩,⟨1692048926,2128670642⟩⟩⟩
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms add
theorem source : ∑ j∈Finset.range 3,JHm_Dots.term j=value := by
  rw [Finset.sum_range_succ,JHm_Weighted1.source,term,add]
#print axioms source
end AspisR1.JHm_Weighted2
end
