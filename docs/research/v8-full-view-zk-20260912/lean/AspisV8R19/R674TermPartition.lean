import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace AspisV8R19.R674TermPartition
open scoped BigOperators
/-- Pure symbolic partition of the selected 26+12 products into its ten
source chunks. No native array or dependent-index term is normalized. -/
theorem term_partition (f g : Nat → Nat) :
    (∑ i ∈ Finset.range 26, f i) + (∑ j ∈ Finset.range 12, g j) =
      [f 0+f 1+f 2+f 3,f 4+f 5+f 6+f 7,f 8+f 9+f 10+f 11,f 12+f 13+f 14+f 15,f 16+f 17+f 18+f 19,f 20+f 21+f 22+f 23,f 24+f 25+g 0+g 1,g 2+g 3+g 4+g 5,g 6+g 7+g 8+g 9,g 10+g 11].sum := by
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,List.sum_cons,List.sum_nil]
  ring
#print axioms term_partition
end AspisV8R19.R674TermPartition
