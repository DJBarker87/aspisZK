import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace R26SchoolbookDot
variable {F : Type*} [CommRing F]

theorem tower_product (a b c d e f g h : F) :
    (a*e-b*f+2*(c*g-d*h)-(c*h+d*g),
     a*f+b*e+(c*g-d*h)+2*(c*h+d*g),
     a*g-b*h+c*e-d*f,
     a*h+b*g+c*f+d*e) =
    (a*e+2*(c*g)-b*f-2*(d*h)-c*h-d*g,
     a*f+b*e+c*g+2*(c*h)+2*(d*g)-d*h,
     a*g+c*e-b*h-d*f,
     a*h+b*g+c*f+d*e) := by
  ext <;> ring

theorem commute_sum {ι : Type*} (s : Finset ι)
    (a b c d e f : ι → F) :
    (∑ i ∈ s, (a i + 2*b i - c i - 2*d i - e i - f i)) =
    (∑ i ∈ s, a i) + 2*(∑ i ∈ s, b i) - (∑ i ∈ s, c i) -
      2*(∑ i ∈ s, d i) - (∑ i ∈ s, e i) - (∑ i ∈ s, f i) := by
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

theorem numeric_bounds :
    4*(2147483647-1:Nat)^2 < 2^64 ∧
    1024*(5*2147483647:Nat) < 2^44 ∧
    8*(2147483647:Nat) < 2^34 := by norm_num

#print axioms tower_product
#print axioms commute_sum
#print axioms numeric_bounds
end R26SchoolbookDot
