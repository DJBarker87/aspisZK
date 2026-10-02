import AspisV8R19.R374SingleCoordinateDegree

/-! Ordinary and xor12 opening polynomials are affine in one original
coordinate. The successor bound remains ten. No Rust execution or complete
terminal degree correspondence is asserted here. -/
set_option autoImplicit false
namespace AspisR19.R376SimplePointDegree
open Polynomial ResidualModel R374SingleCoordinateDegree
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F]

theorem simple_point_degree (z : Fin 10 → F) (j i : Fin 10)
    (which : Nat) (hwhich : which≠1) :
    (point (line z j) which i).natDegree ≤ if i=j then 1 else 0 := by
  by_cases h0 : which=0
  · simpa only [point,if_pos h0] using line_degree z j i
  · simp only [point,if_neg h0,if_neg hwhich]
    split_ifs
    · exact sub_bound (by simp) (line_degree z j i)
    · exact line_degree z j i

theorem simple_tensor_degree (z : Fin 10 → F) (j : Fin 10)
    (which r : Nat) (hwhich : which≠1) :
    (tensor (point (line z j) which) r).natDegree ≤ 1 := by
  unfold tensor
  apply (natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ i : Fin 10, (if i=j then 1 else 0 : Nat) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · exact sub_bound (by simp) (simple_point_degree z j i which hwhich)
      · exact simple_point_degree z j i which hwhich
    _ = 1 := by simp

theorem simple_claim_degree (table : Fin 1024 → F) (z : Fin 10 → F)
    (j : Fin 10) (which : Fin 3) (hwhich : which.val≠1) :
    (claimPolynomial table z j which).natDegree ≤ 1 := by
  apply natDegree_sum_le_of_forall_le
  intro r _
  apply natDegree_mul_le.trans
  simpa only [natDegree_C,zero_add] using simple_tensor_degree z j which.val r.val hwhich

#print axioms simple_point_degree
#print axioms simple_tensor_degree
#print axioms simple_claim_degree
end
end AspisR19.R376SimplePointDegree
