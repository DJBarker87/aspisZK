import AspisV8R19.R381ProjectedPoseidonDegree

/-! The selected positive-transfer scalar expression in the maintained
point-polynomial model. Actual source evaluation and field-word packing
remain separate obligations. -/
set_option autoImplicit false
namespace AspisR19.R384PositiveDeltaDegree
open Polynomial R374SingleCoordinateDegree R376SimplePointDegree R381ProjectedPoseidonDegree
open AspisV8R19.R377SelectorCoordinateDegree
noncomputable section
variable {F : Type*} [Field F]

def residual (tables : Fin 16 → Fin 1024 → F) (z : Fin 10 → F) (j : Fin 10) : F[X] :=
  claimPolynomial (tables 1) z j 0*claimPolynomial (tables 1) z j 1*
    claimPolynomial (tables 3) z j 0-1

theorem residual_degree (tables : Fin 16 → Fin 1024 → F) (z : Fin 10 → F)
    (j : Fin 10) : (residual tables z j).natDegree ≤ 12 := by
  apply sub_bound _ (by simp)
  apply natDegree_mul_le.trans
  have h0 := simple_claim_degree (tables 1) z j 0 (by decide)
  have h1 := claim_degree (tables 1) z j 1
  have h3 := simple_claim_degree (tables 3) z j 0 (by decide)
  have hp := natDegree_mul_le (p:=claimPolynomial (tables 1) z j 0)
    (q:=claimPolynomial (tables 1) z j 1)
  omega

def rowSelector (z : Fin 10 → F) (j : Fin 10) : F[X] :=
  selectorPolynomial Finset.univ (fun i => decide ((1014/2^(9-i.val))%2=1)) z j

theorem rowSelector_degree (z : Fin 10 → F) (j : Fin 10) :
    (rowSelector z j).natDegree ≤ 1 := by
  simpa only [rowSelector,Finset.mem_univ,if_true] using selectorPolynomial_degree
    Finset.univ (fun i => decide ((1014/2^(9-i.val))%2=1)) z j

def delta (tables : Fin 16 → Fin 1024 → F) (z zc : Fin 10 → F) (j : Fin 10)
    (theta eta limb2 : F) : F[X] :=
  C (eta*theta^27*limb2)*(equality z zc j*(rowSelector z j*residual tables z j))

theorem delta_degree (tables : Fin 16 → Fin 1024 → F) (z zc : Fin 10 → F)
    (j : Fin 10) (theta eta limb2 : F) :
    (delta tables z zc j theta eta limb2).natDegree ≤ 14 := by
  have hr := natDegree_mul_le.trans
    (Nat.add_le_add (rowSelector_degree z j) (residual_degree tables z j))
  have he := natDegree_mul_le.trans (Nat.add_le_add (equality_degree z zc j) hr)
  apply natDegree_mul_le.trans
  simpa only [natDegree_C,zero_add] using he

#print axioms residual_degree
#print axioms rowSelector_degree
#print axioms delta_degree
end
end AspisR19.R384PositiveDeltaDegree
