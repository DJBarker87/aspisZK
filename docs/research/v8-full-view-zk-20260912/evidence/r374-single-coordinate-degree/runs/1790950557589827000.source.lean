import AspisV8R19.SourceStatementPoints
import Mathlib.Algebra.Polynomial.BigOperators

/-! Symbolic one-coordinate degree bounds for the maintained statement-point
model. A successor multilinear opening need not be affine. This is not a
Rust execution refinement or a complete selected-terminal degree proof. -/
set_option autoImplicit false
namespace AspisR19.R374SingleCoordinateDegree
open Polynomial ResidualModel
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F]

def line (z : Fin 10 → F) (j : Fin 10) : Fin 10 → F[X] :=
  Function.update (fun i => C (z i)) j X

theorem line_eval (z : Fin 10 → F) (j i : Fin 10) (x : F) :
    (line z j i).eval x=Function.update z j x i := by
  by_cases h : i=j <;> simp [line,Function.update_apply,h]

theorem line_degree (z : Fin 10 → F) (j i : Fin 10) :
    (line z j i).natDegree ≤ if i=j then 1 else 0 := by
  by_cases h : i=j <;> simp [line,Function.update_apply,h]

theorem carry_degree (z : Fin 10 → F) (j i : Fin 10) :
    (carry (line z j) i).natDegree ≤ if i.val<j.val then 1 else 0 := by
  unfold carry
  by_cases h : i.val<j.val
  · rw [if_pos h]
    apply (natDegree_prod_le _ _).trans
    calc
      _ ≤ ∑ k : Fin 10, (if k=j then 1 else 0 : Nat) := by
        apply Finset.sum_le_sum
        intro k _
        by_cases hk : i.val<k.val
        · simp only [if_pos hk]
          exact line_degree z j k
        · simp [hk]
      _ = 1 := by simp
  · rw [if_neg h]
    apply (natDegree_prod_le _ _).trans
    have hz : ∀ k : Fin 10,
        (if i.val<k.val then line z j k else 1).natDegree=0 := by
      intro k
      by_cases hk : i.val<k.val
      · have hkj : k≠j := by intro he; subst k; exact h hk
        simp [hk,line,Function.update_apply,hkj]
      · simp [hk]
    simp only [hz,Finset.sum_const_zero,le_refl]

theorem point_degree (z : Fin 10 → F) (j : Fin 10) (which : Nat) (i : Fin 10) :
    (point (line z j) which i).natDegree ≤ 1 := by
  have hz : (line z j i).natDegree ≤ 1 :=
    (line_degree z j i).trans (by split_ifs <;> omega)
  have hc : (carry (line z j) i).natDegree ≤ 1 :=
    (carry_degree z j i).trans (by split_ifs <;> omega)
  have hp : (line z j i*carry (line z j) i).natDegree ≤ 1 := by
    apply natDegree_mul_le.trans
    by_cases h : i=j
    · subst i
      have hh := carry_degree z j j
      simp only [lt_self_iff_false,if_false] at hh
      have hz' := line_degree z j j
      simp only [if_true] at hz'
      omega
    · have hz' := line_degree z j i
      rw [if_neg h] at hz'
      omega
  have htwo : (2*line z j i*carry (line z j) i).natDegree ≤ 1 := by
    rw [mul_assoc]
    apply natDegree_mul_le.trans
    have h2 : (2 : F[X]).natDegree=0 := by
      change (C (2:F)).natDegree=0
      simp
    rw [h2]
    simpa only [zero_add] using hp
  unfold point
  split_ifs
  · exact hz
  · exact natDegree_sub_le_of_degree_le
      (natDegree_add_le_of_degree_le hz hc) htwo
  · exact natDegree_sub_le_of_degree_le (by simp) hz
  · exact hz

theorem tensor_degree (z : Fin 10 → F) (j : Fin 10) (which r : Nat) :
    (tensor (point (line z j) which) r).natDegree ≤ 10 := by
  unfold tensor
  apply (natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ i : Fin 10, (1 : Nat) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · exact natDegree_sub_le_of_degree_le (by simp) (point_degree z j which i)
      · exact point_degree z j which i
    _ = 10 := by simp

def claimPolynomial (table : Fin 1024 → F) (z : Fin 10 → F)
    (j : Fin 10) (which : Fin 3) : F[X] :=
  ∑ r : Fin 1024, C (table r)*tensor (point (line z j) which.val) r.val

theorem claim_degree (table : Fin 1024 → F) (z : Fin 10 → F)
    (j : Fin 10) (which : Fin 3) :
    (claimPolynomial table z j which).natDegree ≤ 10 := by
  apply natDegree_sum_le_of_forall_le
  intro r _
  apply natDegree_mul_le.trans
  simpa only [natDegree_C,zero_add] using tensor_degree z j which.val r.val

theorem claim_eval (table : Fin 1024 → F) (z : Fin 10 → F)
    (j : Fin 10) (which : Fin 3) (x : F) :
    (claimPolynomial table z j which).eval x=
      ∑ r : Fin 1024, table r * AspisV8R17.sourcePointBasis
        (SourceStatementPoints.points (Function.update z j x) which) r.val := by
  rw [SourceStatementPoints.points_eq]
  simp only [claimPolynomial,eval_finsetSum,eval_mul,eval_C,FullPointFunctional.source_tensor]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  change (evalRingHom x) (tensor (point (line z j) which.val) r.val)=_
  simp only [tensor,map_prod,apply_ite,map_sub,map_one,ResidualModel.map_point]
  have he : (fun k => (evalRingHom x) (line z j k))=Function.update z j x := by
    funext k
    exact line_eval z j k x
  rw [he]

#print axioms line_eval
#print axioms line_degree
#print axioms carry_degree
#print axioms point_degree
#print axioms tensor_degree
#print axioms claim_degree
#print axioms claim_eval
end
end AspisR19.R374SingleCoordinateDegree
