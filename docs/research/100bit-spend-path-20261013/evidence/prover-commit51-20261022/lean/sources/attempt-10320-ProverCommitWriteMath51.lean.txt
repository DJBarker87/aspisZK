import R1Z.ProverCommitMaskWrites51
import Mathlib.Algebra.Polynomial.BigOperators
/-! Symbolic overwrite invariant: untouched cells and scheduled cells suffice. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitWriteMath51
open scoped BigOperators
open ProverCommitMaskWrites51
variable {K : Type}

theorem fill_eq (e : Nat → Nat) (v t : Nat → K)
    (hv : ∀ i, i < 26 → v i=t (e i)) (n : Nat) (hn : n≤26)
    (q : Nat → K)
    (hq : ∀ k, (∀ i, 26 - n ≤ i → i < 26 → e i ≠ k) → q k=t k) :
    fill e v n q=t := by
  induction n generalizing q with
  | zero =>
    funext k
    exact hq k (by intro i hi hb;omega)
  | succ n ih =>
    change fill e v n (Function.update q (e (26-(n+1))) (v (26-(n+1))))=t
    apply ih (by omega)
    intro k hk
    by_cases h : k=e (26-(n+1))
    · rw [h,Function.update_self,hv _ (by omega)]
    · rw [Function.update_of_ne h]
      apply hq k
      intro i hi hib
      by_cases hstart : i=26-(n+1)
      · rw [hstart];exact Ne.symm h
      · exact hk i (by omega) hib

section Field
variable [Field K]

def polynomial (e : Fin 26 → Nat) (v : Fin 26 → K) : Polynomial K :=
  ∑ i, Polynomial.monomial (e i) (v i)

theorem coeff_at (e : Fin 26 → Nat) (v : Fin 26 → K)
    (he : Function.Injective e) (i : Fin 26) :
    (polynomial e v).coeff (e i)=v i := by
  classical
  simp only [polynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial]
  have h (j : Fin 26) : e j=e i ↔ j=i := he.eq_iff
  simp only [h,Finset.sum_ite_eq',Finset.mem_univ,if_true]

theorem coeff_outside (e : Fin 26 → Nat) (v : Fin 26 → K)
    (k : Nat) (hk : ∀ i, e i ≠ k) :
    (polynomial e v).coeff k=0 := by
  simp only [polynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial,hk,if_false,Finset.sum_const_zero]
end Field

#print axioms fill_eq
#print axioms coeff_at
#print axioms coeff_outside
end R1Z.ProverCommitWriteMath51
