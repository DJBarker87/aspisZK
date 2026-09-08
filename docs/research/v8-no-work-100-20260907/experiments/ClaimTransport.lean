import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-! Algebraic interfaces of the corrected research prepare(): scalar-power
batching and affine chord transport. No assumed inactive exactness or desired
discrepancy equality. The actual encoder/chord matrix port remains separate. -/
set_option autoImplicit false
namespace AspisV8.ClaimTransport
open Polynomial
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

def batch (gamma : K) (p : Fin 29 → V) : V :=
  ∑ lane, gamma ^ lane.val • p lane

noncomputable def errorPolynomial (ell : V →ₗ[K] K)
    (p : Fin 29 → V) (claimed : Fin 29 → K) : K[X] :=
  ∑ lane, Polynomial.monomial lane.val (claimed lane - ell (p lane))

theorem component_error_eval (ell : V →ₗ[K] K) (p : Fin 29 → V)
    (claimed : Fin 29 → K) (gamma : K) :
    (∑ lane, gamma^lane.val * claimed lane) - ell (batch gamma p) =
      (errorPolynomial ell p claimed).eval gamma := by
  simp only [batch, map_sum, map_smul, smul_eq_mul, errorPolynomial,
    Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem component_error_coeff (ell : V →ₗ[K] K) (p : Fin 29 → V)
    (claimed : Fin 29 → K) (lane : Fin 29) :
    (errorPolynomial ell p claimed).coeff lane.val = claimed lane - ell (p lane) := by
  simp [errorPolynomial, Polynomial.coeff_monomial, Fin.val_inj]

theorem component_error_degree (ell : V →ₗ[K] K) (p : Fin 29 → V)
    (claimed : Fin 29 → K) :
    (errorPolynomial ell p claimed).natDegree ≤ 28 := by
  unfold errorPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro lane _
  exact (Polynomial.natDegree_monomial_le _).trans (by omega)

theorem component_error_nonzero (ell : V →ₗ[K] K) (p : Fin 29 → V)
    (claimed : Fin 29 → K) (lane : Fin 29) (wrong : claimed lane ≠ ell (p lane)) :
    errorPolynomial ell p claimed ≠ 0 := by
  intro hz
  have h := component_error_coeff ell p claimed lane
  rw [hz, Polynomial.coeff_zero] at h
  exact wrong (sub_eq_zero.mp h.symm)

def ordinary (iw : V →ₗ[K] K) (rows : Fin 3 → V →ₗ[K] K) (kappa : K) :
    V →ₗ[K] K :=
  iw + kappa • rows 0 + kappa^2 • rows 1 + kappa^3 • rows 2

/-- Literal correction: inactive has power zero and all three point rows
have strictly positive powers. L and I reconstruct the original polynomial;
the transported functional is constructed by composition, not assumed. -/
theorem corrected_prepare_discrepancy
    (iw : V →ₗ[K] K) (rows : Fin 3 → V →ₗ[K] K)
    (L : W →ₗ[K] V) (Q : W) (I : V)
    (inactive kappa : K) (claimed : Fin 3 → K) :
    (inactive + kappa*claimed 0 + kappa^2*claimed 1 + kappa^3*claimed 2
      - ordinary iw rows kappa I)
      - (ordinary iw rows kappa).comp L Q =
    (inactive - iw (L Q + I))
      + kappa*(claimed 0 - rows 0 (L Q + I))
      + kappa^2*(claimed 1 - rows 1 (L Q + I))
      + kappa^3*(claimed 2 - rows 2 (L Q + I)) := by
  simp only [ordinary, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, map_add, smul_eq_mul]
  ring

/-- A pre-gamma component tuple and actual row functionals construct the
point-error polynomial interface used by gamma_then_row_near_event_bound. -/
theorem batched_prepare_discrepancy
    (iw : V →ₗ[K] K) (rows : Fin 3 → V →ₗ[K] K)
    (p : Fin 29 → V) (claimed : Fin 3 → Fin 29 → K)
    (inactive gamma kappa : K) :
    (inactive + kappa*(∑ lane, gamma^lane.val*claimed 0 lane)
      + kappa^2*(∑ lane, gamma^lane.val*claimed 1 lane)
      + kappa^3*(∑ lane, gamma^lane.val*claimed 2 lane))
      - ordinary iw rows kappa (batch gamma p) =
    (inactive - iw (batch gamma p))
      + kappa*(errorPolynomial (rows 0) p (claimed 0)).eval gamma
      + kappa^2*(errorPolynomial (rows 1) p (claimed 1)).eval gamma
      + kappa^3*(errorPolynomial (rows 2) p (claimed 2)).eval gamma := by
  rw [← component_error_eval, ← component_error_eval, ← component_error_eval]
  simp only [ordinary, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

#print axioms component_error_eval
#print axioms component_error_coeff
#print axioms component_error_degree
#print axioms component_error_nonzero
#print axioms corrected_prepare_discrepancy
#print axioms batched_prepare_discrepancy
end AspisV8.ClaimTransport
