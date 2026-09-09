import FirstImageDiscrepancy
import ClaimTransport

/-! Construct the pre-image prefix from shifted rows and affine transport.
Q, all four original covectors/claims, L and I are fixed before kappa. The
transported covector is constructed, not accompanied by an assumed dot law.
No inactiveExact, image validity, codeword coverage or witness premise. -/
set_option autoImplicit false
namespace AspisV8.ShiftedRowPrefix
open Polynomial
open AspisV5FriRelationCandidateBridge AspisV5FriConcreteEncoderApplicability
open AspisV8.FirstImageDiscrepancy
universe u
variable {K : Type u} [Field K] [DecidableEq K]

noncomputable def covector {n : Nat} (w : Fin n → K) : (Fin n → K) →ₗ[K] K where
  toFun := candidateClaim w
  map_add' f g := by
    simp [candidateClaim, add_mul, Finset.sum_add_distrib]
  map_smul' a f := by
    simp [candidateClaim, Finset.mul_sum, mul_assoc]

/-- Coefficients of an arbitrary linear functional on the canonical message
coordinates, constructed by applying it to coordinate vectors. -/
def reify {n : Nat} (ell : (Fin n → K) →ₗ[K] K) : Fin n → K :=
  fun i => ell (Pi.single i 1)

theorem reify_dot {n : Nat} (ell : (Fin n → K) →ₗ[K] K) (v : Fin n → K) :
    candidateClaim (reify ell) v=ell v := by
  have hv : (∑ i, v i • Pi.single i (1 : K))=v := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul]
  calc
    candidateClaim (reify ell) v = ∑ i, v i*ell (Pi.single i 1) := rfl
    _ = ell (∑ i, v i • Pi.single i (1 : K)) := by simp [map_sum, map_smul]
    _ = ell v := congrArg ell hv

structure Rows where
  original : Fin 4 → Fin 1024 → K
  claimed : Fin 4 → K
  reconstruction : (Fin 1024 → K) →ₗ[K] (Fin 1024 → K)
  interpolant : Fin 1024 → K
  referenceQ : Fin 1024 → K
  quarter : K
  b : K
  c : K

noncomputable def Rows.functional (r : Rows (K := K)) (j : Fin 4) :
    (Fin 1024 → K) →ₗ[K] K := covector (r.original j)
noncomputable def Rows.ordinaryFunctional (r : Rows (K := K)) (kappa : K) :
    (Fin 1024 → K) →ₗ[K] K :=
  ClaimTransport.ordinary (r.functional 0) (fun j : Fin 3 => r.functional j.succ) kappa
noncomputable def Rows.correctedClaim (r : Rows (K := K)) (kappa : K) : K :=
  r.claimed 0+kappa*r.claimed 1+kappa^2*r.claimed 2+kappa^3*r.claimed 3
    -r.ordinaryFunctional kappa r.interpolant
noncomputable def Rows.transportedWeight (r : Rows (K := K)) (kappa : K) : Fin 1024 → K :=
  reify ((r.ordinaryFunctional kappa).comp r.reconstruction)
noncomputable def Rows.errors (r : Rows (K := K)) : Fin 4 → K :=
  fun j => r.claimed j-r.functional j (r.reconstruction r.referenceQ+r.interpolant)
noncomputable def Rows.errorPolynomial (r : Rows (K := K)) : K[X] :=
  monomialPolynomial r.errors

/-- Both scalar and transported functional are constructed from the same
shifted original rows, with their actual affine interpolant subtraction. -/
noncomputable def Rows.before (r : Rows (K := K)) (kappa : K) : Before (K := K) where
  ordinary := r.transportedWeight kappa
  referenceQ := r.referenceQ
  claim := r.correctedClaim kappa
  quarter := r.quarter
  b := r.b
  c := r.c

theorem transported_dot (r : Rows (K := K)) (kappa : K) :
    candidateClaim (r.transportedWeight kappa) r.referenceQ =
      r.ordinaryFunctional kappa (r.reconstruction r.referenceQ) :=
  reify_dot ((r.ordinaryFunctional kappa).comp r.reconstruction) r.referenceQ

/-- Reuse the existing corrected affine transport lemma. Its inactive
coefficient is kept in the constant term and is not assumed exact. -/
theorem before_prior_cubic (r : Rows (K := K)) (kappa : K) :
    (r.before kappa).prior =
      r.errors 0+kappa*r.errors 1+kappa^2*r.errors 2+kappa^3*r.errors 3 := by
  unfold Before.prior Rows.before
  dsimp only
  rw [transported_dot]
  exact ClaimTransport.corrected_prepare_discrepancy
    (r.functional 0) (fun j : Fin 3 => r.functional j.succ)
    r.reconstruction r.referenceQ r.interpolant (r.claimed 0) kappa
    (fun j : Fin 3 => r.claimed j.succ)

theorem four_coefficient_eval (e : Fin 4 → K) (kappa : K) :
    (monomialPolynomial e).eval kappa=e 0+kappa*e 1+kappa^2*e 2+kappa^3*e 3 := by
  simp [monomialPolynomial, Fin.sum_univ_succ]
  ring

theorem before_prior (r : Rows (K := K)) (kappa : K) :
    (r.before kappa).prior=r.errorPolynomial.eval kappa := by
  rw [before_prior_cubic]
  exact (four_coefficient_eval r.errors kappa).symm

theorem error_degree (r : Rows (K := K)) : r.errorPolynomial.natDegree ≤ 3 :=
  monomialPolynomial_natDegree_le (by decide) r.errors

theorem error_coeff (r : Rows (K := K)) (j : Fin 4) :
    r.errorPolynomial.coeff j.val=r.errors j := monomialPolynomial_coeff r.errors j

theorem error_nonzero (r : Rows (K := K)) (wrong : r.errors ≠ 0) :
    r.errorPolynomial ≠ 0 := by
  intro hz
  apply wrong
  funext j
  have hc := error_coeff r j
  rw [hz, Polynomial.coeff_zero] at hc
  exact hc.symm

theorem before_E1 (r : Rows (K := K)) (kappa : K) :
    (r.before kappa).E1=r.referenceQ ⟨1023, by decide⟩ := rfl
theorem before_E2 (r : Rows (K := K)) (kappa : K) :
    (r.before kappa).E2=r.b*r.referenceQ ⟨1022, by decide⟩-r.c*r.referenceQ ⟨1021, by decide⟩ := rfl
theorem before_quarter (r : Rows (K := K)) (kappa : K) :
    (r.before kappa).quarter=r.quarter := rfl
theorem before_referenceQ (r : Rows (K := K)) (kappa : K) :
    (r.before kappa).referenceQ=r.referenceQ := rfl

#print axioms reify_dot
#print axioms transported_dot
#print axioms before_prior_cubic
#print axioms four_coefficient_eval
#print axioms before_prior
#print axioms error_degree
#print axioms error_coeff
#print axioms error_nonzero
#print axioms before_E1
#print axioms before_E2
#print axioms before_quarter
#print axioms before_referenceQ
end AspisV8.ShiftedRowPrefix
