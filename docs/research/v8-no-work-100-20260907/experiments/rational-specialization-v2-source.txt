import RationalHelperIdentity

/-! Classify ALL polynomial horizontal roots of the retained helper pole
control.  The former identity regression alone did not bound its accepting
specializations.  At a nonzero gamma the only polynomial candidate is zero,
and it exists precisely at gamma=b. No finite-field enumeration. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 100000
namespace AspisV8.RationalHelperSpecialization
open Polynomial AspisV8.RationalHelperIdentity
noncomputable section
variable {K : Type*} [Field K]

theorem polynomial_root_iff (a b gamma : K) (nonzero : gamma ≠ 0) (U : K[X]) :
    (X-C a)*U = C ((numerator b).eval gamma) ↔ gamma=b ∧ U=0 := by
  constructor
  · intro equation
    have atPole := congrArg (Polynomial.eval a) equation
    have numeratorZero : (numerator b).eval gamma = 0 := by
      simpa only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, sub_self, zero_mul] using atPole.symm
    have gammaEq : gamma=b := by
      simp only [numerator, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_sub, Polynomial.eval_C] at numeratorZero
      exact sub_eq_zero.mp ((mul_eq_zero.mp numeratorZero).resolve_left (pow_ne_zero 26 nonzero))
    have uzero : U=0 := by
      rw [numeratorZero, Polynomial.C_0] at equation
      exact (mul_eq_zero.mp equation).resolve_left (Polynomial.X_sub_C_ne_zero a)
    exact ⟨gammaEq, uzero⟩
  · rintro ⟨rfl, rfl⟩
    simp [numerator]

theorem good_nonzero_card_le_one (a b : K) (G : Finset K)
    (good : ∀ gamma∈G, gamma≠0 ∧ ∃ U : K[X],
      (X-C a)*U = C ((numerator b).eval gamma)) : G.card ≤ 1 := by
  classical
  have subset : G ⊆ {b} := by
    intro gamma member
    obtain ⟨nonzero, U, equation⟩ := good gamma member
    exact Finset.mem_singleton.mpr ((polynomial_root_iff a b gamma nonzero U).mp equation).1
  simpa only [Finset.card_singleton] using Finset.card_le_card subset

#print axioms polynomial_root_iff
#print axioms good_nonzero_card_le_one
end
end AspisV8.RationalHelperSpecialization
