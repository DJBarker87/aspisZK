import QuadraticSourceDichotomy

/-! Preserve the square-part degree factor in the source quadratic
alternative. The fixed obstruction is the same actual H coefficient;
only the exported degree budget is strengthened. No sampler or query
law is supplied and the committed dichotomy is not changed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.QuadraticSourceSharp
open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementRegularWeights
open AspisK1.V7ExactCorrelatedAgreementFactorBudgets
noncomputable section
variable {K : Type*} [Field K] [NeZero (2 : K)]

/-- Keep the actual leading-Z coefficient of H, its support-derived
degree bound, and the sharp consequence of D=H^2*R with nonzero factors. -/
theorem constant_obstruction_sharp
    (F : TrivariatePolynomial K) (irreducible : Irreducible F)
    (degree : F.natDegree = 2) (H R : Polynomial K[X])
    (hNonzero : H ≠ 0) (rNonzero : R ≠ 0)
    (decomposition : QuadraticFactorSource.discriminant F = H^2*R)
    (constant : R.natDegree = 0) :
    ∃ E : K[X], E ≠ 0 ∧ E = (Polynomial.Bivariate.swap H).leadingCoeff ∧
      E.natDegree ≤ H.natDegree ∧
      2*E.natDegree ≤ (QuadraticFactorSource.discriminant F).natDegree ∧
      ∀ (points : Fin 2 → K) (answers : Fin 2 → K[X]),
        (∀ r, FactorCoherence.pointSubstitution (points r) (answers r) F = 0) →
        ∀ r, E.eval (points r) = 0 := by
  obtain ⟨E, nonzero, supportBound, chosen, forces⟩ :=
    QuadraticConstantParity.source_fixed_obstruction F irreducible degree H R
      ((QuadraticSourceDichotomy.discriminant_order F).trans decomposition) constant
  refine ⟨E, nonzero, chosen, supportBound, ?_, forces⟩
  have exactDegree := congrArg Polynomial.natDegree decomposition
  rw [Polynomial.natDegree_mul (pow_ne_zero 2 hNonzero) rNonzero,
    Polynomial.natDegree_pow] at exactDegree
  omega

/-- Both branches are fixed from F before OOD points, answers, gamma
sets or adaptive polynomial candidates. This strengthens only the
obstruction degree bound, retaining the previous all-root gamma bound. -/
theorem fixed_source_alternative (p curveDegree : Nat) [CharP K p]
    (F : TrivariatePolynomial K) (irreducible : Irreducible F)
    (degree : F.natDegree = 2)
    (small : (QuadraticFactorSource.discriminant F).natDegree < p) :
    (∃ E : K[X], E ≠ 0 ∧
      2*E.natDegree ≤ (QuadraticFactorSource.discriminant F).natDegree ∧
      ∀ (points : Fin 2 → K) (answers : Fin 2 → K[X]),
        (∀ r, FactorCoherence.pointSubstitution (points r) (answers r) F = 0) →
        ∀ r, E.eval (points r) = 0) ∨
    (∀ G : Finset K,
      (∀ gamma ∈ G, ∃ U : K[X], challengeCandidateHom gamma U F = 0) →
      G.card ≤ 8*trivariateYZWeight curveDegree F) := by
  obtain ⟨H, R, hn, rn, identity, _, alternatives⟩ :=
    QuadraticConstructedParity.exists_fixed_parity_dichotomy p
      (Polynomial.Bivariate.swap (F.coeff 2))
      (Polynomial.Bivariate.swap (F.coeff 1))
      (Polynomial.Bivariate.swap (F.coeff 0))
      (QuadraticSourceDichotomy.discriminant_nonzero F irreducible degree) small
  change QuadraticFactorSource.discriminant F = H^2*R at identity
  rcases alternatives with constant | bounded
  · left
    obtain ⟨E, en, _, _, sharp, forces⟩ :=
      constant_obstruction_sharp F irreducible degree H R hn rn identity constant
    exact ⟨E, en, sharp, forces⟩
  · right
    intro G roots
    have counted := bounded G (fun gamma member => by
      obtain ⟨U, root⟩ := roots gamma member
      exact QuadraticFactorSource.candidate_root F degree gamma U root)
    have weight := QuadraticFactorSource.discriminant_degree_le_weight F curveDegree
    change G.card ≤ 4*(Polynomial.Bivariate.swap (QuadraticFactorSource.discriminant F)).natDegree
      at counted
    omega

#print axioms constant_obstruction_sharp
#print axioms fixed_source_alternative
end
end AspisV8.QuadraticSourceSharp
