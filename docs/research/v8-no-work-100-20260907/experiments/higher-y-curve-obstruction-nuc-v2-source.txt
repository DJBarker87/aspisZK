import FactorIdentityCover

/-! Draft, not checked: the last algebraic step in a direct-incidence
argument for higher-Y factors. A prime factor of Y-degree at least two
cannot have a polynomial-in-Z component curve as a global root. Hence a
degree-c curve can satisfy that factor at at most its (Z+cY)-weight many
distinct challenges. This does NOT supply that curve for arbitrary selected
candidates: the intended predecessor is V7's actual fixed-branch incidence
theorem. No regularity, source agreement, or family-coverage premise is
silently discharged here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.HigherYCurveObstruction
open Polynomial Finset
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementFactorBudgets
open AspisK1.V7ExactCorrelatedAgreementRegularWeights
noncomputable section

/-- The degree proof works over the coefficient domain K[X], not just a
field. X receives weight zero; the middle Z remains the polynomial variable. -/
theorem eval_degree_le_weight {R : Type*} [CommRing R] [IsDomain R]
    (c : Nat) (F : Polynomial (Polynomial R)) (curve : Polynomial R)
    (small : curve.natDegree <= c) :
    (F.eval curve).natDegree <= localBivariateWeight c F := by
  classical
  have expanded : F.eval curve =
      ∑ j ∈ F.support, F.coeff j * curve^j := by
    calc
      F.eval curve = (∑ j ∈ F.support, monomial j (F.coeff j)).eval curve :=
        congrArg (fun P : Polynomial (Polynomial R) => P.eval curve) F.as_sum_support
      _ = _ := by simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  rw [expanded]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j member
  exact Polynomial.natDegree_mul_le.trans <|
    (Nat.add_le_add_left (Polynomial.natDegree_pow_le.trans
      (Nat.mul_le_mul_left j small)) _).trans
        (coeff_weight_le_localBivariateWeight c F j member)

variable {K : Type*} [Field K]

theorem specialize_curve (F : TrivariatePolynomial K)
    (curve : Polynomial K[X]) (gamma : K) :
    challengeCandidateHom gamma (curve.eval (C gamma)) F =
      (F.eval curve).eval (C gamma) := by
  change (F.map (Polynomial.evalRingHom (C gamma))).eval
    (curve.eval (C gamma)) = _
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply (Polynomial.evalRingHom (C gamma)) curve

/-- This is a contradiction for a fixed polynomial curve, not an
assumption that adaptive horizontal candidates already lie on one curve. -/
theorem prime_curve_nonzero (F : TrivariatePolynomial K)
    (prime : Prime F) (higher : 2 <= F.natDegree) (curve : Polynomial K[X]) :
    F.eval curve ≠ 0 :=
  prime.irreducible.not_isRoot_of_natDegree_ne_one (by omega)

/-- Distinct gamma values remain distinct as constants in K[X]. Thus the
ordinary integral-domain root count applies directly, without enumerating
the field or evaluating all X coordinates. -/
theorem coherent_specializations_card (c : Nat) (F : TrivariatePolynomial K)
    (prime : Prime F) (higher : 2 <= F.natDegree)
    (curve : Polynomial K[X]) (small : curve.natDegree <= c)
    (selected : Finset K)
    (roots : ∀ gamma ∈ selected,
      challengeCandidateHom gamma (curve.eval (C gamma)) F = 0) :
    selected.card <= trivariateYZWeight c F := by
  classical
  have nonzero := prime_curve_nonzero F prime higher curve
  have bound : (selected.image (Polynomial.C : K -> K[X])).card <=
      (F.eval curve).natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro value member
    obtain ⟨gamma, gammaMember, rfl⟩ := Finset.mem_image.mp member
    apply (Polynomial.mem_roots nonzero).mpr
    exact (specialize_curve F curve gamma).symm.trans (roots gamma gammaMember)
  rw [Finset.card_image_of_injective selected Polynomial.C_injective] at bound
  exact bound.trans (eval_degree_le_weight c F curve small)

#print axioms eval_degree_le_weight
#print axioms specialize_curve
#print axioms prime_curve_nonzero
#print axioms coherent_specializations_card
end
end AspisV8.HigherYCurveObstruction
