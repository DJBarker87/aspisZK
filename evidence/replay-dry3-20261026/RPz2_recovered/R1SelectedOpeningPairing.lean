import R1SelectedOpeningData

/-! Connect explicit coefficient checks on the selected opening payloads to
the existing pairing predicate. The checks, words, functionals and challenges
are supplied inputs. No Rust execution or accepted-proof implication is proved.
-/
set_option autoImplicit false
noncomputable section
namespace AspisR1.SelectedOpeningPairing

open scoped BigOperators
open AspisR1.SelectedOpeningData AspisR1.MatchingSupport

abbrev E := AspisWideTower.WideExact

def eval7 (coefficients : Fin 7 → E) (x : E) : E :=
  ∑ i : Fin 7, coefficients i * x ^ i.val

def coefficientChecks (p : SelectedOpeningData.Payloads)
    (F : Fin 6 → Functional E) (F0 : Functional E)
    (gamma kappa alpha0 alpha1 : E) : Prop :=
  eval7 p.row30.2 alpha1 = RoundPairing.dot p.row31
    (RoundPairing.dualFold (n := 64) alpha1
      (RoundPairing.dualFold (n := 256) alpha0
        (FunctionalWeights.weights F F0 kappa))) ∧
  p.row30.2 0 + p.row30.2 4 =
    RoundPairing.quarter * eval7 p.row29 alpha0 ∧
  p.row29 0 + p.row29 4 = RoundPairing.quarter *
    (∑ j : Fin 7, kappa ^ j.val *
      SelectedOpeningClaims.parts p.row25 p.row26 p.row27 p.row28 gamma j)

theorem acceptedPairing_iff_coefficientChecks (p : SelectedOpeningData.Payloads)
    (W : Fin 29 → InitialWord E) (V : FinalWord E)
    (F : Fin 6 → Functional E) (F0 : Functional E)
    (gamma kappa alpha0 alpha1 : E) :
    MatchingSupport.AcceptedPairing
      (SelectedOpeningData.data p W V F F0 gamma kappa alpha0 alpha1) ↔
    coefficientChecks p F F0 gamma kappa alpha0 alpha1 := by
  unfold MatchingSupport.AcceptedPairing SelectedOpeningData.data
  simp only [OpeningPolynomialView.firstPolynomial_boundary,
    OpeningPolynomialView.secondPolynomial_boundary]
  simp only [OpeningPolynomialView.firstPolynomial,
    OpeningPolynomialView.secondPolynomial,
    OpeningPolynomialView.polynomial_eval]
  unfold coefficientChecks eval7
  rw [SelectedOpeningClaims.parts_weighted_sum]

#print axioms acceptedPairing_iff_coefficientChecks

end AspisR1.SelectedOpeningPairing
end
