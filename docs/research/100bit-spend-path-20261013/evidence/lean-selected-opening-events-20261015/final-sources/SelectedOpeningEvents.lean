import R1SelectedOpeningStages
import R1SelectedOpeningClaims
import R1OpeningPolynomialView
import R1ConcreteBinding

/-! Fixed-input opening bad sets on the staged payload views. The word and
functional arguments remain explicit. Their causal recovery and the complete
round-by-round classifier are not established by these cardinality bounds.
-/
set_option autoImplicit false
noncomputable section
namespace AspisR1.SelectedOpeningEvents

open AspisPool.AlgorithmicCircleDecoderV7
open AspisR1.SelectedOpeningStages
abbrev E := AspisWideTower.WideExact
abbrev Functional := ConcreteBinding.Functional E

def claims (p : Gamma) : Fin 6 → Fin 29 → E :=
  SelectedOpeningClaims.Y p.row25 p.row26 p.row27

def gammaBad (W : Fin 29 → InitialWord E) (F : Fin 6 → Functional)
    (p : Gamma) : Finset E := ConcreteBinding.gammaBad W F (claims p)

def kappaBad (W : Fin 29 → InitialWord E) (F : Fin 6 → Functional)
    (F0 : Functional) (p : Kappa) (gamma : E) : Finset E :=
  ConcreteBinding.kappaBad W F F0 (claims p.toGamma) p.row28 gamma

def firstBad (W : Fin 29 → InitialWord E) (F : Fin 6 → Functional)
    (F0 : Functional) (p : First) (gamma kappa : E) : Finset E :=
  ConcreteBinding.firstBad W gamma (FunctionalWeights.weights F F0 kappa)
    (OpeningPolynomialView.firstPolynomial p.row29)

def secondBad (W : Fin 29 → InitialWord E) (V : FinalWord E)
    (F : Fin 6 → Functional) (F0 : Functional) (p : Second)
    (gamma kappa alpha0 : E) : Finset E :=
  ConcreteBinding.secondBad W V gamma alpha0
    (FunctionalWeights.weights F F0 kappa)
    (OpeningPolynomialView.secondPolynomial p.row30)

theorem gammaBad_card (W : Fin 29 → InitialWord E) (F : Fin 6 → Functional)
    (p : Gamma) : (gammaBad W F p).card ≤ 336869026622539 :=
  ConcreteBinding.gammaBad_card W F (claims p)

theorem kappaBad_card (W : Fin 29 → InitialWord E) (F : Fin 6 → Functional)
    (F0 : Functional) (p : Kappa) (gamma : E) :
    (kappaBad W F F0 p gamma).card ≤ 600 :=
  ConcreteBinding.kappaBad_card W F F0 (claims p.toGamma) p.row28 gamma

theorem firstBad_card (W : Fin 29 → InitialWord E) (F : Fin 6 → Functional)
    (F0 : Functional) (p : First) (gamma kappa : E) :
    (firstBad W F F0 p gamma kappa).card ≤ 9396508281846 :=
  ConcreteBinding.firstBad_card W gamma (FunctionalWeights.weights F F0 kappa)
    (OpeningPolynomialView.firstPolynomial p.row29)
    (OpeningPolynomialView.firstPolynomial_natDegree_le p.row29)

theorem secondBad_card (W : Fin 29 → InitialWord E) (V : FinalWord E)
    (F : Fin 6 → Functional) (F0 : Functional) (p : Second)
    (gamma kappa alpha0 : E) :
    (secondBad W V F F0 p gamma kappa alpha0).card ≤ 9396508281846 :=
  ConcreteBinding.secondBad_card W V gamma alpha0
    (FunctionalWeights.weights F F0 kappa)
    (OpeningPolynomialView.secondPolynomial p.row30)
    (OpeningPolynomialView.secondPolynomial_natDegree_le p.row30)

#print axioms gammaBad_card
#print axioms kappaBad_card
#print axioms firstBad_card
#print axioms secondBad_card

end AspisR1.SelectedOpeningEvents
end
