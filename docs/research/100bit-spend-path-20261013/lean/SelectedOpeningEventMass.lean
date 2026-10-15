import R1SelectedOpeningEvents
import R1SelectedChallengeMap

/-! Independent-answer masses for the selected staged opening events.
All word, functional, payload and earlier-challenge inputs are fixed here.
This is not the arbitrary-prefix D2 theorem or a shared-oracle reduction.
-/
set_option autoImplicit false
noncomputable section
namespace AspisR1.SelectedOpeningEventMass

open AspisPool.AlgorithmicCircleDecoderV7
open AspisV8R19.SourceDuplexStep
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisR1.SelectedOpeningStages AspisR1.SelectedOpeningEvents

theorem gamma_ne_zero (s : State) : SelectedChallengeMap.sigma 27 s ≠ 0 := by
  rw [SelectedChallengeMap.gamma_row]
  exact OpeningSamplerBound.gammaSample_ne_zero
    SelectedSamplerRanks.stateRank R0C.ModuloField.nonzeroRank s

theorem gamma_mass (W : Fin 29 → InitialWord E) (F : Fin 6 → Functional)
    (p : Gamma) :
    mean (fun s : State => indicator
      (SelectedChallengeMap.sigma 27 s ∈ gammaBad W F p)) ≤
      (336869026622539 : ℚ) * OpeningSamplerBound.gammaAtom := by
  simp_rw [SelectedChallengeMap.gamma_row]
  exact OpeningSamplerBound.gamma_mass_le SelectedSamplerRanks.stateRank
    R0C.ModuloField.nonzeroRank W F (claims p)

theorem kappa_mass (W : Fin 29 → InitialWord E) (F : Fin 6 → Functional)
    (F0 : Functional) (p : Kappa) (gamma : E) :
    mean (fun s : State => indicator
      (SelectedChallengeMap.sigma 28 s ∈ kappaBad W F F0 p gamma)) ≤
      (600 : ℚ) * OpeningSamplerBound.atom := by
  simp_rw [SelectedChallengeMap.opening_row 28 (by omega)]
  exact OpeningSamplerBound.kappa_mass_le SelectedSamplerRanks.stateRank
    R0C.ModuloField.fieldRank W F F0 (claims p.toGamma) p.row28 gamma

theorem first_mass (W : Fin 29 → InitialWord E) (F : Fin 6 → Functional)
    (F0 : Functional) (p : First) (gamma kappa : E) :
    mean (fun s : State => indicator
      (SelectedChallengeMap.sigma 29 s ∈ firstBad W F F0 p gamma kappa)) ≤
      (9396508281846 : ℚ) * OpeningSamplerBound.atom := by
  simp_rw [SelectedChallengeMap.opening_row 29 (by omega)]
  exact OpeningSamplerBound.first_mass_le SelectedSamplerRanks.stateRank
    R0C.ModuloField.fieldRank W gamma (FunctionalWeights.weights F F0 kappa)
    (OpeningPolynomialView.firstPolynomial p.row29)
    (OpeningPolynomialView.firstPolynomial_natDegree_le p.row29)

theorem second_mass (W : Fin 29 → InitialWord E) (V : FinalWord E)
    (F : Fin 6 → Functional) (F0 : Functional) (p : Second)
    (gamma kappa alpha0 : E) :
    mean (fun s : State => indicator
      (SelectedChallengeMap.sigma 30 s ∈ secondBad W V F F0 p gamma kappa alpha0)) ≤
      (9396508281846 : ℚ) * OpeningSamplerBound.atom := by
  simp_rw [SelectedChallengeMap.opening_row 30 (by omega)]
  exact OpeningSamplerBound.second_mass_le SelectedSamplerRanks.stateRank
    R0C.ModuloField.fieldRank W V gamma alpha0 (FunctionalWeights.weights F F0 kappa)
    (OpeningPolynomialView.secondPolynomial p.row30)
    (OpeningPolynomialView.secondPolynomial_natDegree_le p.row30)

#print axioms gamma_ne_zero
#print axioms gamma_mass
#print axioms kappa_mass
#print axioms first_mass
#print axioms second_mass

end AspisR1.SelectedOpeningEventMass
end
