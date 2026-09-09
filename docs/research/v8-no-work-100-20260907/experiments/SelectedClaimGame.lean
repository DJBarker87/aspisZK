import SelectedComponentGame
import ComponentOODBinding

/-! One constructed pre-gamma tuple binds either an incorrect ordinary
component point claim OR an incorrect component OOD answer. One wrong
claim is chosen from the fixed prefix; no union over 145 claims or 100
targets is needed. The event remains actual compact acceptance with an
actual folded final at distance≤2324, not global witness extraction. -/
set_option autoImplicit false
set_option maxRecDepth 200
set_option maxHeartbeats 300000
namespace AspisV8.SelectedClaimGame
open Finset
open AspisV8.SelectedReceivedOracle AspisV8.GammaComponentGame
open AspisV8.SelectedComponentGame AspisV8.ComponentOODBinding
open AspisV8.OODInterpolant AspisV8.CausalOrderedRelation
open AspisV8.ShiftedRowPrefix AspisV8.JointImageGame AspisV8.ClaimTransport
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.PartialFoldRecovery AspisV8.NearGammaSelectedCoefficients
open AspisPool.V7C1ConcreteProjectionBinding
noncomputable section
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
noncomputable local instance : Fintype (Fin 262144) :=
  AspisV8.EarlyC1Specialization.explicit_instance

/-- The OOD functional and answer vector do not depend on gamma; overwriting
only the gamma field preserves both literally. -/
theorem ood_error_atGamma (data : Data (K := K)) (gamma : K)
    (p : Fin 29 → Message) (r : Fin 2) :
    errorPolynomial (circleFunctional (pointX (atGamma data gamma) r)
      (pointY (atGamma data gamma) r)) p ((atGamma data gamma).answers r)=
      errorPolynomial (circleFunctional (pointX data r) (pointY data r)) p (data.answers r) := rfl

/-- Deterministic coverage here is supplied by the constructed selected
cover in all_claims_dichotomy below, never assumed from acceptance. -/
theorem wrong_ood_near_bound {q : Nat}
    (c1 : C1Received) (c2 : C2Received) (Gamma : Finset K)
    (p : Fin 29 → Message)
    (cover : ∀ gamma∈Gamma, ∀ message : Message,
      (fibreBad (m := 262144) (exactInitialEncoder message)
        (NearGammaSelectedC1.rawBatch c1 c2 gamma)).card≤9301 →
      message=NearGammaMessageCover.batch p gamma)
    (data : Data (K := K)) (checked : data.Checked)
    (circles : data.x0^2+data.y0^2=1 ∧ data.x1^2+data.y1^2=1)
    (quarter : K) (hq : quarter*4=1) (w : Fin 4 → Fin 1024 → K)
    (claimed : Fin 3 → Fin 29 → K) (inactive : K → K)
    (strategy : K → K → Strategy domain q) (A G : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (hgamma : Gamma.Nonempty)
    (hpos : 0<q) (hcount : q≤domain.card) (r : Fin 2) (lane : Fin 29)
    (wrong : data.answers r lane≠circleFunctional (pointX data r) (pointY data r) (p lane)) :
    avg Gamma (fun gamma => nearProbability data quarter hq w claimed inactive
      (received c1 c2 data) 2324 strategy gamma A G)≤
      28/Gamma.card+((q:ℚ)+3)/G.card+24/A.card := by
  let ell := circleFunctional (pointX data r) (pointY data r)
  have h := avg_polynomial Gamma hgamma (errorPolynomial ell p (data.answers r))
    (component_error_nonzero ell p (data.answers r) lane wrong) 28
    (component_error_degree ell p (data.answers r))
    (fun gamma => nearProbability data quarter hq w claimed inactive
      (received c1 c2 data) 2324 strategy gamma A G)
    (((q:ℚ)+3)/G.card+24/A.card) (by positivity)
    (fun gamma _ => SelectedComponentGame.unit c1 c2 data quarter hq w claimed inactive
      strategy gamma A G ha hg hcount)
    (by
      intro gamma hgam nonzero
      apply near_bound_of_wrong_rows data quarter hq w claimed inactive (received c1 c2 data)
        2324 strategy gamma A G ha hg hpos hcount (by norm_num)
      intro Q close h1 h2
      have recovered : (atGamma data gamma).original Q=ClaimTransport.batch gamma p :=
        cover gamma hgam _ (close_original c1 c2 data checked gamma Q close h1 h2)
      have zero := recovered_ood_error_eval (atGamma data gamma)
        (checked_atGamma data checked gamma) Q ⟨h1,h2⟩ circles p recovered r
      rw [ood_error_atGamma] at zero
      exact False.elim (nonzero zero))
  simpa only [add_assoc,Nat.cast_ofNat] using h

/-- A SINGLE p is constructed before all claim/point/strategy choices. The
same actual execution is bounded if any of its 3x29 ordinary claims or 2x29
OOD answers is wrong for p. Sparse coverage is still an explicit branch. -/
theorem all_claims_dichotomy (c1 : C1Received) (c2 : C2Received) (Gamma : Finset K) :
    (NearGammaSelectedC1.good c1 c2 Gamma).card<64 ∨
      ∃ p : Fin 29 → Message,
        245609≤(support fibreEncode (fibreWord29 c1 c2) p).card ∧
        earlyC1 c1=some (c1Projection p) ∧
        ∀ (q : Nat) (data : Data (K := K)), data.Checked →
        data.x0^2+data.y0^2=1 ∧ data.x1^2+data.y1^2=1 →
        ∀ (quarter : K) (hq : quarter*4=1) (w : Fin 4 → Fin 1024 → K)
          (claimed : Fin 3 → Fin 29 → K) (inactive : K → K)
          (strategy : K → K → Strategy domain q)
          (A G : Finset K), A.Nonempty → G.Nonempty → Gamma.Nonempty →
          0<q → q≤domain.card →
          ((∃ (j : Fin 3) (lane : Fin 29), claimed j lane≠covector (w j.succ) (p lane)) ∨
            ∃ (r : Fin 2) (lane : Fin 29), data.answers r lane≠
              circleFunctional (pointX data r) (pointY data r) (p lane)) →
          avg Gamma (fun gamma => nearProbability data quarter hq w claimed inactive
            (received c1 c2 data) 2324 strategy gamma A G)≤
            28/Gamma.card+((q:ℚ)+3)/G.card+24/A.card := by
  rcases raw_message_cover_dichotomy c1 c2 Gamma with sparse | ⟨p,own,early,cover⟩
  · exact Or.inl sparse
  · refine Or.inr ⟨p,own,early,?_⟩
    intro q data checked circles quarter hq w claimed inactive strategy A G ha hg hgamma hpos hcount wrong
    rcases wrong with ⟨j,lane,hwrong⟩ | ⟨r,lane,hwrong⟩
    · apply wrong_component_near_bound data quarter hq w claimed inactive (received c1 c2 data)
        2324 strategy p j lane hwrong A G Gamma ha hg hgamma hpos hcount (by norm_num)
      intro gamma hgam Q close h1 h2
      exact cover gamma hgam _ (close_original c1 c2 data checked gamma Q close h1 h2)
    · exact wrong_ood_near_bound c1 c2 Gamma p cover data checked circles quarter hq w claimed
        inactive strategy A G ha hg hgamma hpos hcount r lane hwrong

#print axioms ood_error_atGamma
#print axioms wrong_ood_near_bound
#print axioms all_claims_dichotomy
end
end AspisV8.SelectedClaimGame
