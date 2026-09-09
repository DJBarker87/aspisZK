import SelectedClaimGame

/-! Reuse the actual OOD reconstruction identity at a generic supported-final
radius. The deterministic recovered-close interface is consumed by the new
constructed three-helper cover, not assumed to follow from acceptance. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 300000
namespace AspisV8.GenericOODClaimGame
open Finset
open AspisV8.SelectedReceivedOracle AspisV8.GammaComponentGame
open AspisV8.SelectedComponentGame AspisV8.ComponentOODBinding
open AspisV8.OODInterpolant AspisV8.CausalOrderedRelation
open AspisV8.ShiftedRowPrefix AspisV8.JointImageGame AspisV8.ClaimTransport
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection AspisV8.PartialFoldRecovery
open AspisV8.NearGammaSelectedCoefficients
open AspisPool.V7C1ConcreteProjectionBinding
noncomputable section
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero

theorem unit {q : Nat} (c1 : C1Received) (c2 : C2Received) (data : Data (K := K))
    (quarter : K) (hq : quarter*4=1) (w : Fin 4 → Fin 1024 → K)
    (claimed : Fin 3 → Fin 29 → K) (inactive : K → K) (B : Nat)
    (strategy : K → K → Strategy domain q) (gamma : K) (A G : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (hcount : q≤domain.card) :
    nearProbability data quarter hq w claimed inactive (received c1 c2 data) B
      strategy gamma A G≤1 :=
  GammaComponentAux.rows_unit (rowPrefix data quarter w claimed inactive gamma) hq
    (oracle 0 (received c1 c2 data gamma)) (strategy gamma)
    (AspisV8.PreAnchorJoint.near (received c1 c2 data gamma) B (strategy gamma))
    A G ha hg hcount

/-- One wrong fixed component OOD answer gives one degree28 gamma polynomial.
The final and successive responses retain their actual causal adaptivity. -/
theorem wrong_ood_bound {q : Nat}
    (c1 : C1Received) (c2 : C2Received) (Gamma : Finset K)
    (p : Fin 29 → Message) (B : Nat)
    (data : Data (K := K)) (checked : data.Checked)
    (circles : data.x0^2+data.y0^2=1 ∧ data.x1^2+data.y1^2=1)
    (quarter : K) (hq : quarter*4=1) (w : Fin 4 → Fin 1024 → K)
    (claimed : Fin 3 → Fin 29 → K) (inactive : K → K)
    (strategy : K → K → Strategy domain q) (A G : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (hgamma : Gamma.Nonempty)
    (hpos : 0<q) (hcount : q≤domain.card) (margin : 5*B+255<262144)
    (cover : ∀ gamma∈Gamma, ∀ Q : Fin 1024 → K,
      (fibreBad (m := 262144) (exactInitialEncoder Q)
        (received c1 c2 data gamma)).card≤4*B →
      Q 1023=0 → (atGamma data gamma).b*Q 1022-(atGamma data gamma).c*Q 1021=0 →
      (atGamma data gamma).original Q=ClaimTransport.batch gamma p)
    (r : Fin 2) (lane : Fin 29)
    (wrong : data.answers r lane≠circleFunctional (pointX data r) (pointY data r) (p lane)) :
    avg Gamma (fun gamma => nearProbability data quarter hq w claimed inactive
      (received c1 c2 data) B strategy gamma A G)≤
      28/Gamma.card+((q:ℚ)+3)/G.card+24/A.card := by
  let ell := circleFunctional (pointX data r) (pointY data r)
  have h := avg_polynomial Gamma hgamma (errorPolynomial ell p (data.answers r))
    (component_error_nonzero ell p (data.answers r) lane wrong) 28
    (component_error_degree ell p (data.answers r))
    (fun gamma => nearProbability data quarter hq w claimed inactive
      (received c1 c2 data) B strategy gamma A G)
    (((q:ℚ)+3)/G.card+24/A.card) (by positivity)
    (fun gamma _ => unit c1 c2 data quarter hq w claimed inactive B
      strategy gamma A G ha hg hcount)
    (by
      intro gamma hgam nonzero
      apply near_bound_of_wrong_rows data quarter hq w claimed inactive (received c1 c2 data)
        B strategy gamma A G ha hg hpos hcount margin
      intro Q close h1 h2
      have zero := recovered_ood_error_eval (atGamma data gamma)
        (checked_atGamma data checked gamma) Q ⟨h1,h2⟩ circles p
        (cover gamma hgam Q close h1 h2) r
      rw [SelectedClaimGame.ood_error_atGamma] at zero
      exact False.elim (nonzero zero))
  simpa only [add_assoc,Nat.cast_ofNat] using h

#print axioms unit
#print axioms wrong_ood_bound
end
end AspisV8.GenericOODClaimGame
