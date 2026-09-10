import HigherYRegularBranch
import SelectedHigherYBranch

/-! Source-review draft: the one-factor regular incidence bound applied to
the literal selected received/OOD prefix. Every witness is the SAME Q in
Qualified, reconstruction, actual original-symbol support, and factor root.
The event existentially includes all later choices; the proof chooses one
witness per gamma only for the deterministic cardinality argument.
No acceptance-to-this-branch, sampler law, or pre-gamma candidate is assumed.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.SelectedHigherYRegularTail
open Polynomial Finset
open AspisPool.V7C1ConcreteProjectionBinding
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisK1.V7Tag73ExactGRSConversion
open AspisV6Width29CorrelatedAgreement
open AspisV8.SelectedReceivedOracle AspisV8.SelectedOODGate
open AspisV8.SelectedFactorCoherence AspisV8.SelectedHigherYBranch
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.OODInterpolant AspisV8.GammaComponentGame
open AspisV8.ComponentOODBinding AspisV8.CoveredOriginalSymbols
open AspisV8.FactorIdentityCover
noncomputable section
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P
attribute [local irreducible] curvePrimeFactors

/-- Literal stored symbol equality against the SAME selected raw batch. -/
def originalSupport (c1 : C1Received) (c2 : C2Received) (d : Data (K := K))
    (gamma : K) (Q : Fin 1024 → K) : Finset (Fin 1048576) :=
  symbolSupport (exactInitialEncoder ((atGamma d gamma).original Q))
    (NearGammaSelectedC1.rawBatch c1 c2 gamma)

/-- The threshold is on an actual Qualified witness, not on an unrelated
original or a preselected expected trace. The full regular set is retained
as the outer event, including its fixed-row derivative restriction. -/
def supportGammas (c1 : C1Received) (c2 : C2Received) (d : Data (K := K))
    (F : TrivariatePolynomial K) (r : Fin 2) (Gamma : Finset K) (M : Nat) : Finset K :=
  (regularGammas c1 c2 d F r Gamma).filter fun gamma =>
    ∃ Q, Qualified c1 c2 d F gamma Q ∧ M ≤ (originalSupport c1 c2 d gamma Q).card

theorem originalSupport_agreement
    (c1 : C1Received) (c2 : C2Received) (d : Data (K := K))
    (gamma : K) (Q : Fin 1024 → K) (i : Fin 1048576)
    (member : i ∈ originalSupport c1 c2 d gamma Q) :
    exactInitialEncoder ((atGamma d gamma).original Q) i =
      width29CurveValue (received29 c1 c2) gamma i := by
  have matched : exactInitialEncoder ((atGamma d gamma).original Q) i =
      NearGammaSelectedC1.rawBatch c1 c2 gamma i := (Finset.mem_filter.mp member).2
  exact matched.trans (raw_batch_eq_curve c1 c2 gamma i)

/-- Existing literal-family support, including the two-SYMBOL pole loss,
already discharges the numerical threshold. No decoder success is used. -/
theorem qualified_support_38230
    (c1 : C1Received) (c2 : C2Received) (d : Data (K := K)) (checked : d.Checked)
    (F : TrivariatePolynomial K) (gamma : K) (Q : Fin 1024 → K)
    (qualified : Qualified c1 c2 d F gamma Q) :
    38230 ≤ (originalSupport c1 c2 d gamma Q).card := by
  have large := (qualified_valid c1 c2 d checked F (fun _ => Q) gamma qualified).1
  change 38229 < (originalSupport c1 c2 d gamma Q).card at large
  omega

theorem mem_supportGammas
    (c1 : C1Received) (c2 : C2Received) (d : Data (K := K))
    (F : TrivariatePolynomial K) (r : Fin 2) (Gamma : Finset K) (M : Nat) (gamma : K) :
    gamma ∈ supportGammas c1 c2 d F r Gamma M ↔
      gamma ∈ Gamma ∧
      (FactorCoherence.derivativeCurve F (point d r)
        (CurveOODGate.answerCurve (answers d r))).eval gamma ≠ 0 ∧
      ∃ Q, Qualified c1 c2 d F gamma Q ∧ M ≤ (originalSupport c1 c2 d gamma Q).card := by
  constructor
  · intro member
    obtain ⟨regular, witness⟩ := Finset.mem_filter.mp member
    obtain ⟨qualifying, derivative⟩ := Finset.mem_filter.mp regular
    exact ⟨(Finset.mem_filter.mp qualifying).1, derivative, witness⟩
  · rintro ⟨inGamma, derivative, Q, qualified, large⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, Q, qualified, large⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨inGamma, Q, qualified⟩, derivative⟩

/-- M=38230 does not impose a new support premise on regularGammas. -/
theorem supportGammas_38230
    (c1 : C1Received) (c2 : C2Received) (d : Data (K := K)) (checked : d.Checked)
    (F : TrivariatePolynomial K) (r : Fin 2) (Gamma : Finset K) :
    supportGammas c1 c2 d F r Gamma 38230 = regularGammas c1 c2 d F r Gamma := by
  ext gamma
  constructor
  · exact fun member => (Finset.mem_filter.mp member).1
  · intro member
    have qualifying := (Finset.mem_filter.mp member).1
    obtain ⟨Q, qualified⟩ := (Finset.mem_filter.mp qualifying).2
    exact Finset.mem_filter.mpr ⟨member, Q, qualified,
      qualified_support_38230 c1 c2 d checked F gamma Q qualified⟩

/-- Fixed actual parent factor and fixed retained OOD row. The symbolic
threshold selects the event; no particular gamma-indexed candidate strategy
is a hypothesis. Arbitrary later choices are already existential in it. -/
theorem support_tail_count
    (c1 : C1Received) (c2 : C2Received) (d : Data (K := K)) (checked : d.Checked)
    (circles : d.x0 ^ 2 + d.y0 ^ 2 = 1 ∧ d.x1 ^ 2 + d.y1 ^ 2 = 1)
    (west : ∀ r, pointX d r ≠ -1)
    (F : TrivariatePolynomial K) (factor : F ∈ curvePrimeFactors (parent c1 c2))
    (higher : 3 ≤ F.natDegree)
    (retained : Retained (point d) (fun r => CurveOODGate.answerCurve (answers d r)) F)
    (r : Fin 2) (Gamma : Finset K) (M : Nat) :
    (M - 1024) * (supportGammas c1 c2 d F r Gamma M).card ≤
      1048576 * HigherYRegularBranch.budget F := by
  let G := supportGammas c1 c2 d F r Gamma M
  have witnesses : ∀ gamma ∈ G, ∃ Q, Qualified c1 c2 d F gamma Q ∧
      M ≤ (originalSupport c1 c2 d gamma Q).card := by
    intro gamma member
    exact ((mem_supportGammas c1 c2 d F r Gamma M gamma).mp member).2.2
  let quotient : K → Fin 1024 → K := fun gamma =>
    if member : gamma ∈ G then Classical.choose (witnesses gamma member) else 0
  have selected : ∀ gamma ∈ G, Qualified c1 c2 d F gamma (quotient gamma) ∧
      M ≤ (originalSupport c1 c2 d gamma (quotient gamma)).card := by
    intro gamma member
    have chosen : quotient gamma = Classical.choose (witnesses gamma member) :=
      dif_pos member
    rw [chosen]
    exact Classical.choose_spec (witnesses gamma member)
  have nonzero : parent c1 c2 ≠ 0 :=
    curveTrivariatePolynomial_ne_zero _ (fixedInterpolant_nonzero c1 c2)
  have prime : Prime F := curvePrimeFactors_prime (parent c1 c2) nonzero F factor
  apply HigherYRegularBranch.regular_branch_count F prime higher
    (point d r) (CurveOODGate.answerCurve (answers d r))
    (CurveOODGate.answerCurve_degree (answers d r)) (retained.2 r)
    (received29 c1 c2) (fun gamma => (atGamma d gamma).original (quotient gamma))
    (fun gamma => originalSupport c1 c2 d gamma (quotient gamma)) G M
  · exact fun gamma member => (selected gamma member).2
  · intro gamma member i inside
    exact originalSupport_agreement c1 c2 d gamma (quotient gamma) i inside
  · exact fun gamma member => (selected gamma member).1.2.2
  · intro gamma member
    exact qualified_points c1 c2 d checked circles west F gamma (quotient gamma)
      (selected gamma member).1 r
  · intro gamma member
    exact ((mem_supportGammas c1 c2 d F r Gamma M gamma).mp member).2.1

/-- Literal covered-family threshold, with no supplied support inequality. -/
theorem regular_gammas_count
    (c1 : C1Received) (c2 : C2Received) (d : Data (K := K)) (checked : d.Checked)
    (circles : d.x0 ^ 2 + d.y0 ^ 2 = 1 ∧ d.x1 ^ 2 + d.y1 ^ 2 = 1)
    (west : ∀ r, pointX d r ≠ -1)
    (F : TrivariatePolynomial K) (factor : F ∈ curvePrimeFactors (parent c1 c2))
    (higher : 3 ≤ F.natDegree)
    (retained : Retained (point d) (fun r => CurveOODGate.answerCurve (answers d r)) F)
    (r : Fin 2) (Gamma : Finset K) :
    37206 * (regularGammas c1 c2 d F r Gamma).card ≤
      1048576 * HigherYRegularBranch.budget F := by
  have bound := support_tail_count c1 c2 d checked circles west F factor higher retained
    r Gamma 38230
  rw [supportGammas_38230 c1 c2 d checked F r Gamma] at bound
  exact bound

#print axioms originalSupport_agreement
#print axioms qualified_support_38230
#print axioms mem_supportGammas
#print axioms supportGammas_38230
#print axioms support_tail_count
#print axioms regular_gammas_count
end
end AspisV8.SelectedHigherYRegularTail
