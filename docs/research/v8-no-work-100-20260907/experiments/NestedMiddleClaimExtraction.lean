import SelectedMiddleFourAlpha
import Gamma29Reconstruction
import ComponentRows

/-! Deterministic composition of the actual higher-Y middle witness gates.
Four alpha continuations reconstruct the canonical quotient at each gamma;
twenty-nine gamma nodes then reconstruct component messages.  The repaired
ordinary-row gate already present in each `MiddleWitness` supplies the three
batched point equations, so all eighty-seven component point claims follow.

This is not a shared-support, authenticated-opening, payment-validity,
sampler, Fiat--Shamir, or probability theorem. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.NestedMiddleClaimExtraction
open Finset
open AspisV5ComponentCConcreteFoldLinearity
open AspisV8.CausalCoveredRecovery AspisV8.SelectedMiddleUniqueness
open AspisV8.SelectedCoveredRelation AspisV8.ReferenceIndependentRelation
open AspisV8.GammaComponentGame AspisV8.ShiftedRowPrefix
open AspisV8.ClaimTransport
noncomputable section

abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero

theorem reverse_eq_of_sub_eq_zero {a b : K} (zero : a - b = 0) : b = a :=
  (sub_eq_zero.mp zero).symm

/-- The quotient is computed solely from the four disclosed final vectors at
the selected alpha nodes. Values of the strategy outside those nodes are not
used by `Generic.reconstruct`. -/
def recoveredQuotient {q : Nat} (e : Execution q)
    (alphaNodes : K → Finset K) (kappa tau : K → K → K) (gamma : K) :
    Fin 1024 → K :=
  SelectedMiddleFourAlpha.Generic.reconstruct (alphaNodes gamma)
    (fun alpha => (e.strategy gamma (kappa gamma alpha)).final (tau gamma alpha) alpha)

def recoveredOriginal {q : Nat} (e : Execution q)
    (alphaNodes : K → Finset K) (kappa tau : K → K → K) (gamma : K) :
    Fin 1024 → K :=
  ComponentRows.original (atGamma e.data gamma)
    (recoveredQuotient e alphaNodes kappa tau gamma)

def recoveredComponents {q : Nat} (e : Execution q) (gammaNodes : Finset K)
    (alphaNodes : K → Finset K) (kappa tau : K → K → K) :
    Fin 29 → Fin 1024 → K :=
  Gamma29Reconstruction.reconstructed gammaNodes
    (recoveredOriginal e alphaNodes kappa tau)

theorem recovered_quotient_canonical {q : Nat} (e : Execution q)
    (alphaNodes : K → Finset K) (kappa tau : K → K → K) (gamma : K)
    (four : (alphaNodes gamma).card = 4)
    (middle : ∀ alpha ∈ alphaNodes gamma, ∃ Q,
      MiddleWitness e gamma (kappa gamma alpha) (tau gamma alpha) alpha Q) :
    recoveredQuotient e alphaNodes kappa tau gamma = canonical e gamma := by
  exact SelectedMiddleFourAlpha.reconstruct_middle_canonical e gamma
    (alphaNodes gamma) four (kappa gamma) (tau gamma) middle

/-- The row equation is derived from the `not badAnchor` field of an actual
middle witness. It is not an independently supplied desired equality. -/
theorem recovered_original_row_match {q : Nat} (e : Execution q)
    (alphaNodes : K → Finset K) (kappa tau : K → K → K) (gamma : K)
    (four : (alphaNodes gamma).card = 4)
    (middle : ∀ alpha ∈ alphaNodes gamma, ∃ Q,
      MiddleWitness e gamma (kappa gamma alpha) (tau gamma alpha) alpha Q)
    (row : Fin 3) :
    covector (e.weights row.succ)
        (recoveredOriginal e alphaNodes kappa tau gamma) =
      ∑ lane : Fin 29, gamma ^ lane.val * e.claims row lane := by
  have nodeNonempty : (alphaNodes gamma).Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨alpha, alphaMember⟩ := nodeNonempty
  obtain ⟨Q, witness⟩ := middle alpha alphaMember
  have active : HasMiddle e gamma :=
    ⟨Q, kappa gamma alpha, tau gamma alpha, alpha, witness⟩
  have recoveredEq : recoveredQuotient e alphaNodes kappa tau gamma = Q :=
    (recovered_quotient_canonical e alphaNodes kappa tau gamma four middle).trans
      (canonical_eq e gamma active (kappa gamma alpha) (tau gamma alpha) alpha Q
        witness.1 witness.2.1)
  have errorsZero : (replaceRows (e.rows gamma) Q).errors = 0 := by
    by_contra nonzero
    exact witness.1.2.1 (Or.inr (Or.inr nonzero))
  have sourceErrors :
      (ComponentRows.rows (atGamma e.data gamma) e.quarter e.weights e.claims
        (e.inactive gamma) Q).errors = 0 := by
    rw [← reference_rows]
    exact errorsZero
  have point := ComponentRows.point_error (atGamma e.data gamma) e.quarter
    e.weights e.claims (e.inactive gamma) Q row
  have gammaValue : (atGamma e.data gamma).gamma = gamma := rfl
  rw [gammaValue] at point
  have rowZero := congrFun sourceErrors row.succ
  rw [show (0 : Fin 4 → K) row.succ = 0 from rfl] at rowZero
  have zeroDiff := point.symm.trans rowZero
  have matched := reverse_eq_of_sub_eq_zero zeroDiff
  unfold recoveredOriginal
  rw [recoveredEq]
  exact matched

theorem recovered_components_at_nodes {q : Nat} (e : Execution q)
    (gammaNodes : Finset K) (count : gammaNodes.card = 29)
    (alphaNodes : K → Finset K) (kappa tau : K → K → K)
    (gamma : K) (member : gamma ∈ gammaNodes) :
    batch gamma (recoveredComponents e gammaNodes alphaNodes kappa tau) =
      recoveredOriginal e alphaNodes kappa tau gamma := by
  exact Gamma29Reconstruction.nodal_reconstruction gammaNodes
    (recoveredOriginal e alphaNodes kappa tau) count gamma member

/-- Actual source-shaped deterministic endpoint of the nested interpolation:
all three rows and all twenty-nine component claims are exact for the tuple
reconstructed from the disclosed finals. -/
theorem recovered_component_claims_exact {q : Nat} (e : Execution q)
    (gammaNodes : Finset K) (count : gammaNodes.card = 29)
    (alphaNodes : K → Finset K) (kappa tau : K → K → K)
    (four : ∀ gamma ∈ gammaNodes, (alphaNodes gamma).card = 4)
    (middle : ∀ gamma ∈ gammaNodes, ∀ alpha ∈ alphaNodes gamma, ∃ Q,
      MiddleWitness e gamma (kappa gamma alpha) (tau gamma alpha) alpha Q) :
    ∀ row lane,
      e.claims row lane =
        covector (e.weights row.succ)
          (recoveredComponents e gammaNodes alphaNodes kappa tau lane) := by
  let rowMap : Fin 3 → (Fin 1024 → K) →ₗ[K] K :=
    fun row => covector (e.weights row.succ)
  have matched : ∀ gamma ∈ gammaNodes, ∀ row : Fin 3,
      rowMap row (recoveredOriginal e alphaNodes kappa tau gamma) =
        ∑ lane : Fin 29, gamma ^ lane.val * e.claims row lane := by
    intro gamma member row
    exact recovered_original_row_match e alphaNodes kappa tau gamma
      (four gamma member) (middle gamma member) row
  exact Gamma29Reconstruction.reconstructed_claims_exact gammaNodes count
    (recoveredOriginal e alphaNodes kappa tau) rowMap e.claims matched

#print axioms recovered_quotient_canonical
#print axioms reverse_eq_of_sub_eq_zero
#print axioms recovered_original_row_match
#print axioms recovered_components_at_nodes
#print axioms recovered_component_claims_exact
end
end AspisV8.NestedMiddleClaimExtraction
