import NestedMiddleC1Support
import SelectedHigherYHighSupport

/-! The reconstructed twenty-nine-component tuple has a total deterministic
own-support classification.  Sufficient own support gives the existing early
C1 family member.  Otherwise, every collected gamma whose four continuations
carry actual middle witnesses belongs to the fixed exceptional-gamma set of
that SAME reconstructed tuple.

This is not a probability theorem: the reconstructed tuple depends on the
collected gamma nodes, so charging its exceptional set still requires a
causal collector/selection argument. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000
set_option maxHeartbeats 240000

namespace AspisV8.NestedMiddleOwnSupportDichotomy
open Finset
open AspisV8.CausalCoveredRecovery AspisV8.NestedMiddleClaimExtraction
open AspisV8.SelectedMiddleUniqueness AspisV8.SelectedHigherYHighSupport
open AspisV8.SelectedOwnSymbol AspisV8.GammaComponentGame
open AspisV8.ClaimTransport AspisV8.EarlyC1LateProjection
open AspisV8.OODInterpolant AspisV8.TupleQueryTransport
open AspisV8.OwnSymbolCollision AspisV8.QuotientFamilySelected
open AspisV8.NearGammaSelectedC1
noncomputable section

abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P

theorem exists_mem_of_card_four {A : Type*} [DecidableEq A] (s : Finset A)
    (four : s.card = 4) : ∃ x, x ∈ s := by
  exact Finset.card_pos.mp (by omega)

/-- Deterministic own-support dichotomy for the actual tuple reconstructed
from the nested middle witnesses.  The right branch does not union over
candidate tuples: it names one tuple and one fixed exceptional set. -/
theorem early_member_or_all_nodes_bad {q : Nat} (e : Execution q)
    (checked : e.data.Checked) (G gammaNodes : Finset K)
    (nodeSubset : gammaNodes ⊆ G) (count : gammaNodes.card = 29)
    (alphaNodes : K → Finset K) (kappa tau : K → K → K)
    (four : ∀ gamma ∈ gammaNodes, (alphaNodes gamma).card = 4)
    (middle : ∀ gamma ∈ gammaNodes, ∀ alpha ∈ alphaNodes gamma, ∃ Q,
      MiddleWitness e gamma (kappa gamma alpha) (tau gamma alpha) alpha Q) :
    c1Projection (recoveredComponents e gammaNodes alphaNodes kappa tau) ∈
        EarlyC1Family.family e.c1 ∨
      ∀ gamma ∈ gammaNodes,
        gamma ∈ badGamma e.c1 e.c2
          (recoveredComponents e gammaNodes alphaNodes kappa tau) G := by
  let components := recoveredComponents e gammaNodes alphaNodes kappa tau
  change c1Projection components ∈ EarlyC1Family.family e.c1 ∨
    ∀ gamma ∈ gammaNodes, gamma ∈ badGamma e.c1 e.c2 components G
  by_cases large : 38228 ≤ (own e.c1 e.c2 components).card
  · exact Or.inl (own_supported_early_member e.c1 e.c2 components large)
  · right
    have small : (own e.c1 e.c2 components).card < 38228 := Nat.lt_of_not_ge large
    intro gamma gammaMember
    let alpha : K := Classical.choose
      (exists_mem_of_card_four (alphaNodes gamma) (four gamma gammaMember))
    have alphaMember : alpha ∈ alphaNodes gamma := Classical.choose_spec
      (exists_mem_of_card_four (alphaNodes gamma) (four gamma gammaMember))
    let Q : Fin 1024 → K := Classical.choose
      (middle gamma gammaMember alpha alphaMember)
    have witness : MiddleWitness e gamma (kappa gamma alpha) (tau gamma alpha) alpha Q :=
      Classical.choose_spec (middle gamma gammaMember alpha alphaMember)
    have image := witness_image e gamma (kappa gamma alpha) (tau gamma alpha) alpha Q
      witness.1
    have recoveredEq : recoveredQuotient e alphaNodes kappa tau gamma = Q :=
      (recovered_quotient_canonical e alphaNodes kappa tau gamma
        (four gamma gammaMember) (middle gamma gammaMember)).trans
        (canonical_eq e gamma
          ⟨Q, kappa gamma alpha, tau gamma alpha, alpha, witness⟩
          (kappa gamma alpha) (tau gamma alpha) alpha Q witness.1 witness.2.1)
    have nodeEq : batch gamma components = recoveredOriginal e alphaNodes kappa tau gamma :=
      recovered_components_at_nodes e gammaNodes count alphaNodes kappa tau gamma gammaMember
    have represented :
        (atGamma e.data gamma).original Q = batch gamma components := by
      rw [← SelectedComponentGame.original_eq e.data gamma Q]
      rw [← recoveredEq]
      exact nodeEq.symm
    have literal : Q ∈ QuotientFamilySelected.literalFamily
        (SelectedComponentGame.received e.c1 e.c2 e.data gamma) := by
      exact witness.1.1
    letI : DecidableEq K := Classical.decEq K
    have quotientSupport := CoveredOriginalSymbols.family_member_original_38230
      (atGamma e.data gamma)
      (SelectedComponentGame.checked_atGamma e.data checked gamma) Q image
      (rawBatch e.c1 e.c2 gamma) literal
    rw [represented] at quotientSupport
    have enough : 38230 ≤ (OwnSymbolCollision.matching Finset.univ
        (received29 e.c1 e.c2) (expected components) gamma).card := by
      rw [matching_eq_symbols]
      exact quotientSupport
    have excess : (OwnSymbolCollision.own Finset.univ
        (received29 e.c1 e.c2) (expected components)).card <
        (OwnSymbolCollision.matching Finset.univ
          (received29 e.c1 e.c2) (expected components) gamma).card := by
      dsimp only [SelectedOwnSymbol.own] at small
      omega
    have inside : OwnSymbolCollision.matching Finset.univ
        (received29 e.c1 e.c2) (expected components) gamma ⊆
        (Finset.univ : Finset (Fin 1048576)) := Finset.subset_univ _
    have roots : ∀ i ∈ OwnSymbolCollision.matching Finset.univ
        (received29 e.c1 e.c2) (expected components) gamma,
        (symbolError e.c1 e.c2 components i).eval gamma = 0 := by
      intro i member
      simpa only [OwnSymbolCollision.matching, Finset.mem_filter, Finset.mem_univ,
        true_and, symbolError] using member
    have forced := SelectedOwnSymbol.Generic.excess_charged
      (Finset.univ : Finset (Fin 1048576))
      (OwnSymbolCollision.own Finset.univ
        (received29 e.c1 e.c2) (expected components))
      (OwnSymbolCollision.matching Finset.univ
        (received29 e.c1 e.c2) (expected components) gamma)
      G (fun i g => (symbolError e.c1 e.c2 components i).eval g = 0)
      gamma (nodeSubset gammaMember) inside roots excess
    rw [badGamma_eq_charged]
    exact forced

/-- The repaired ordinary rows simultaneously identify all 87 point claims,
regardless of which support branch holds. -/
theorem claims_exact_and_support_classified {q : Nat} (e : Execution q)
    (checked : e.data.Checked) (G gammaNodes : Finset K)
    (nodeSubset : gammaNodes ⊆ G) (count : gammaNodes.card = 29)
    (alphaNodes : K → Finset K) (kappa tau : K → K → K)
    (four : ∀ gamma ∈ gammaNodes, (alphaNodes gamma).card = 4)
    (middle : ∀ gamma ∈ gammaNodes, ∀ alpha ∈ alphaNodes gamma, ∃ Q,
      MiddleWitness e gamma (kappa gamma alpha) (tau gamma alpha) alpha Q) :
    (∀ row lane, e.claims row lane =
        ShiftedRowPrefix.covector (e.weights row.succ)
          (recoveredComponents e gammaNodes alphaNodes kappa tau lane)) ∧
      (c1Projection (recoveredComponents e gammaNodes alphaNodes kappa tau) ∈
          EarlyC1Family.family e.c1 ∨
        ∀ gamma ∈ gammaNodes,
          gamma ∈ badGamma e.c1 e.c2
            (recoveredComponents e gammaNodes alphaNodes kappa tau) G) := by
  constructor
  · exact recovered_component_claims_exact e gammaNodes count alphaNodes kappa tau
      four middle
  · exact early_member_or_all_nodes_bad e checked G gammaNodes nodeSubset count
      alphaNodes kappa tau four middle

#print axioms early_member_or_all_nodes_bad
#print axioms claims_exact_and_support_classified
end
end AspisV8.NestedMiddleOwnSupportDichotomy
