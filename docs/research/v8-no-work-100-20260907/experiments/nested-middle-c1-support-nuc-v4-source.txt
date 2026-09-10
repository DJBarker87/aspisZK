import NestedMiddleClaimExtraction
import SelectedOwnSymbol

/-! A common authenticated symbol set at the twenty-nine reconstructed gamma
nodes identifies the component tuple on that SAME set. This is the exact
support seam between nested middle reconstruction and the early-C1 family.
The common set remains an explicit premise; separate large supports at each
gamma do not imply it. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 220000

namespace AspisV8.NestedMiddleC1Support
open Polynomial Finset
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV8.CausalCoveredRecovery AspisV8.NearGammaSelectedC1
open AspisV8.NestedMiddleClaimExtraction AspisV8.Gamma29Reconstruction
open AspisV8.TupleQueryTransport AspisV8.OwnSymbolCollision
open AspisV8.SelectedOwnSymbol AspisV8.EarlyC1LateProjection
noncomputable section

abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P

/-- Twenty-nine nodal batch equalities turn equality on one common symbol
set into coefficientwise equality for all twenty-nine lanes. -/
theorem common_nodes_subset_own {q : Nat} (e : Execution q)
    (gammaNodes : Finset K) (count : gammaNodes.card = 29)
    (alphaNodes : K → Finset K) (kappa tau : K → K → K)
    (S : Finset (Fin 1048576))
    (common : ∀ gamma ∈ gammaNodes, ∀ i ∈ S,
      rawBatch e.c1 e.c2 gamma i =
        exactInitialEncoder (recoveredOriginal e alphaNodes kappa tau gamma) i) :
    S ⊆ SelectedOwnSymbol.own e.c1 e.c2
      (recoveredComponents e gammaNodes alphaNodes kappa tau) := by
  intro i member
  let tuple := recoveredComponents e gammaNodes alphaNodes kappa tau
  have zeros : ∀ gamma ∈ gammaNodes,
      (symbolError e.c1 e.c2 tuple i).eval gamma = 0 := by
    intro gamma gammaMember
    rw [symbolError_eval]
    rw [recovered_components_at_nodes e gammaNodes count alphaNodes kappa tau
      gamma gammaMember]
    exact sub_eq_zero.mpr (common gamma gammaMember i member)
  have degree : (symbolError e.c1 e.c2 tuple i).natDegree ≤ 28 := by
    unfold symbolError
    exact residual_degree (received29 e.c1 e.c2) (expected tuple) i
  have polynomialZero : symbolError e.c1 e.c2 tuple i = 0 :=
    degree28_zero_of_29_nodes gammaNodes count _ degree zeros
  have lanes : ∀ lane,
      received29 e.c1 e.c2 lane i = exactInitialEncoder (tuple lane) i := by
    have identified := (residual_zero_iff (received29 e.c1 e.c2)
      (expected tuple) i).mp polynomialZero
    simpa only [expected] using identified
  rw [SelectedOwnSymbol.own_eq_joint]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lanes⟩

theorem early_member_of_common_nodes {q : Nat} (e : Execution q)
    (gammaNodes : Finset K) (count : gammaNodes.card = 29)
    (alphaNodes : K → Finset K) (kappa tau : K → K → K)
    (S : Finset (Fin 1048576)) (large : 38228 ≤ S.card)
    (common : ∀ gamma ∈ gammaNodes, ∀ i ∈ S,
      rawBatch e.c1 e.c2 gamma i =
        exactInitialEncoder (recoveredOriginal e alphaNodes kappa tau gamma) i) :
    c1Projection (recoveredComponents e gammaNodes alphaNodes kappa tau) ∈
      EarlyC1Family.family e.c1 := by
  have subset := common_nodes_subset_own e gammaNodes count alphaNodes kappa tau S common
  apply own_supported_early_member e.c1 e.c2
    (recoveredComponents e gammaNodes alphaNodes kappa tau)
  exact large.trans (Finset.card_le_card subset)

/-- The strongest deterministic nested endpoint presently justified: the
same reconstructed tuple has an early-C1 family member and all 87 exact point
claims, provided one common support set and the actual middle witnesses. -/
theorem early_member_and_claims {q : Nat} (e : Execution q)
    (gammaNodes : Finset K) (count : gammaNodes.card = 29)
    (alphaNodes : K → Finset K) (kappa tau : K → K → K)
    (four : ∀ gamma ∈ gammaNodes, (alphaNodes gamma).card = 4)
    (middle : ∀ gamma ∈ gammaNodes, ∀ alpha ∈ alphaNodes gamma, ∃ Q,
      SelectedMiddleUniqueness.MiddleWitness e gamma
        (kappa gamma alpha) (tau gamma alpha) alpha Q)
    (S : Finset (Fin 1048576)) (large : 38228 ≤ S.card)
    (common : ∀ gamma ∈ gammaNodes, ∀ i ∈ S,
      rawBatch e.c1 e.c2 gamma i =
        exactInitialEncoder (recoveredOriginal e alphaNodes kappa tau gamma) i) :
    c1Projection (recoveredComponents e gammaNodes alphaNodes kappa tau) ∈
        EarlyC1Family.family e.c1 ∧
      ∀ row lane, e.claims row lane =
        ShiftedRowPrefix.covector (e.weights row.succ)
          (recoveredComponents e gammaNodes alphaNodes kappa tau lane) := by
  constructor
  · exact early_member_of_common_nodes e gammaNodes count alphaNodes kappa tau
      S large common
  · exact recovered_component_claims_exact e gammaNodes count alphaNodes kappa tau
      four middle

#print axioms common_nodes_subset_own
#print axioms early_member_of_common_nodes
#print axioms early_member_and_claims
end
end AspisV8.NestedMiddleC1Support
