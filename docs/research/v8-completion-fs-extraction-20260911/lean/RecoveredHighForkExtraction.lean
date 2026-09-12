import NestedMiddleClaimExtraction
import SelectedResidualHighRecovery

/-!
Deterministic candidate construction from a successful 29-by-4 fork table.
The extractor reads only the disclosed final256 vectors at the selected
continuations.  `RecoveredMiddleFork` is deliberately stronger than one
ordinary accepted run: it requires the same fixed execution/family to reach
the already-defined recovered middle event at every collected continuation.
Producing this table with bounded ROM queries and rewinds is a separate
probabilistic/resource theorem.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8Completion.RecoveredHighForkExtraction
open Polynomial Finset
open AspisV8.ClaimTransport AspisV8.Gamma29Reconstruction
open AspisV8.CausalCoveredRecovery AspisV8.SelectedHigherYHighSupport
open AspisV8.SelectedMiddleImageRecovery AspisV8.SelectedMiddleUniqueness
open AspisV8.SelectedRegularLowSupport AspisV8.NestedMiddleClaimExtraction
noncomputable section

abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact
abbrev Tuple := Fin 29 → Fin 1024 → K
local instance : NeZero (2 : K) := AspisV8.SelectedReceivedOracle.twoNonzero
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P

def coordinate (i : Fin 1024) : (Fin 1024 → K) →ₗ[K] K where
  toFun value := value i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

set_option maxRecDepth 400
/-- Twenty-nine distinct scalar-power evaluations determine all 29 vector
coefficients.  This is used to prove inclusion of the computed interpolation,
not supplied as a candidate-membership premise. -/
theorem tuple_eq_of_batches (nodes : Finset K) (count : nodes.card = 29)
    (left right : Tuple)
    (same : ∀ gamma ∈ nodes, batch gamma left = batch gamma right) : left = right := by
  funext lane i
  let error := errorPolynomial (coordinate i) left (fun j => right j i)
  have degree : error.natDegree ≤ 28 := component_error_degree (coordinate i) left _
  have zeros : ∀ gamma ∈ nodes, error.eval gamma = 0 := by
    intro gamma member
    have evaluated :
        (∑ j : Fin 29, gamma ^ j.val * right j i) - coordinate i (batch gamma left) =
          error.eval gamma := by
      exact component_error_eval (coordinate i) left (fun j => right j i) gamma
    have rightBatch : (∑ j : Fin 29, gamma ^ j.val * right j i) =
        coordinate i (batch gamma right) := by
      simp only [coordinate, batch, LinearMap.coe_mk, AddHom.coe_mk,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have sameCoordinate : coordinate i (batch gamma right) =
        coordinate i (batch gamma left) := by
      change batch gamma right i = batch gamma left i
      exact congrFun (same gamma member).symm i
    calc
      error.eval gamma =
          (∑ j : Fin 29, gamma ^ j.val * right j i) -
            coordinate i (batch gamma left) := evaluated.symm
      _ = coordinate i (batch gamma right) - coordinate i (batch gamma left) :=
        congrArg (fun value => value - coordinate i (batch gamma left)) rightBatch
      _ = 0 := sub_eq_zero.mpr sameCoordinate
  have zero : error = 0 := degree28_zero_of_29_nodes nodes count error degree zeros
  have coefficient := component_error_coeff (coordinate i) left (fun j => right j i) lane
  change error.coeff lane.val = right lane i - coordinate i (left lane) at coefficient
  rw [zero, Polynomial.coeff_zero] at coefficient
  exact (sub_eq_zero.mp coefficient.symm).symm

set_option maxRecDepth 200

/-- The exact branch needed by the 29-by-4 construction.  `RecoveredHigh`
alone includes high-support quotients above the middle radius; this predicate
keeps the middle upper bound visible rather than silently assuming it. -/
def RecoveredMiddleFork {q : Nat} (e : Execution q) (family : Finset Tuple)
    (gamma kappa tau alpha : K) : Prop :=
  ∃ Q, Witness e gamma kappa tau alpha Q ∧
    HighSupport (e.raw gamma) Q ∧
    fibreCount (e.raw gamma) Q ≤ 252847 ∧
    Recovered e.c1 e.c2 family e.data gamma Q

theorem fork_middle {q : Nat} (e : Execution q) (family : Finset Tuple)
    (gamma kappa tau alpha : K)
    (fork : RecoveredMiddleFork e family gamma kappa tau alpha) :
    ∃ Q, MiddleWitness e gamma kappa tau alpha Q := by
  obtain ⟨Q, witness, high, upper, _⟩ := fork
  have partition := AspisV8.SelectedMiddleGammaCover.full_bad_partition (e.raw gamma) Q
  have lower : 200808 ≤ fibreCount (e.raw gamma) Q := by
    change (AspisV8.PartialFoldRecovery.fibreBad (m := 262144)
      (AspisPool.V7C1ConcreteProjectionBinding.exactInitialEncoder Q)
      (e.raw gamma)).card ≤ 4 * 15334 at high
    omega
  exact ⟨Q, witness, lower, upper⟩

theorem family_member_unique (family : Finset Tuple) (one : family.card ≤ 1)
    (left right : Tuple) (leftMem : left ∈ family) (rightMem : right ∈ family) :
    left = right := by
  exact (Finset.card_le_one.mp one) left leftMem right rightMem

/-- A 29-by-4 recovered middle fork table constructs the unique fixed-family
tuple from final256 values.  The returned equality is the key non-tautological
property: the algorithmic interpolation output is proved to be in `family`;
the family member is not an input to `recoveredComponents`.

The collector still owes 116 successful causal continuations and all their
authentication/source/ROM/resource conditions. -/
theorem recovered_components_mem_family {q : Nat} (e : Execution q)
    (family : Finset Tuple) (one : family.card ≤ 1)
    (gammaNodes : Finset K) (count : gammaNodes.card = 29)
    (alphaNodes : K → Finset K) (kappa tau : K → K → K)
    (four : ∀ gamma ∈ gammaNodes, (alphaNodes gamma).card = 4)
    (forks : ∀ gamma ∈ gammaNodes, ∀ alpha ∈ alphaNodes gamma,
      RecoveredMiddleFork e family gamma (kappa gamma alpha) (tau gamma alpha) alpha) :
    recoveredComponents e gammaNodes alphaNodes kappa tau ∈ family := by
  have gammaNonempty : gammaNodes.Nonempty := by
    rw [← Finset.card_pos, count]
    decide
  obtain ⟨gamma0, gamma0Mem⟩ := gammaNonempty
  have alpha0Nonempty : (alphaNodes gamma0).Nonempty := by
    rw [← Finset.card_pos, four gamma0 gamma0Mem]
    decide
  obtain ⟨alpha0, alpha0Mem⟩ := alpha0Nonempty
  obtain ⟨Q0, _, _, _, recovered0⟩ := forks gamma0 gamma0Mem alpha0 alpha0Mem
  obtain ⟨p, pMem, _, _, _⟩ := recovered0
  have middles : ∀ gamma ∈ gammaNodes, ∀ alpha ∈ alphaNodes gamma, ∃ Q,
      MiddleWitness e gamma (kappa gamma alpha) (tau gamma alpha) alpha Q := by
    intro gamma gammaMem alpha alphaMem
    exact fork_middle e family gamma _ _ alpha (forks gamma gammaMem alpha alphaMem)
  have candidateAt : ∀ gamma ∈ gammaNodes,
      recoveredOriginal e alphaNodes kappa tau gamma = batch gamma p := by
    intro gamma gammaMem
    have alphaNonempty : (alphaNodes gamma).Nonempty := by
      rw [← Finset.card_pos, four gamma gammaMem]
      decide
    obtain ⟨alpha, alphaMem⟩ := alphaNonempty
    obtain ⟨Q, witness, _high, _upper, recovered⟩ :=
      forks gamma gammaMem alpha alphaMem
    obtain ⟨pGamma, pGammaMem, _, represented, _⟩ := recovered
    have pGammaEq : pGamma = p :=
      family_member_unique family one pGamma p pGammaMem pMem
    have reconstructed := recovered_quotient_canonical e alphaNodes kappa tau gamma
      (four gamma gammaMem) (middles gamma gammaMem)
    have active : HasMiddle e gamma := by
      obtain ⟨middleQ, middle⟩ := middles gamma gammaMem alpha alphaMem
      exact ⟨middleQ, kappa gamma alpha, tau gamma alpha, alpha, middle⟩
    have lower : 200808 ≤ fibreCount (e.raw gamma) Q := by
      change (AspisV8.PartialFoldRecovery.fibreBad (m := 262144)
        (AspisPool.V7C1ConcreteProjectionBinding.exactInitialEncoder Q)
        (e.raw gamma)).card ≤ 4 * 15334 at _high
      have partition := AspisV8.SelectedMiddleGammaCover.full_bad_partition (e.raw gamma) Q
      omega
    have canonicalQ := canonical_eq e gamma active (kappa gamma alpha)
      (tau gamma alpha) alpha Q witness lower
    change AspisV8.ComponentRows.original (AspisV8.GammaComponentGame.atGamma e.data gamma) Q =
      batch gamma pGamma at represented
    unfold recoveredOriginal
    rw [reconstructed, canonicalQ, represented, pGammaEq]
  have batches : ∀ gamma ∈ gammaNodes,
      batch gamma (recoveredComponents e gammaNodes alphaNodes kappa tau) = batch gamma p := by
    intro gamma member
    rw [recovered_components_at_nodes e gammaNodes count alphaNodes kappa tau gamma member]
    exact candidateAt gamma member
  have equal := tuple_eq_of_batches gammaNodes count
    (recoveredComponents e gammaNodes alphaNodes kappa tau) p batches
  rw [equal]
  exact pMem

/-- The computed tuple carries the concrete own-support and early-C1 family
facts of the recovered member.  These are the first downstream inputs needed
by the selected semantic/payment chain; they are not inferred merely from
cardinality-one. -/
theorem recovered_components_family_facts {q : Nat} (e : Execution q)
    (family : Finset Tuple) (one : family.card ≤ 1)
    (gammaNodes : Finset K) (count : gammaNodes.card = 29)
    (alphaNodes : K → Finset K) (kappa tau : K → K → K)
    (four : ∀ gamma ∈ gammaNodes, (alphaNodes gamma).card = 4)
    (forks : ∀ gamma ∈ gammaNodes, ∀ alpha ∈ alphaNodes gamma,
      RecoveredMiddleFork e family gamma (kappa gamma alpha) (tau gamma alpha) alpha) :
    recoveredComponents e gammaNodes alphaNodes kappa tau ∈ family ∧
      38228 ≤ (AspisV8.SelectedOwnSymbol.own e.c1 e.c2
        (recoveredComponents e gammaNodes alphaNodes kappa tau)).card ∧
      AspisV8.EarlyC1LateProjection.c1Projection
        (recoveredComponents e gammaNodes alphaNodes kappa tau) ∈
          AspisV8.EarlyC1Family.family e.c1 := by
  have computedMem := recovered_components_mem_family e family one gammaNodes count
    alphaNodes kappa tau four forks
  have gammaNonempty : gammaNodes.Nonempty := by
    rw [← Finset.card_pos, count]
    decide
  obtain ⟨gamma, gammaMem⟩ := gammaNonempty
  have alphaNonempty : (alphaNodes gamma).Nonempty := by
    rw [← Finset.card_pos, four gamma gammaMem]
    decide
  obtain ⟨alpha, alphaMem⟩ := alphaNonempty
  obtain ⟨Q, _, _, _, recovered⟩ := forks gamma gammaMem alpha alphaMem
  obtain ⟨p, pMem, own, _, early⟩ := recovered
  have same : recoveredComponents e gammaNodes alphaNodes kappa tau = p :=
    family_member_unique family one _ p computedMem pMem
  rw [same]
  exact ⟨pMem, own, early⟩

/-- The same final-only tuple also satisfies all 87 fixed component point
claims.  This reuses the repaired row equations in the actual middle witnesses;
it does not replace the still-missing semantic/copy residual implication. -/
theorem recovered_components_claims_exact {q : Nat} (e : Execution q)
    (family : Finset Tuple)
    (gammaNodes : Finset K) (count : gammaNodes.card = 29)
    (alphaNodes : K → Finset K) (kappa tau : K → K → K)
    (four : ∀ gamma ∈ gammaNodes, (alphaNodes gamma).card = 4)
    (forks : ∀ gamma ∈ gammaNodes, ∀ alpha ∈ alphaNodes gamma,
      RecoveredMiddleFork e family gamma (kappa gamma alpha) (tau gamma alpha) alpha) :
    ∀ row lane,
      e.claims row lane = AspisV8.ShiftedRowPrefix.covector (e.weights row.succ)
        (recoveredComponents e gammaNodes alphaNodes kappa tau lane) := by
  apply AspisV8.NestedMiddleClaimExtraction.recovered_component_claims_exact
    e gammaNodes count alphaNodes kappa tau four
  intro gamma gammaMem alpha alphaMem
  exact fork_middle e family gamma _ _ alpha (forks gamma gammaMem alpha alphaMem)

#print axioms tuple_eq_of_batches
#print axioms fork_middle
#print axioms family_member_unique
#print axioms recovered_components_mem_family
#print axioms recovered_components_family_facts
#print axioms recovered_components_claims_exact
end
end AspisV8Completion.RecoveredHighForkExtraction
