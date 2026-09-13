import FSV8S4MatrixReconstruction
import SelectedResidualHighRecovery
import SelectedMiddleUniqueness

/-! S4 UNCOMPILED source-event adapter for the actual RecoveredHigh predicate.
Unlike a bare interpolation lemma it retains SAME-Q high support and the
actual adaptive final from Witness, and the SAME fixed pre-gamma family.
It does not claim that the replay collector produces the required nodes or
can test RecoveredHigh by running its noncomputable family definition. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 1600
namespace AspisV8Completion.FSV8S4RecoveredHighMatrix
open Finset
open AspisV8.CausalCoveredRecovery AspisV8.SelectedHigherYHighSupport
open AspisV8.SelectedRegularLowSupport AspisV8.SelectedReceivedOracle
open AspisV8.SelectedMiddleImageRecovery AspisV8.SelectedResidualHighRecovery
open AspisV8.SelectedMiddleUniqueness AspisV8.ComponentOODBinding
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.GammaComponentGame AspisV8.EarlyC1Family
open AspisV8Completion.FSV8S4MatrixReconstruction
noncomputable section
abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact
local instance : NeZero (2 : K) := AspisV8.SelectedReceivedOracle.twoNonzero
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P

/-- Reverse direction of the support arithmetic already used by the source
classifier; nothing about the received word being polynomial is assumed. -/
theorem high_support_has_enough (received : Fin 1048576 → K)
    (q : Fin 1024 → K) (high : HighSupport received q) :
    200808≤fibreCount received q := by
  have partition := AspisV8.SelectedMiddleGammaCover.full_bad_partition received q
  change (AspisV8.PartialFoldRecovery.fibreBad (m := 262144)
    (AspisPool.V7C1ConcreteProjectionBinding.exactInitialEncoder q) received).card≤4*15334 at high
  omega

/-- Four usable actual continuations supply a common quotient and a member
of the fixed family, rather than a supplied interpolation-success assertion. -/
theorem recovered_row_representation {q : Nat} (e : Execution q)
    (family : Finset (FSV8S4MatrixReconstruction.Tuple K))
    (gamma : K) (nodes : Finset K) (four : nodes.card=4)
    (kappa tau : K → K)
    (usable : ∀ a∈nodes, RecoveredHigh e family gamma (kappa a) (tau a) a) :
    ∃ quotient : Fin 1024 → K,
      (∀ a∈nodes, (e.strategy gamma (kappa a)).final (tau a) a=
        AspisV5ComponentCConcreteFoldLinearity.coefficientFoldLayer 256 a quotient) ∧
      ∃ p∈family,
        AspisV8.ComponentRows.original (atGamma e.data gamma) quotient=
          AspisV8.ClaimTransport.batch gamma p := by
  have nonempty : nodes.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a0,ha0⟩ := nonempty
  obtain ⟨quotient,witness0,high0,recovered0⟩ := usable a0 ha0
  obtain ⟨p,pmem,own,represented,early⟩ := recovered0
  refine ⟨quotient,?_,p,pmem,?_⟩
  · intro a ha
    obtain ⟨other,witness,high,recovered⟩ := usable a ha
    have same := high_support_unique (e.raw gamma) other quotient
      (high_support_has_enough _ _ high) (high_support_has_enough _ _ high0)
    have actual := witness.2.2.1
    simpa only [same] using actual
  · rw [AspisV8.SelectedComponentGame.original_eq]
    exact represented

/-- Concrete 29x4 composition for the selected RecoveredHigh event.
The returned tuple is COMPUTED from finals. No secret tuple is an argument. -/
theorem recovered_high_matrix_constructs_family_member {q : Nat} (e : Execution q)
    (family : Finset (FSV8S4MatrixReconstruction.Tuple K)) (small : family.card≤1)
    (gammaNodes : Finset K) (twentyNine : gammaNodes.card=29)
    (alphaNodes : K → Finset K)
    (four : ∀ g∈gammaNodes,(alphaNodes g).card=4)
    (kappa tau : K → K → K)
    (usable : ∀ g∈gammaNodes, ∀ a∈alphaNodes g,
      RecoveredHigh e family g (kappa g a) (tau g a) a) :
    FSV8S4MatrixReconstruction.reconstruct gammaNodes alphaNodes
      (fun g a => (e.strategy g (kappa g a)).final (tau g a) a)
      (fun g => atGamma e.data g) ∈ family := by
  apply reconstructed_member_of_single_family gammaNodes twentyNine alphaNodes four
    (fun g a => (e.strategy g (kappa g a)).final (tau g a) a)
    (fun g => atGamma e.data g) family small
  intro g hg
  exact recovered_row_representation e family g (alphaNodes g) (four g hg)
    (kappa g) (tau g) (usable g hg)

/-- The output also carries the actual source recovery event's early-C1
projection membership. This is a mathematical membership result, not an
executable enumeration of EarlyC1Family or a checked payment witness. -/
theorem recovered_high_matrix_has_early_projection {q : Nat} (e : Execution q)
    (family : Finset (FSV8S4MatrixReconstruction.Tuple K)) (small : family.card≤1)
    (gammaNodes : Finset K) (twentyNine : gammaNodes.card=29)
    (alphaNodes : K → Finset K)
    (four : ∀ g∈gammaNodes,(alphaNodes g).card=4)
    (kappa tau : K → K → K)
    (usable : ∀ g∈gammaNodes, ∀ a∈alphaNodes g,
      RecoveredHigh e family g (kappa g a) (tau g a) a) :
    c1Projection (FSV8S4MatrixReconstruction.reconstruct gammaNodes alphaNodes
      (fun g a => (e.strategy g (kappa g a)).final (tau g a) a)
      (fun g => atGamma e.data g)) ∈ AspisV8.EarlyC1Family.family e.c1 := by
  have outputMember := recovered_high_matrix_constructs_family_member e family small
    gammaNodes twentyNine alphaNodes four kappa tau usable
  have nonempty : gammaNodes.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨g,hg⟩ := nonempty
  have alphaNonempty : (alphaNodes g).Nonempty :=
    Finset.card_pos.mp (by rw [four g hg]; omega)
  obtain ⟨a,ha⟩ := alphaNonempty
  obtain ⟨quotient,witness,high,recovered⟩ := usable g hg a ha
  obtain ⟨p,pmem,own,represented,early⟩ := recovered
  have same : FSV8S4MatrixReconstruction.reconstruct gammaNodes alphaNodes
      (fun g a => (e.strategy g (kappa g a)).final (tau g a) a)
      (fun g => atGamma e.data g) = p :=
    Finset.card_le_one.mp small _ outputMember p pmem
  rw [same]
  exact early

#print axioms high_support_has_enough
#print axioms recovered_row_representation
#print axioms recovered_high_matrix_constructs_family_member
#print axioms recovered_high_matrix_has_early_projection
end
end AspisV8Completion.FSV8S4RecoveredHighMatrix
