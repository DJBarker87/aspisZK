import RecoveredHighForkExtraction
import SameC1CheckedTransferFacts

/-! DRAFT: same computed tuple -> base C1 table/point claims -> conditional
selected transfer facts. No caller-supplied candidate, validator success, or
validWitness is an input. Fork-table availability and the literal selected
semantic/Poseidon/copy residuals remain separate explicit assumptions. Exact
point claims alone DO NOT establish those residuals at all Boolean rows.
The copy helper below is computed tuple lane26 (source C2 order H,G,D), not
another freely supplied helper. The actual lambda/chi collision is retained.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000
namespace AspisV8Completion.RecoveredSameC1Transfer
open AspisFormal.ArithmetizationCore AspisFormal.HashMerkleModel
open AspisV5ComponentCQM31TowerExact
open AspisPool.V7FixedWidth29TupleList AspisPool.V7ExtractedLaneWords
open AspisPool.V7C1SubfieldRecovery
open AspisV8.CausalCoveredRecovery AspisV8.NestedMiddleClaimExtraction
open AspisV8.EarlyC1LateProjection AspisV8.EarlyC1CopyCollision
open AspisV8.SelectedEarlyC1Amounts AspisV8.SelectedEarlyC1Outputs
open AspisV8.SelectedSemanticRows AspisV8.SelectedSemanticTransfer
open AspisV8.SelectedSemanticOutputTransition
open AspisV8.SelectedSemanticAfterstateChecks AspisV8.SelectedSemanticInputPath
open AspisV8.SelectedMembershipDecode AspisV8.SelectedPairDecoder
open AspisV8.PositivePackBinding
open AspisV8.SameC1CheckedTransferFacts
open RecoveredHighForkExtraction
noncomputable section
abbrev K := QM31Exact
local instance : NeZero (2 : K) := AspisV8.SelectedReceivedOracle.twoNonzero

def recoveredC1 {q : Nat} (e : Execution q) (gammaNodes : Finset K)
    (alphaNodes : K → Finset K) (kappa tau : K → K → K) : C1InitialMessages :=
  c1Projection (recoveredComponents e gammaNodes alphaNodes kappa tau)

variable {q : Nat} (e : Execution q) (family : Finset Tuple)
  (one : family.card ≤ 1) (gammaNodes : Finset K) (count : gammaNodes.card = 29)
  (alphaNodes : K → Finset K) (kappa tau : K → K → K)
  (four : ∀ gamma ∈ gammaNodes, (alphaNodes gamma).card = 4)
  (forks : ∀ gamma ∈ gammaNodes, ∀ alpha ∈ alphaNodes gamma,
    RecoveredMiddleFork e family gamma (kappa gamma alpha) (tau gamma alpha) alpha)

include family one count four forks

/-- Base descent and exact claimed C1 functionals of the SAME decoded table.
The functional's literal multilinear/source-weight producer is still a
separate interface: this theorem does not infer it from its name. -/
theorem recovered_table_and_c1_claims
    (baseWord : ∀ column index, projectBase (e.c1 column index) = e.c1 column index) :
    (∀ row : Fin 1024, ∀ column : Fin 16,
      liftBase (semanticTable (recoveredC1 e gammaNodes alphaNodes kappa tau)
        row.val column.val) =
      memberTable (recoveredC1 e gammaNodes alphaNodes kappa tau) row column.val) ∧
    (∀ row : Fin 3, ∀ column : Fin 16,
      e.claims row (c1LaneIndex ⟨column.val, by omega⟩) =
        AspisV8.ShiftedRowPrefix.covector (e.weights row.succ)
          (fun i => liftBase (semanticTable
            (recoveredC1 e gammaNodes alphaNodes kappa tau) i.val column.val))) := by
  have familyFacts := recovered_components_family_facts e family one gammaNodes count
    alphaNodes kappa tau four forks
  have base := semanticTable_embeds e.c1
    (recoveredC1 e gammaNodes alphaNodes kappa tau) familyFacts.2.2 baseWord
  refine ⟨base, ?_⟩
  intro row column
  have claims := recovered_components_claims_exact e family gammaNodes count
    alphaNodes kappa tau four forks row (c1LaneIndex ⟨column.val, by omega⟩)
  have table :
      (fun i : Fin 1024 => liftBase (semanticTable
        (recoveredC1 e gammaNodes alphaNodes kappa tau) i.val column.val)) =
      recoveredComponents e gammaNodes alphaNodes kappa tau
        (c1LaneIndex ⟨column.val, by omega⟩) := by
    funext i
    exact (base i column).trans (late_projection_read
      (recoveredComponents e gammaNodes alphaNodes kappa tau) i column)
  rw [table]
  exact claims

/-- Residual enforcement is deliberately exposed here, never derived by
renaming fixed point binding. The copy branch uses the recovered H column
and keeps its active-row poles and both helper boundary sums. -/
theorem recovered_transfer_facts_or_copy_collision
    (rc : RoundConstants) (pub : Public) (sequence nextIndex rustCarry : Nat)
    (lambdas chis : Finset K) (lambda chi : K)
    (lambdaMember : lambda ∈ lambdas) (chiMember : chi ∈ chis)
    (rowResiduals : RowsVanish pub
      (semanticTable (recoveredC1 e gammaNodes alphaNodes kappa tau)))
    (poseidonResiduals : PoseidonChecks rc
      (semanticTable (recoveredC1 e gammaNodes alphaNodes kappa tau)))
    (copyResiduals : CopyConditions (recoveredC1 e gammaNodes alphaNodes kappa tau)
      .transfer pub.appendIndex lambda chi
      (recoveredComponents e gammaNodes alphaNodes kappa tau 26))
    (comparisons : SourceComparisons pub sequence nextIndex rustCarry)
    (carryExact : rustCarry = AspisV8.SelectedAppendAfterstate.carryIndex pub.appendIndex) :
    (TransferTransitionFacts rc pub (recoveredC1 e gammaNodes alphaNodes kappa tau)
        sequence nextIndex ∧
      RawInputDecoderFacts (recoveredC1 e gammaNodes alphaNodes kappa tau) ∧
      decodedForestRoot rc
        (rawSemanticTable (recoveredC1 e gammaNodes alphaNodes kappa tau)) = pub.anchor ∧
      pub.nullifier = nullifierHash rc
        (AspisV8.SelectedNoteRecovery.key
          (semanticTable (recoveredC1 e gammaNodes alphaNodes kappa tau)))
        (AspisV8.SelectedNoteRecovery.salt
          (semanticTable (recoveredC1 e gammaNodes alphaNodes kappa tau)))) ∨
    (lambda,chi) ∈ collisionPairs e.c1 .transfer pub.appendIndex lambdas chis := by
  have familyFacts := recovered_components_family_facts e family one gammaNodes count
    alphaNodes kappa tau four forks
  have classified := source_member_covered e.c1 .transfer pub.appendIndex lambdas chis
    lambda chi lambdaMember chiMember (recoveredC1 e gammaNodes alphaNodes kappa tau)
    familyFacts.2.2 (recoveredComponents e gammaNodes alphaNodes kappa tau 26) copyResiduals
  rcases classified with aliases | collision
  · have facts := selected_residuals_construct_transfer_and_membership rc pub
      (recoveredC1 e gammaNodes alphaNodes kappa tau) sequence nextIndex rustCarry
      rowResiduals poseidonResiduals aliases comparisons carryExact
    exact Or.inl ⟨facts.1, facts.2.2.2.2, facts.2.2.2.1, facts.2.2.1⟩
  · exact Or.inr collision

#print recovered_table_and_c1_claims
#print recovered_transfer_facts_or_copy_collision
#print axioms recovered_table_and_c1_claims
#print axioms recovered_transfer_facts_or_copy_collision
end
end AspisV8Completion.RecoveredSameC1Transfer
