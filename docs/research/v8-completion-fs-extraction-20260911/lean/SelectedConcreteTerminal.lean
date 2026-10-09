import SelectedConcreteRowLanes
import SelectedSemanticTerminalAlternativeV5

/-! Concrete same-tuple specialization of the compact semantic alternative.
This is a deterministic conditional consumer, not a verifier-success producer.
The reference trace, its causal plan, mask binding and terminal binding remain
explicit. The three helper conclusions are not assumed or hidden in success.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000
set_option maxRecDepth 2000
namespace AspisV8.SelectedConcreteTerminal
open scoped BigOperators
open AspisV5ComponentCQM31TowerExact
open AspisFormal.HashMerkleModel
open AspisV8.SelectedConcreteRowLanes AspisV8.SelectedSemanticRows
open AspisV8.SelectedSemanticTransfer AspisV8.SelectedEarlyC1Amounts
open AspisV8.EarlyC1LateProjection AspisV8.EarlyC1CopyCollision
open AspisV8.SelectedSemanticLaneAggregation AspisV8.SelectedSemanticHelperAggregation
open AspisV8.SelectedSemanticTerminalAlternative AspisV8.SelectedCompactSemanticRepair
open AspisV6TranscriptRelationGrammar AspisV6AcceptedPathObligations
noncomputable section
abbrev K := QM31Exact

/-- Concrete facts about the table and H of this tuple, not payment validity.
The helper global equalities are conclusions from aggregation; nonpoles are
not among these conclusions. -/
def TupleResiduals (rc : RoundConstants) (pub : Public)
    (tuple : Fin 29 → Fin 1024 → K) (lambda chi : K)
    (active : Fin 1024 → K) : Prop :=
  RowsVanish pub (semanticTable (c1Projection tuple)) ∧
  PoseidonChecks rc (semanticTable (c1Projection tuple)) ∧
  (∀ row, SelectedSemanticRows.copyResidual (memberTable (c1Projection tuple))
    pub.appendIndex lambda chi (tuple 26) row = 0) ∧
  (∑ row, tuple 26 row) = 0 ∧
  (∑ row, (1-active row)*tuple 26 row) = 0

structure ConcreteOutcome (T M : Finset K) (rc : RoundConstants) (pub : Public)
    (tuple : Fin 29 → Fin 1024 → K) (lambda chi : K)
    (active : Fin 1024 → K) (theta : K) (equalityPoint : Fin 10 → K) (mu : K) : Prop where
  algebraic : AlgebraicOutcome T M (tupleLanes rc pub tuple lambda chi)
    (tuple 26) active theta equalityPoint mu
  residuals_of_good :
    (AllRowsZero (tupleLanes rc pub tuple lambda chi) ∧
      (∑ row, tuple 26 row) = 0 ∧
      (∑ row, (1-active row)*tuple 26 row) = 0) →
    TupleResiduals rc pub tuple lambda chi active

theorem algebraic_outcome_constructs_residuals
    (T M : Finset K) (rc : RoundConstants) (pub : Public)
    (tuple : Fin 29 → Fin 1024 → K) (lambda chi : K)
    (active : Fin 1024 → K) (theta : K) (equalityPoint : Fin 10 → K) (mu : K)
    (outcome : AlgebraicOutcome T M (tupleLanes rc pub tuple lambda chi)
      (tuple 26) active theta equalityPoint mu) :
    ConcreteOutcome T M rc pub tuple lambda chi active theta equalityPoint mu := by
  refine ⟨outcome, ?_⟩
  rintro ⟨rows, helper, inactive⟩
  obtain ⟨semantic, poseidon, copy⟩ :=
    tupleRowsZero_constructs_residuals rc pub tuple lambda chi rows
  exact ⟨semantic, poseidon, copy, helper, inactive⟩

section Execution
variable (T M S : Finset K) (rc : RoundConstants) (pub : Public)
  (tuple : Fin 29 → Fin 1024 → K) (lambda chi : K)
  (fields : FixedFieldView K) (point : Fin 10 → K)
  (active mask : Fin 1024 → K) (theta : K) (equalityPoint : Fin 10 → K) (mu eta : K)
  (thetaInside : theta ∈ T) (muInside : mu ∈ M) (etaNonzero : eta ≠ 0)
  (reference : ReferenceTrace
    (maskedTable eta (realTable (tupleLanes rc pub tuple lambda chi)
      (tuple 26) active theta equalityPoint mu) mask) point)
  (plan : Plan K) (causal : FollowsPlan fields point reference plan)
  (inside : ∀ round, point round ∈ S)

include thetaInside muInside etaNonzero causal inside

/-- Both unmatched initial mask and terminal reference values remain named
alternatives. Thus even without source bindings this partition loses no case. -/
theorem concrete_terminal_alternative :
    ConcreteOutcome T M rc pub tuple lambda chi active theta equalityPoint mu ∨
    fields.initialClaim ≠ (∑ row, mask row) ∨
    semanticTerminalClaim fields point ≠
      referenceClaim (∑ row, maskedTable eta
        (realTable (tupleLanes rc pub tuple lambda chi) (tuple 26)
          active theta equalityPoint mu) mask row)
        reference.messages point (Fin.last 10) ∨
    RepairHit S plan point := by
  have split := selected_terminal_alternative T M S fields point
    (tupleLanes rc pub tuple lambda chi) (tuple 26) active mask
    theta equalityPoint mu eta thetaInside muInside etaNonzero
    reference plan causal inside
  exact map_alternatives split
    (algebraic_outcome_constructs_residuals T M rc pub tuple lambda chi
      active theta equalityPoint mu) (fun hit => hit)

/-- Minimal binding premises for deleting the two unmatched-value branches.
These equalities are not defined as, nor inferred from, Rust acceptance.
In particular a separately supplied reference trace does not authenticate them. -/
theorem bound_terminal_constructs_residuals_or_named_exceptions
    (maskBound : fields.initialClaim = ∑ row, mask row)
    (terminalBound : semanticTerminalClaim fields point =
      referenceClaim (∑ row, maskedTable eta
        (realTable (tupleLanes rc pub tuple lambda chi) (tuple 26)
          active theta equalityPoint mu) mask row)
        reference.messages point (Fin.last 10)) :
    ConcreteOutcome T M rc pub tuple lambda chi active theta equalityPoint mu ∨
      RepairHit S plan point := by
  rcases concrete_terminal_alternative T M S rc pub tuple lambda chi
    fields point active mask theta equalityPoint mu eta thetaInside muInside
    etaNonzero reference plan causal inside with outcome | badMask | badTerminal | repair
  · exact Or.inl outcome
  · exact False.elim (badMask maskBound)
  · exact False.elim (badTerminal terminalBound)
  · exact Or.inr repair
end Execution

#print bound_terminal_constructs_residuals_or_named_exceptions
#print axioms algebraic_outcome_constructs_residuals
#print axioms concrete_terminal_alternative
#print axioms bound_terminal_constructs_residuals_or_named_exceptions
end
end AspisV8.SelectedConcreteTerminal
