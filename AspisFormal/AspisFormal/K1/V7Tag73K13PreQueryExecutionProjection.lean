import AspisFormal.K1.V7Tag73BatchedQuerySourceBridge

/-!
# Exact pre-query snapshot of the Tag-73 relation execution

The query-batch collision polynomial uses the running scalar immediately
before the query weights are installed.  Production already has the
post-round-zero claim, folded OOD covector, and disclosed final vector at that
point.  This file records precisely those three verifier values and factors
the scalar through them.  Query weights, query claims, later relation rounds,
and later alphas are deliberately absent.

This is the source-facing noninterference boundary needed by K1.3: an Aeneas
bridge can prove equality of concrete pre-query snapshots, while Lean derives
equality of the algebraic discrepancy rather than accepting it as a premise.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73K13PreQueryExecutionProjection

open AspisK1.V7Tag73BatchedQuerySourceBridge
open AspisPool.V7RelationCandidateBinding
open AspisV5ComponentCQM31TowerExact
open AspisV5FriRelationCandidateBridge

/-- Exactly the three production values read by the pre-query subtraction. -/
structure ExactK13PreQueryExecutionSnapshot where
  claimAfterRoundZero : QM31Exact
  foldedOodWeights256 : Fin 256 → QM31Exact
  disclosedFinal256 : Fin 256 → QM31Exact

/-- Literal snapshot from the maintained candidate execution. -/
def exactK13PreQueryExecutionSnapshot
    (execution : CandidateExecution QM31Exact) :
    ExactK13PreQueryExecutionSnapshot where
  claimAfterRoundZero := execution.claimAfterRound0
  foldedOodWeights256 := execution.foldedOodWeights256
  disclosedFinal256 := execution.disclosedFinal256

/-- Pure algebraic evaluator of the pre-query discrepancy. -/
def ExactK13PreQueryExecutionSnapshot.discrepancy
    (snapshot : ExactK13PreQueryExecutionSnapshot) : QM31Exact :=
  snapshot.claimAfterRoundZero -
    candidateClaim snapshot.foldedOodWeights256 snapshot.disclosedFinal256

/-- The maintained pre-query scalar reads no field outside the projection. -/
theorem preQueryDiscrepancy_eq_projection
    (execution : CandidateExecution QM31Exact) :
    preQueryDiscrepancy execution =
      (exactK13PreQueryExecutionSnapshot execution).discrepancy := by
  rfl

/-- Equal concrete pre-query snapshots force equal algebraic discrepancies. -/
theorem preQueryDiscrepancy_congr_of_projection_eq
    (left right : CandidateExecution QM31Exact)
    (snapshotExact : exactK13PreQueryExecutionSnapshot left =
      exactK13PreQueryExecutionSnapshot right) :
    preQueryDiscrepancy left = preQueryDiscrepancy right := by
  rw [preQueryDiscrepancy_eq_projection,
    preQueryDiscrepancy_eq_projection, snapshotExact]

#print axioms preQueryDiscrepancy_eq_projection
#print axioms preQueryDiscrepancy_congr_of_projection_eq

end AspisK1.V7Tag73K13PreQueryExecutionProjection
