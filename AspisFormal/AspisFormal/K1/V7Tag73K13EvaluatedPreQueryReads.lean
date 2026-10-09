import AspisFormal.K1.V7Tag73K13PreQueryExecutionProjection
import AspisFormal.K1.V7Tag73K13SnapshotLengthAudit

/-!
# Effective source reads for the K1.3 pre-query scalar

Draft, not kernel checked in the authoring environment.

The existing ExactK13PreQueryExecutionInput stores two entire functions of
firstMix. Production needs only their values at the actual firstMix. Equality
of these evaluated reads is a strictly narrower proof obligation than equality
of the functions at every possible challenge. This module proves the reduction;
it does NOT assume or prove that the reads are fixed by a source prefix.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73K13EvaluatedPreQueryReads

open AspisK1.V7Tag73BatchedQuerySourceBridge
open AspisK1.V7Tag73K13PreQueryExecutionProjection
open AspisK1.V7Tag73K13SnapshotLengthAudit
open AspisPool.V7RelationCandidateBinding
open AspisV5ComponentCQM31TowerExact
open AspisV5FriRelationCandidateBridge
open AspisV6TranscriptRelationGrammar

/-- The actual values read by the pure pre-query calculation. In particular,
secondOodWeightsAtMix and secondOodClaimAtMix are values, not response functions. -/
structure ExactK13EvaluatedPreQueryReads where
  disclosedFinal256 : Fin 256 → QM31Exact
  initialWeights : Fin 1024 → QM31Exact
  initialClaim : QM31Exact
  firstOodWeights : Fin 1024 → QM31Exact
  firstOodClaim : QM31Exact
  secondOodWeightsAtMix : Fin 1024 → QM31Exact
  secondOodClaimAtMix : QM31Exact
  firstMix : QM31Exact
  secondMix : QM31Exact
  relationRoundZero : RelationRoundParts QM31Exact
  alphaZero : QM31Exact
  quarter : QM31Exact

def evaluatedReads (input : ExactK13PreQueryExecutionInput) :
    ExactK13EvaluatedPreQueryReads where
  disclosedFinal256 := input.disclosedFinal256
  initialWeights := input.initialWeights
  initialClaim := input.initialClaim
  firstOodWeights := input.firstOodWeights
  firstOodClaim := input.firstOodClaim
  secondOodWeightsAtMix := input.secondOodWeights input.firstMix
  secondOodClaimAtMix := input.secondOodClaim input.firstMix
  firstMix := input.firstMix
  secondMix := input.secondMix
  relationRoundZero := input.relationRoundZero
  alphaZero := input.alphaZero
  quarter := input.quarter

/-- Embed evaluated data using constant continuations. They are used only to
reuse the existing evaluator, not to assert constant production continuations. -/
def ExactK13EvaluatedPreQueryReads.toInput
    (reads : ExactK13EvaluatedPreQueryReads) : ExactK13PreQueryExecutionInput where
  disclosedFinal256 := reads.disclosedFinal256
  initialWeights := reads.initialWeights
  initialClaim := reads.initialClaim
  firstOodWeights := reads.firstOodWeights
  firstOodClaim := reads.firstOodClaim
  secondOodWeights := fun _ => reads.secondOodWeightsAtMix
  secondOodClaim := fun _ => reads.secondOodClaimAtMix
  firstMix := reads.firstMix
  secondMix := reads.secondMix
  relationRoundZero := reads.relationRoundZero
  alphaZero := reads.alphaZero
  quarter := reads.quarter

/-- mixedWeights reads secondOod only at firstMix. The proof is a small
projection/beta identity, not evaluation of a 1024-entry concrete vector. -/
theorem evaluatedReads_snapshot_exact (input : ExactK13PreQueryExecutionInput) :
    (evaluatedReads input).toInput.snapshot = input.snapshot := by
  rfl

def executionReads (execution : CandidateExecution QM31Exact) :
    ExactK13EvaluatedPreQueryReads :=
  evaluatedReads (exactK13PreQueryExecutionInput execution)

theorem executionReads_snapshot_exact (execution : CandidateExecution QM31Exact) :
    (executionReads execution).toInput.snapshot =
      exactK13PreQueryExecutionSnapshot execution := by
  unfold executionReads
  rw [evaluatedReads_snapshot_exact, preQueryExecutionInput_snapshot_exact]

theorem executionReads_discrepancy_exact
    (execution : CandidateExecution QM31Exact) :
    (executionReads execution).toInput.snapshot.discrepancy =
      preQueryDiscrepancy execution := by
  rw [executionReads_snapshot_exact]
  exact (preQueryDiscrepancy_eq_projection execution).symm

/-- This is a genuine read-footprint congruence theorem, not the unproved
claim that two compiler executions have equal read footprints. -/
theorem preQueryDiscrepancy_eq_of_executionReads_eq
    (left right : CandidateExecution QM31Exact)
    (readsExact : executionReads left = executionReads right) :
    preQueryDiscrepancy left = preQueryDiscrepancy right := by
  calc
    preQueryDiscrepancy left =
        (executionReads left).toInput.snapshot.discrepancy :=
      (executionReads_discrepancy_exact left).symm
    _ = (executionReads right).toInput.snapshot.discrepancy :=
      congrArg (fun reads : ExactK13EvaluatedPreQueryReads =>
        reads.toInput.snapshot.discrepancy) readsExact
    _ = preQueryDiscrepancy right := executionReads_discrepancy_exact right

/-- The repaired *full-length finite-sum specification* is exactly the current
algebraic snapshot discrepancy. Linking WeightAccumulator::dot to this sum is
still a separate source theorem; no dot-correctness premise is hidden here. -/
theorem full_length_snapshot_spec_exact
    (snapshot : ExactK13PreQueryExecutionSnapshot) :
    snapshot.claimAfterRoundZero -
        dotThrough 256 snapshot.foldedOodWeights256 snapshot.disclosedFinal256 =
      snapshot.discrepancy := by
  rw [dotThrough_256]
  rfl

#print axioms evaluatedReads_snapshot_exact
#print axioms executionReads_snapshot_exact
#print axioms executionReads_discrepancy_exact
#print axioms preQueryDiscrepancy_eq_of_executionReads_eq
#print axioms full_length_snapshot_spec_exact

end AspisK1.V7Tag73K13EvaluatedPreQueryReads
