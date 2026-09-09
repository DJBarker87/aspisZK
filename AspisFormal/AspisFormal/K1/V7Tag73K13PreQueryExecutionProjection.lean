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
open AspisV5RelationSumcheckSoundness
open AspisV6TranscriptRelationGrammar

/-- Exactly the three production values read by the pre-query subtraction. -/
structure ExactK13PreQueryExecutionSnapshot where
  claimAfterRoundZero : QM31Exact
  foldedOodWeights256 : Fin 256 → QM31Exact
  disclosedFinal256 : Fin 256 → QM31Exact

/-- The exact production inputs needed to compute the pre-query snapshot.
Fields used only after query injection, and the 1024 candidate values, are
deliberately absent.  This is the small literal state an Aeneas/source bridge
must preserve before the query-batch challenge is returned. -/
structure ExactK13PreQueryExecutionInput where
  disclosedFinal256 : Fin 256 → QM31Exact
  initialWeights : Fin 1024 → QM31Exact
  initialClaim : QM31Exact
  firstOodWeights : Fin 1024 → QM31Exact
  firstOodClaim : QM31Exact
  secondOodWeights : QM31Exact → Fin 1024 → QM31Exact
  secondOodClaim : QM31Exact → QM31Exact
  firstMix : QM31Exact
  secondMix : QM31Exact
  relationRoundZero : RelationRoundParts QM31Exact
  alphaZero : QM31Exact
  quarter : QM31Exact

/-- Literal projection of the maintained candidate state before query
injection.  The quarter witness is not included because it proves validity of
the field constant but does not affect the computed snapshot. -/
def exactK13PreQueryExecutionInput
    (execution : CandidateExecution QM31Exact) :
    ExactK13PreQueryExecutionInput where
  disclosedFinal256 := execution.disclosedFinal256
  initialWeights := execution.initialWeights
  initialClaim := execution.initialClaim
  firstOodWeights := execution.firstOodWeights
  firstOodClaim := execution.firstOodClaim
  secondOodWeights := execution.secondOodWeights
  secondOodClaim := execution.secondOodClaim
  firstMix := execution.firstMix
  secondMix := execution.secondMix
  relationRoundZero := execution.relationParts 0
  alphaZero := execution.alpha 0
  quarter := execution.quarter

/-- Pure reconstruction of the three values read before query injection. -/
def ExactK13PreQueryExecutionInput.snapshot
    (input : ExactK13PreQueryExecutionInput) :
    ExactK13PreQueryExecutionSnapshot where
  claimAfterRoundZero :=
    relationEvaluate input.quarter
      (input.initialClaim + input.firstMix * input.firstOodClaim +
        input.secondMix * input.secondOodClaim input.firstMix)
      input.relationRoundZero input.alphaZero
  foldedOodWeights256 :=
    dualWeightFoldLayer 256 input.alphaZero
      (mixedWeights (n := 256) input.initialWeights input.firstOodWeights
        input.secondOodWeights input.firstMix input.secondMix)
  disclosedFinal256 := input.disclosedFinal256

/-- Literal snapshot from the maintained candidate execution. -/
def exactK13PreQueryExecutionSnapshot
    (execution : CandidateExecution QM31Exact) :
    ExactK13PreQueryExecutionSnapshot where
  claimAfterRoundZero := execution.claimAfterRound0
  foldedOodWeights256 := execution.foldedOodWeights256
  disclosedFinal256 := execution.disclosedFinal256

/-- The minimal literal input reconstructs exactly the maintained candidate
snapshot; no query-batch or later-round field is involved. -/
theorem preQueryExecutionInput_snapshot_exact
    (execution : CandidateExecution QM31Exact) :
    (exactK13PreQueryExecutionInput execution).snapshot =
      exactK13PreQueryExecutionSnapshot execution := by
  rfl

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
#print axioms preQueryExecutionInput_snapshot_exact

end AspisK1.V7Tag73K13PreQueryExecutionProjection
