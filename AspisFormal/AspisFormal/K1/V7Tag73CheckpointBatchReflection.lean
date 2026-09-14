import AspisFormal.K1.V7Tag73K13CommittedPreChallengeData
import AspisFormal.K1.V7Tag73RestoredJointBatchKernel

/-!
# Existing committed-source reads to the restored batch target

This adapter reuses the existing 256-wide snapshot, parsed final vector,
schedule, and K1.2-derived initial word. It does not equate the parsed final
vector with the execution copy by fiat. Those two copies remain distinct in
ExactK13CommittedPreChallengeInput and in the source obligations.
-/
set_option autoImplicit false
namespace AspisK1.V7Tag73CheckpointBatchReflection
open AspisK1.V7Tag73K13CommittedPreChallengeData
open AspisK1.V7Tag73K13PreQueryExecutionProjection
open AspisK1.V7Tag73RestoredJointBatchKernel
open AspisK1.V7Tag73JointQueryBatchSoundness
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact
noncomputable section

/-- Compute the batch target's data from the existing literal read package. -/
def committedBatchCheckpoint (decoder : ExactDecoderInstantiation QM31Exact)
    (input : ExactK13CommittedPreChallengeInput) : BatchCheckpoint QM31Exact where
  priorDiscrepancy := input.snapshot.discrepancy
  expected := input.expected decoder
  authenticated := input.authenticated

theorem committedBatchCheckpoint_congr (decoder : ExactDecoderInstantiation QM31Exact)
    (left right : ExactK13CommittedPreChallengeInput) (same : left = right) :
    committedBatchCheckpoint decoder left = committedBatchCheckpoint decoder right :=
  congrArg (committedBatchCheckpoint decoder) same

/-- Only the already-proved field components are used to prove target equality. -/
theorem batchCheckpoint_eq_of_reads
    (left right : BatchCheckpoint QM31Exact)
    (scalar : left.priorDiscrepancy = right.priorDiscrepancy)
    (expected : left.expected = right.expected)
    (authenticated : left.authenticated = right.authenticated) : left = right := by
  cases left
  cases right
  cases scalar
  cases expected
  cases authenticated
  rfl

theorem committed_target_congr (decoder : ExactDecoderInstantiation QM31Exact)
    (left right : ExactK13CommittedPreChallengeInput) (same : left = right) :
    (committedBatchCheckpoint decoder left).target =
      (committedBatchCheckpoint decoder right).target := by rw [same]

/-- The target cardinality is inherited from the actual repository polynomial. -/
theorem committed_target_card_le (decoder : ExactDecoderInstantiation QM31Exact)
    (input : ExactK13CommittedPreChallengeInput)
    (different : input.expected decoder ≠ input.authenticated) :
    (committedBatchCheckpoint decoder input).target.card ≤ 16 :=
  checkpoint_target_card _ different

/-- No uniformity claim: this is just the deterministic source-to-root-set step. -/
theorem committed_zero_discrepancy_is_target
    (decoder : ExactDecoderInstantiation QM31Exact)
    (input : ExactK13CommittedPreChallengeInput) (rho : QM31Exact)
    (nonzero : rho ≠ 0)
    (zero : jointQueryBatchDiscrepancy input.snapshot.discrepancy
      (input.expected decoder) input.authenticated rho = 0) :
    rho ∈ (committedBatchCheckpoint decoder input).target :=
  zero_discrepancy_mem_checkpoint _ rho nonzero zero

#print axioms committedBatchCheckpoint_congr
#print axioms batchCheckpoint_eq_of_reads
#print axioms committed_target_congr
#print axioms committed_target_card_le
#print axioms committed_zero_discrepancy_is_target
end
end AspisK1.V7Tag73CheckpointBatchReflection
