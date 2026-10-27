import R1Z.PV_L2_BoolTrace
import R1Z.PV_L2_F3AttemptSource
import R1Z.PV_L2_F3FullRetry
import R1Z.PV_L2_F3FullSource
import R1Z.PV_L2_F3PrefixBounds
import R1Z.PV_L2_F3SeedFrames
import R1Z.PV_L2_F5DivPass
import R1Z.PV_L2_F5DivStep
import R1Z.PV_L2_F5Mle
import R1Z.PV_L2_F5SparsePred
import R1Z.PV_L2_F5SparseSuffix
import R1Z.PV_L2_F5SparseSum
import R1Z.PV_L2_F5SparseWeight
import R1Z.PV_L2_F5SparseWidth
import R1Z.PV_L2_F6BCond
import R1Z.PV_L2_F6Callers
import R1Z.PV_L2_F6Checker
import R1Z.PV_L2_F6Echelon
import R1Z.PV_L2_F6EchelonRow
import R1Z.PV_L2_F6EchelonRowStep
import R1Z.PV_L2_F6EchelonStep
import R1Z.PV_L2_F6Entries
import R1Z.PV_L2_F6EntriesStep
import R1Z.PV_L2_F6FlagLoop
import R1Z.PV_L2_F6Half
import R1Z.PV_L2_F6HalfInputs
import R1Z.PV_L2_F6HalfPQ
import R1Z.PV_L2_F6HalfR0
import R1Z.PV_L2_F6HalfR1
import R1Z.PV_L2_F6HalfR2
import R1Z.PV_L2_F6HalfR3
import R1Z.PV_L2_F6HalfShift
import R1Z.PV_L2_F6Identity
import R1Z.PV_L2_F6IdentityRow
import R1Z.PV_L2_F6IdentityRowStep
import R1Z.PV_L2_F6IdentityStep
import R1Z.PV_L2_F6Lifts
import R1Z.PV_L2_F6LiftsStep
import R1Z.PV_L2_F6MM
import R1Z.PV_L2_F6Null
import R1Z.PV_L2_F6NullEntry
import R1Z.PV_L2_F6NullFinish
import R1Z.PV_L2_F6NullRow
import R1Z.PV_L2_F6NullRowStep
import R1Z.PV_L2_F6NullStep
import R1Z.PV_L2_F6NullWant
import R1Z.PV_L2_F6PermutationLeft
import R1Z.PV_L2_F6PermutationLeftStep
import R1Z.PV_L2_F6PermutationRight
import R1Z.PV_L2_F6PermutationRightStep
import R1Z.PV_L2_F6QPrime
import R1Z.PV_L2_HeadlineJoint
import R1Z.PV_L2_InversionPole
import R1Z.PV_L2_InversionQ
import R1Z.PV_L2_Premises
import R1Z.PV_L2_PremisesBound
import R1Z.PV_L2_RecordCompact
import R1Z.PV_L2_RecordRefinement
import R1Z.PV_L2_F3SeedFrames
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F3SeedPrefix
open Aeneas Aeneas.Std Result AspisR1ProverStep8 R0Z.FsStatement
open R1Z.ProverCommitStepLoop (State)
open R1Z.ProverCommitOwnedDecoder R1Z.ProverCommitStreamSource
open R1Z.PV_L2_F3SeedFrames
variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]

/-- Full prefix transport under an arbitrary retained E1 seed, including
None, failed reads and divergence. Counts/values are identical; actual seed
frames are substituted throughout the retained ordered read record.
This is the finite counter backend, not an adaptive-ROM equivalence. -/
theorem transport {n : Nat} (answers : Fin n → OracleAnswer) (domain : Slice U8)
    (seed : Bytes32) (L r : Nat) (state : State) :
    PV_L2_F3FullSource.produce (K := K) (blockHash answers) domain L r (reseed seed state) =
      ((PV_L2_F3FullSource.produce (K := K) (blockHash answers) domain L r state).1,
        (PV_L2_F3FullSource.produce (K := K) (blockHash answers) domain L r state).2.map (read seed)) := by
  fun_induction PV_L2_F3FullSource.produce (K := K) (blockHash answers) domain L r state <;>
    rw [PV_L2_F3FullSource.produce]
  all_goals try rfl
  all_goals rw [next_reseed]
  all_goals simp_all +zetaDelta [mapAfter,PV_L2_F3SeedFrames.read]

  all_goals try (split_ifs <;> (first | omega | rfl))
  rename_i L r state answer impossible
  cases hn : prover_commit_reference.next (blockHash answers) domain state <;>
    simp_all +zetaDelta [mapAfter,PV_L2_F3SeedFrames.read]

  rename_i pair
  exact False.elim (impossible pair.1 pair.2 rfl)

#print axioms transport
end R1Z.PV_L2_F3SeedPrefix

/-! Final focused audit of the continuation: no deployment claim. -/
#print axioms R1Z.PV_L2_BoolTrace.value
#print axioms R1Z.PV_L2_BoolTrace.false_prefix
#print axioms R1Z.PV_L2_F3AttemptSource.source_projection
#print axioms R1Z.PV_L2_F3AttemptSource.owned_projection
#print axioms R1Z.PV_L2_F3AttemptSource.complete_l1
#print axioms R1Z.PV_L2_F3FullRetry.full_l1_erases
#print axioms R1Z.PV_L2_F3FullRetry.rejected_prefix
#print axioms R1Z.PV_L2_F3FullRetry.stopping_prefix
#print axioms R1Z.PV_L2_F3FullRetry.rejected_rom_prefix
#print axioms R1Z.PV_L2_F3FullRetry.l1_events
#print axioms R1Z.PV_L2_F3FullSource.erases
#print axioms R1Z.PV_L2_F3FullSource.arrays_erases
#print axioms R1Z.PV_L2_F3FullSource.pair_erases
#print axioms R1Z.PV_L2_F3FullSource.observed_erases
#print axioms R1Z.PV_L2_F3PrefixBounds.read_bound
#print axioms R1Z.PV_L2_F3PrefixBounds.actual_answers
#print axioms R1Z.PV_L2_F3PrefixBounds.request_bound
#print axioms R1Z.PV_L2_F3PrefixBounds.failed_read
#print axioms R1Z.PV_L2_F3PrefixBounds.diverging_read
#print axioms R1Z.PV_L2_F3PrefixBounds.exhausted
#print axioms R1Z.PV_L2_F3SeedFrames.finish
#print axioms R1Z.PV_L2_F3SeedFrames.blockHash_seed
#print axioms R1Z.PV_L2_F3SeedFrames.next_reseed
#print axioms R1Z.PV_L2_F3SeedFrames.actual_answer
#print axioms R1Z.PV_L2_F3SeedFrames.refill_frame
#print axioms R1Z.PV_L2_F3SeedPrefix.transport
#print axioms R1Z.PV_L2_F5DivPass.unroll
#print axioms R1Z.PV_L2_F5DivPass.erases
#print axioms R1Z.PV_L2_F5DivPass.pass_erases
#print axioms R1Z.PV_L2_F5DivStep.erases
#print axioms R1Z.PV_L2_F5DivStep.source_body
#print axioms R1Z.PV_L2_F5DivStep.decrease
#print axioms R1Z.PV_L2_F5Mle.suffix_erases
#print axioms R1Z.PV_L2_F5Mle.erases
#print axioms R1Z.PV_L2_F5SparsePred.one_erases
#print axioms R1Z.PV_L2_F5SparsePred.boolean_erases
#print axioms R1Z.PV_L2_F5SparseSuffix.erases
#print axioms R1Z.PV_L2_F5SparseSum.erases
#print axioms R1Z.PV_L2_F5SparseSum.run_erases
#print axioms R1Z.PV_L2_F5SparseWeight.factor_erases
#print axioms R1Z.PV_L2_F5SparseWeight.erases
#print axioms R1Z.PV_L2_F5SparseWidth.erases
#print axioms R1Z.PV_L2_F5SparseWidth.source_width
#print axioms R1Z.PV_L2_F6BCond.erases
#print axioms R1Z.PV_L2_F6Callers.piv_erases
#print axioms R1Z.PV_L2_F6Callers.image_erases
#print axioms R1Z.PV_L2_F6Callers.product_erases
#print axioms R1Z.PV_L2_F6Checker.erases
#print axioms R1Z.PV_L2_F6Echelon.erases
#print axioms R1Z.PV_L2_F6EchelonRow.erases
#print axioms R1Z.PV_L2_F6EchelonRowStep.recorded_erases
#print axioms R1Z.PV_L2_F6EchelonRowStep.unroll
#print axioms R1Z.PV_L2_F6EchelonRowStep.increment
#print axioms R1Z.PV_L2_F6EchelonStep.recorded_erases
#print axioms R1Z.PV_L2_F6EchelonStep.unroll
#print axioms R1Z.PV_L2_F6EchelonStep.increment
#print axioms R1Z.PV_L2_F6Entries.erases
#print axioms R1Z.PV_L2_F6EntriesStep.recorded_erases
#print axioms R1Z.PV_L2_F6EntriesStep.unroll
#print axioms R1Z.PV_L2_F6EntriesStep.increment
#print axioms R1Z.PV_L2_F6FlagLoop.erases
#print axioms R1Z.PV_L2_F6Half.recorded_erases
#print axioms R1Z.PV_L2_F6Half.source_eq
#print axioms R1Z.PV_L2_F6Half.erases
#print axioms R1Z.PV_L2_F6HalfInputs.erases
#print axioms R1Z.PV_L2_F6HalfPQ.erases
#print axioms R1Z.PV_L2_F6HalfR0.erases
#print axioms R1Z.PV_L2_F6HalfR1.erases
#print axioms R1Z.PV_L2_F6HalfR2.erases
#print axioms R1Z.PV_L2_F6HalfR3.erases
#print axioms R1Z.PV_L2_F6HalfShift.erases
#print axioms R1Z.PV_L2_F6Identity.erases
#print axioms R1Z.PV_L2_F6IdentityRow.erases
#print axioms R1Z.PV_L2_F6IdentityRowStep.recorded_erases
#print axioms R1Z.PV_L2_F6IdentityRowStep.unroll
#print axioms R1Z.PV_L2_F6IdentityRowStep.increment
#print axioms R1Z.PV_L2_F6IdentityStep.recorded_erases
#print axioms R1Z.PV_L2_F6IdentityStep.unroll
#print axioms R1Z.PV_L2_F6IdentityStep.increment
#print axioms R1Z.PV_L2_F6Lifts.erases
#print axioms R1Z.PV_L2_F6LiftsStep.recorded_erases
#print axioms R1Z.PV_L2_F6LiftsStep.unroll
#print axioms R1Z.PV_L2_F6LiftsStep.increment
#print axioms R1Z.PV_L2_F6MM.erases
#print axioms R1Z.PV_L2_F6Null.erases
#print axioms R1Z.PV_L2_F6NullEntry.erases
#print axioms R1Z.PV_L2_F6NullFinish.erases
#print axioms R1Z.PV_L2_F6NullRow.erases
#print axioms R1Z.PV_L2_F6NullRowStep.recorded_erases
#print axioms R1Z.PV_L2_F6NullRowStep.unroll
#print axioms R1Z.PV_L2_F6NullRowStep.increment
#print axioms R1Z.PV_L2_F6NullStep.recorded_erases
#print axioms R1Z.PV_L2_F6NullStep.unroll
#print axioms R1Z.PV_L2_F6NullStep.increment
#print axioms R1Z.PV_L2_F6NullWant.erases
#print axioms R1Z.PV_L2_F6PermutationLeft.erases
#print axioms R1Z.PV_L2_F6PermutationLeftStep.recorded_erases
#print axioms R1Z.PV_L2_F6PermutationLeftStep.unroll
#print axioms R1Z.PV_L2_F6PermutationLeftStep.increment
#print axioms R1Z.PV_L2_F6PermutationRight.erases
#print axioms R1Z.PV_L2_F6PermutationRightStep.recorded_erases
#print axioms R1Z.PV_L2_F6PermutationRightStep.unroll
#print axioms R1Z.PV_L2_F6PermutationRightStep.increment
#print axioms R1Z.PV_L2_F6QPrime.erases
#print axioms R1Z.PV_L2_HeadlineJoint.original_refinement
#print axioms R1Z.PV_L2_HeadlineJoint.agreement_exact
#print axioms R1Z.PV_L2_InversionPole.producer
#print axioms R1Z.PV_L2_InversionPole.consumer
#print axioms R1Z.PV_L2_InversionQ.branch_nonzero
#print axioms R1Z.PV_L2_InversionQ.logup_operand
#print axioms R1Z.PV_L2_InversionQ.logup_all
#print axioms R1Z.PV_L2_InversionQ.zero_exact
#print axioms R1Z.PV_L2_Premises.rows_agree
#print axioms R1Z.PV_L2_Premises.same_coupling
#print axioms R1Z.PV_L2_PremisesBound.joint_test_bound
#print axioms R1Z.PV_L2_RecordCompact.bind_eq
#print axioms R1Z.PV_L2_RecordCompact.bind_value
#print axioms R1Z.PV_L2_RecordCompact.operation_bind_value
#print axioms R1Z.PV_L2_RecordCompact.fail_prefix
#print axioms R1Z.PV_L2_RecordCompact.div_prefix
#print axioms R1Z.PV_L2_RecordRefinement.bind_erases
