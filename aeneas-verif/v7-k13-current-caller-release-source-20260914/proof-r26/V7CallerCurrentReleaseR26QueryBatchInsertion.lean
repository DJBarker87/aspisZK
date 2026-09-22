import V7CallerCurrentReleaseR26.Funs

/-!
# Literal source trace for Tag-73 query-batch insertion

This theorem decomposes one successful translated execution of
`add_v7_final256_query_batch_shifted`.  It exposes the exact ordered shifted
rho scale chain,
the exact line-covector insertion call, the exact dot-product call over the
authenticated folded values, and the exact running-claim update.  It makes no
pointwise final-polynomial claim.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26QueryBatchInsertion

abbrev RawQM31 := field.QM31
abbrev RawWeights := sumcheck.WeightAccumulator
abbrev AuthenticatedBatch := v6_query_batch.V6AuthenticatedQueryBatch

/-- Every field is an actual intermediate result from the same successful
translated call. The scale-loop result is retained as a named source value so
its symbolic recurrence can be proved separately. -/
structure AcceptedQueryBatchInsertionTrace
    (weights : RawWeights) (runningClaim : RawQM31)
    (queries : Array Std.U32 16#usize)
    (authenticated : AuthenticatedBatch) (rho : RawQM31)
    (claimIncrement : RawQM31) (weightsAfter : RawWeights)
    (runningClaimAfter : RawQM31) : Type where
  seed : Array RawQM31 16#usize
  seedSuccess :
    Array.update (Array.repeat 16#usize field.QM31.ZERO) 0#usize rho = ok seed
  preparedRho : field.PreparedQm31Multiplier
  preparedRhoSuccess :
    field.PreparedQm31Multiplier.impl.new rho = ok preparedRho
  scales : Array RawQM31 16#usize
  scalesLoopSuccess :
    v6_query_batch.add_final256_query_batch_with_initial_scale_loop
      { start := 1#usize, «end» := v6_query_batch.V6_QUERY_BATCH_COUNT }
      seed preparedRho = ok scales
  weightsInsertSuccess :
    sumcheck.WeightAccumulator.impl.add_line_m31_batch weights
        (Array.to_slice scales) (Array.to_slice authenticated.line_x) =
      ok (core.result.Result.Ok (), weightsAfter)
  claimDotSuccess :
    field.qm31_dot (Array.to_slice scales)
      (Array.to_slice authenticated.values) = ok claimIncrement
  runningClaimSuccess :
    field.QM31.add runningClaim claimIncrement = ok runningClaimAfter

/-- Accepted normalized production source exposes the exact query-batch
insertion data.  Validation intermediates are eliminated from the conclusion:
their only role here is selecting the successful branch before the arithmetic
shown in the trace. -/
theorem accepted_query_batch_exposes_exact_insertion
    (weights : RawWeights) (runningClaim : RawQM31)
    (queries : Array Std.U32 16#usize)
    (authenticated : AuthenticatedBatch) (rho : RawQM31)
    (claimIncrement : RawQM31) (weightsAfter : RawWeights)
    (runningClaimAfter : RawQM31)
    (success : v6_query_batch.add_v7_final256_query_batch_shifted weights runningClaim
      queries authenticated rho =
        ok (core.result.Result.Ok claimIncrement, weightsAfter,
          runningClaimAfter)) :
    Nonempty (AcceptedQueryBatchInsertionTrace weights runningClaim queries
      authenticated rho claimIncrement weightsAfter runningClaimAfter) := by
  unfold v6_query_batch.add_v7_final256_query_batch_shifted at success
  unfold v6_query_batch.add_final256_query_batch_with_initial_scale at success
  simp only [lift, Array.to_slice_mut, Bind.bind,
    Aeneas.Std.bind] at success
  cases hsort : core.slice.Slice.sort_unstable core.cmp.OrdU32
      (Array.to_slice queries) <;> simp [hsort] at success
  rename_i sortedSlice
  generalize hcountMinus : Std.Usize.wrapping_sub
      v6_query_batch.V6_QUERY_BATCH_COUNT 1#usize = lastOrdinal at success
  cases hlast : Array.index_usize
      (Array.from_slice queries sortedSlice) lastOrdinal <;>
    rw [hlast] at success <;> dsimp at success
  all_goals first | cases success | skip
  rename_i lastQuery
  generalize hshift : Std.U32.wrapping_shl 1#u32
      (UScalar.cast .U32 v6_query_batch.V6_QUERY_BATCH_TREE_DEPTH) = domainSize at success
  by_cases hout : domainSize.val ≤ lastQuery.val
  · simp [hout] at success
  · simp [hout] at success
    cases hwindows : core.slice.Slice.windows
        (Array.to_slice (Array.from_slice queries sortedSlice)) 2#usize <;>
      simp [hwindows] at success
    rename_i windows
    cases hany : core.iter.traits.iterator.Iterator.any.default
        (core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice
          Std.U32)
        v6_query_batch.add_final256_query_batch_with_initial_scale.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU32Bool
        windows () <;> simp [hany] at success
    rename_i anyResult
    rcases anyResult with ⟨hasDuplicate, windowsAfter⟩
    cases hasDuplicate
    · simp at success
      cases hseed : Array.update (Array.repeat 16#usize field.QM31.ZERO)
          0#usize rho <;> simp [hseed] at success
      rename_i seed
      cases hprepared : field.PreparedQm31Multiplier.impl.new rho <;>
        simp [hprepared] at success
      rename_i preparedRho
      cases hscales : v6_query_batch.add_final256_query_batch_with_initial_scale_loop
          { start := 1#usize, «end» := v6_query_batch.V6_QUERY_BATCH_COUNT }
          seed preparedRho <;> simp [hscales] at success
      rename_i scales
      cases hweights : sumcheck.WeightAccumulator.impl.add_line_m31_batch weights
          (Array.to_slice scales) (Array.to_slice authenticated.line_x) <;>
        simp [hweights] at success
      rename_i weightResult
      rcases weightResult with ⟨result, weightsCandidate⟩
      cases result with
      | Err error =>
        simp [core.result.Result.map_err,
          v6_query_batch.add_final256_query_batch_with_initial_scale.closure_1.Insts.CoreOpsFunctionFnOnceTupleTensorWeightErrorV6QueryBatchError.call_once,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
          at success
      | Ok weightUnit =>
        simp [core.result.Result.map_err,
          core.result.Result.Insts.CoreOpsTry.branch] at success
        cases hdot : field.qm31_dot
            (Array.to_slice scales) (Array.to_slice authenticated.values) <;>
          simp [hdot] at success
        rename_i claimCandidate
        cases hadd : field.QM31.add runningClaim claimCandidate <;>
          simp [hadd] at success
        rename_i runningCandidate
        rcases success with ⟨hclaim, hweightsAfter, hrunningAfter⟩
        subst claimCandidate
        subst weightsCandidate
        subst runningCandidate
        cases weightUnit
        refine ⟨{
          seed := seed
          seedSuccess := hseed
          preparedRho := preparedRho
          preparedRhoSuccess := hprepared
          scales := scales
          scalesLoopSuccess := hscales
          weightsInsertSuccess := by simpa using hweights
          claimDotSuccess := by simpa using hdot
          runningClaimSuccess := hadd }⟩
    · simp at success
#print axioms accepted_query_batch_exposes_exact_insertion

end V7CallerCurrentReleaseR26QueryBatchInsertion
