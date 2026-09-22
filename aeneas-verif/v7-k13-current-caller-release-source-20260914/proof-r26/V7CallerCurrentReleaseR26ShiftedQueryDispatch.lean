import V7CallerCurrentReleaseR26.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7CallerCurrentReleaseR26ShiftedQueryDispatch

open V7CallerCurrentReleaseR26

/-- The current production Tag-73 helper is exactly the shared final256
inserter with both the multiplier and initial scale set to the sampled query
challenge.  This pins the source-level `rho, rho^2, …` recurrence entry point
used by the later loop-invariant proof. -/
theorem shifted_query_helper_uses_rho_as_initial_scale
    (weights : sumcheck.WeightAccumulator) (runningClaim : field.QM31)
    (queries : Array Std.U32 16#usize)
    (authenticated : v6_query_batch.V6AuthenticatedQueryBatch)
    (rho : field.QM31) :
    v6_query_batch.add_v7_final256_query_batch_shifted weights runningClaim
        queries authenticated rho =
      v6_query_batch.add_final256_query_batch_with_initial_scale weights runningClaim
        queries authenticated rho rho := by
  rfl

#print axioms shifted_query_helper_uses_rho_as_initial_scale

end V7CallerCurrentReleaseR26ShiftedQueryDispatch
