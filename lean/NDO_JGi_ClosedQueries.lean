import RPz7_S1ClosedPreparationHashCodeV1
set_option autoImplicit false
namespace AspisR1.JGi_ClosedQueries
open AspisR1PublicPreparation AspisR1CurrentCaller.BorrowedClaimPrepared

theorem source : @PreparedModel.Boundaries.queries closedHashBoundaries.sampling=
    @QueriesModel.queries closedHashQueries := by
  have h := congrArg (fun B : PreparedScratchModel.Boundaries => @PreparedModel.Boundaries.queries B.sampling)
    closedHashBoundaries_queries
  change @QueriesModel.queries closedHashQueries=@PreparedModel.Boundaries.queries closedHashBoundaries.sampling at h
  exact h.symm
#print axioms source
end AspisR1.JGi_ClosedQueries
