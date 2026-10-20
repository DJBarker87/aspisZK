import Aeneas
import QueryValidatorGeneratedPrefix
import QueryValidatorLoopInvariant
import QueryValidateIndexAllBranches
import QueryValidateIndexTotal
open Aeneas Aeneas.Std Result AspisR1Stage2AdoptedResume
namespace AspisR1.QueryValidateQueriesSuccessNoTotality
abbrev QueryArray := Array Std.U32 22#usize
open AspisR1.QueryValidatorLoopInvariant

theorem validate_queries_success_sound
    (queries : QueryArray)
    (hvalidate : verifier.validate_queries queries = ok (core.result.Result.Ok ())) :
    ∀ i : Usize, i.val < 22 → validAt queries i := by
  apply AspisR1.QueryValidatorLoopInvariant.validate_queries_success_sound queries
    (fun i hi => AspisR1.QueryValidateIndexTotal.validate_query_index_total queries i hi)
  · intro i hi hcheck
    unfold indexCheckOK at hcheck
    exact AspisR1.QueryValidateIndexAllBranches.successful_index_validAt queries i hi hcheck
  · exact hvalidate

#print axioms validate_queries_success_sound
end AspisR1.QueryValidateQueriesSuccessNoTotality
