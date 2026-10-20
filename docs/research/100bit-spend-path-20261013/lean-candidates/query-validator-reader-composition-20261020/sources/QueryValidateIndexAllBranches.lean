import Aeneas
import QueryValidatorGeneratedPrefix
import QueryValidatorLoopInvariant
import QueryValidateIndexBranch0Sound
import QueryValidateIndexBranch1Sound
import QueryValidateIndexBranch2Sound
import QueryValidateIndexBoundarySound
open Aeneas Aeneas.Std Result AspisR1Stage2AdoptedResume
namespace AspisR1.QueryValidateIndexAllBranches
abbrev QueryArray := Array Std.U32 22#usize
open AspisR1.QueryValidatorLoopInvariant

theorem successful_index_validAt
    (queries : QueryArray) (index : Usize)
    (hbound : index.val < 22)
    (hsuccess : verifier.validate_query_index queries index = ok (core.result.Result.Ok ())) :
    validAt queries index := by
  by_cases hlt8 : index.val < 8
  · apply AspisR1.QueryValidateIndexBranch0Sound.branch0_success_validAt queries index
    · simpa [UScalar.lt_equiv] using hlt8
    · exact hsuccess
  · by_cases heq8 : index.val = 8
    · exact AspisR1.QueryValidateIndexBoundarySound.index8_success_validAt queries index heq8 hsuccess
    · by_cases hlt16 : index.val < 16
      · apply AspisR1.QueryValidateIndexBranch1Sound.branch1_success_validAt queries index
        · constructor <;> omega
        · exact hsuccess
      · by_cases heq16 : index.val = 16
        · exact AspisR1.QueryValidateIndexBoundarySound.index16_success_validAt queries index heq16 hsuccess
        · apply AspisR1.QueryValidateIndexBranch2Sound.branch2_success_validAt queries index
          · constructor <;> omega
          · exact hsuccess

#print axioms successful_index_validAt
end AspisR1.QueryValidateIndexAllBranches
