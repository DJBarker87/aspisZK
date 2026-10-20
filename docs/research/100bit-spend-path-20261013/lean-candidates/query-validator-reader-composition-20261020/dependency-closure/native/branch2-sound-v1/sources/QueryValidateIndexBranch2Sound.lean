import Aeneas
import QueryValidatorGeneratedPrefix
import QueryValidatorChunkArrayBridge
import QueryValidatorChunkNoHitValues
import QueryValidateIndexBranch2
import QueryValidatorLoopInvariant
import Aeneas.Tactic.Solver.ScalarTac
open Aeneas Aeneas.Std Result AspisR1Stage2AdoptedResume
namespace AspisR1.QueryValidateIndexBranch2Sound
abbrev QueryArray := Array Std.U32 22#usize
open AspisR1.QueryValidatorLoopInvariant
open AspisR1.QueryValidatorChunkNoHitValues

theorem branch2_success_validAt
    (queries : QueryArray) (index : Usize)
    (hindex : 16 < index.val ∧ index.val < 22)
    (hsuccess : verifier.validate_query_index queries index =
      ok (core.result.Result.Ok ())) : validAt queries index := by
  obtain ⟨count2, hsub, hcount2, h0, h1, h2⟩ :=
    AspisR1.QueryValidateIndexBranch2.branch2_calls_false queries index hindex hsuccess
  have hbound : index.val < 22 := hindex.2
  have hidx : Array.index_usize queries index = ok queries.val[index.val]! :=
    AspisR1.QueryValidatorChunkArrayBridge.index_ok_gen queries index (by scalar_tac)
  have hshift : (1#u32 <<< 18#i32) = ok (262144#u32) := by rfl
  have hge : ¬ (queries.val[index.val]! ≥ 262144#u32) := by
    intro hbad
    have hcontr : ok (core.result.Result.Err verifier.Error.Checkpoint) =
        ok (core.result.Result.Ok ()) := by
      simpa only [verifier.validate_query_index, hidx, hshift, bind_tc_ok, if_pos hbad]
        using hsuccess
    cases hcontr
  unfold validAt
  constructor
  · exact hbound
  constructor
  · have hnat : (queries.val[index.val]!).val < 2 ^ 18 := by
      by_contra hn
      have hle : 262144 ≤ (queries.val[index.val]!).val := by omega
      have hge' : (queries.val[index.val]!) ≥ 262144#u32 := by
        apply (UScalar.le_equiv _ _).2
        simpa using hle
      exact hge hge'
    exact hnat
  · intro j hj
    by_cases hj8 : j < 8
    · have hne := chunk0_values_nohit queries (queries.val[index.val]!) 8#usize h0 j (by omega) (by scalar_tac)
      intro heq
      exact hne (by simpa [queryValue] using heq)
    · by_cases hj16 : j < 16
      · let k := j - 8
        have hklt8 : k < 8 := by dsimp [k]; omega
        have hkltcount : k < 8 := by dsimp [k]; omega
        have hne := chunk1_values_nohit queries (queries.val[index.val]!) 8#usize h1 k hklt8 hkltcount
        intro heq
        apply hne
        have hkj : k + 8 = j := by dsimp [k]; omega
        simpa [queryValue, hkj] using heq
      · let k := j - 16
        have hklt6 : k < 6 := by dsimp [k]; omega
        have hkltcount : k < count2.val := by rw [hcount2]; dsimp [k]; omega
        have hne := chunk2_values_nohit queries (queries.val[index.val]!) count2 h2 k hklt6 hkltcount
        intro heq
        apply hne
        have hkj : k + 16 = j := by dsimp [k]; omega
        simpa [queryValue, hkj] using heq

#print axioms branch2_success_validAt
end AspisR1.QueryValidateIndexBranch2Sound
