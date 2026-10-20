import Aeneas
import QueryValidatorGeneratedPrefix
import QueryValidatorChunkArrayBridge
import QueryValidatorChunks12NoHit
import QueryValidatorGateInversion
import Aeneas.Tactic.Solver.ScalarTac
open Aeneas Aeneas.Std Result AspisR1Stage2AdoptedResume
namespace AspisR1.QueryValidateIndexBranch0
abbrev QueryArray := Array Std.U32 22#usize

theorem branch0_calls_false
    (queries : QueryArray) (index : Usize)
    (hindex : index < 8#usize)
    (hsuccess : verifier.validate_query_index queries index =
      ok (core.result.Result.Ok ())) :
    verifier.query_duplicate_chunk0 queries (queries.val[index.val]!) index = ok false ∧
    verifier.query_duplicate_chunk1 queries (queries.val[index.val]!) 0#usize = ok false ∧
    verifier.query_duplicate_chunk2 queries (queries.val[index.val]!) 0#usize = ok false := by
  have hidx : Array.index_usize queries index = ok queries.val[index.val]! :=
    AspisR1.QueryValidatorChunkArrayBridge.index_ok_gen queries index (by scalar_tac)
  have hshift : (1#u32 <<< 18#i32) = ok (262144#u32) := by rfl
  have hge : ¬ (queries.val[index.val]! ≥ 262144#u32) := by
    intro hbad
    have hcontra : ok (core.result.Result.Err verifier.Error.Checkpoint) =
        ok (core.result.Result.Ok ()) := by
      simpa only [verifier.validate_query_index, hidx, hshift, bind_tc_ok, if_pos hbad]
        using hsuccess
    cases hcontra
  have hindex8 : index.val < 8 := by simpa [UScalar.lt_equiv] using hindex
  have hle8 : index ≤ 8#usize := by
    have hn : index.val ≤ 8 := by omega
    simpa [UScalar.le_equiv] using hn
  have hle16 : index ≤ 16#usize := by
    have hn : index.val ≤ 16 := by omega
    simpa [UScalar.le_equiv] using hn
  have hbranch : (do
      let b ← verifier.query_duplicate_chunk0 queries (queries.val[index.val]!) index
      if b then ok (core.result.Result.Err verifier.Error.Checkpoint) else do
        let b1 ← verifier.query_duplicate_chunk1 queries (queries.val[index.val]!) 0#usize
        if b1 then ok (core.result.Result.Err verifier.Error.Checkpoint) else do
          let b2 ← verifier.query_duplicate_chunk2 queries (queries.val[index.val]!) 0#usize
          if b2 then ok (core.result.Result.Err verifier.Error.Checkpoint) else
            ok (core.result.Result.Ok ())) = ok (core.result.Result.Ok ()) := by
    simpa only [verifier.validate_query_index, hidx, hshift, bind_tc_ok,
      if_neg hge, if_pos hindex, if_pos hle8, if_pos hle16] using hsuccess
  exact AspisR1.QueryValidatorGateInversion.three_false_of_gates verifier.Error.Checkpoint
    _ _ _ hbranch
end AspisR1.QueryValidateIndexBranch0
