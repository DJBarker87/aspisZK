import Aeneas
import QueryValidatorGeneratedPrefix
import QueryValidatorChunkArrayBridge
import QueryValidatorGateInversion
import Aeneas.Tactic.Solver.ScalarTac
open Aeneas Aeneas.Std Result AspisR1Stage2AdoptedResume
namespace AspisR1.QueryValidateIndexBoundary
abbrev QueryArray := Array Std.U32 22#usize

theorem index8_calls_false
    (queries : QueryArray) (index : Usize)
    (hindex : index.val = 8)
    (hsuccess : verifier.validate_query_index queries index = ok (core.result.Result.Ok ())) :
    verifier.query_duplicate_chunk0 queries (queries.val[index.val]!) 8#usize = ok false ∧
    verifier.query_duplicate_chunk1 queries (queries.val[index.val]!) 0#usize = ok false ∧
    verifier.query_duplicate_chunk2 queries (queries.val[index.val]!) 0#usize = ok false := by
  have hi : index = 8#usize := UScalar.val_eq_imp index 8#usize (by simpa using hindex)
  have hidx : Array.index_usize queries index = ok queries.val[index.val]! :=
    AspisR1.QueryValidatorChunkArrayBridge.index_ok_gen queries index (by scalar_tac)
  have hshift : (1#u32 <<< 18#i32) = ok (262144#u32) := by rfl
  have hge : ¬ (queries.val[index.val]! ≥ 262144#u32) := by
    intro hbad
    have hcontr : ok (core.result.Result.Err verifier.Error.Checkpoint) = ok (core.result.Result.Ok ()) := by
      simpa only [verifier.validate_query_index, hidx, hshift, bind_tc_ok, if_pos hbad] using hsuccess
    cases hcontr
  have h8v : (8#usize).val = 8 := by decide
  have h16v : (16#usize).val = 16 := by decide
  have hlt8 : ¬ index < 8#usize := by
    intro hh
    have hn := (UScalar.lt_equiv _ _).1 hh
    rw [hindex, h8v] at hn
    omega
  have hle8 : index ≤ 8#usize := by
    apply (UScalar.le_equiv _ _).2
    rw [hindex, h8v]
  have hle16 : index ≤ 16#usize := by
    apply (UScalar.le_equiv _ _).2
    rw [hindex, h16v]
    omega
  have hbranch : (do
      let b0 ← verifier.query_duplicate_chunk0 queries (queries.val[index.val]!) 8#usize
      if b0 then ok (core.result.Result.Err verifier.Error.Checkpoint) else do
        let b1 ← verifier.query_duplicate_chunk1 queries (queries.val[index.val]!) 0#usize
        if b1 then ok (core.result.Result.Err verifier.Error.Checkpoint) else do
          let b2 ← verifier.query_duplicate_chunk2 queries (queries.val[index.val]!) 0#usize
          if b2 then ok (core.result.Result.Err verifier.Error.Checkpoint)
            else ok (core.result.Result.Ok ())) = ok (core.result.Result.Ok ()) := by
    simpa only [verifier.validate_query_index, hidx, hshift, bind_tc_ok,
      if_neg hge, if_neg hlt8, if_pos hle8, if_pos hle16] using hsuccess
  exact AspisR1.QueryValidatorGateInversion.three_false_of_gates verifier.Error.Checkpoint _ _ _ hbranch

theorem index16_calls_false
    (queries : QueryArray) (index : Usize)
    (hindex : index.val = 16)
    (hsuccess : verifier.validate_query_index queries index = ok (core.result.Result.Ok ())) :
    verifier.query_duplicate_chunk0 queries (queries.val[index.val]!) 8#usize = ok false ∧
    verifier.query_duplicate_chunk1 queries (queries.val[index.val]!) 8#usize = ok false ∧
    verifier.query_duplicate_chunk2 queries (queries.val[index.val]!) 0#usize = ok false := by
  have hi : index = 16#usize := UScalar.val_eq_imp index 16#usize (by simpa using hindex)
  have hidx : Array.index_usize queries index = ok queries.val[index.val]! :=
    AspisR1.QueryValidatorChunkArrayBridge.index_ok_gen queries index (by scalar_tac)
  have hshift : (1#u32 <<< 18#i32) = ok (262144#u32) := by rfl
  have hge : ¬ (queries.val[index.val]! ≥ 262144#u32) := by
    intro hbad
    have hcontr : ok (core.result.Result.Err verifier.Error.Checkpoint) = ok (core.result.Result.Ok ()) := by
      simpa only [verifier.validate_query_index, hidx, hshift, bind_tc_ok, if_pos hbad] using hsuccess
    cases hcontr
  have h8v : (8#usize).val = 8 := by decide
  have h16v : (16#usize).val = 16 := by decide
  have hlt8 : ¬ index < 8#usize := by
    intro hh
    have hn := (UScalar.lt_equiv _ _).1 hh
    rw [hindex, h8v] at hn
    omega
  have hnotle8 : ¬ index ≤ 8#usize := by
    intro hh
    have hn := (UScalar.le_equiv _ _).1 hh
    rw [hindex, h8v] at hn
    omega
  have hnotlt16 : ¬ index < 16#usize := by
    intro hh
    have hn := (UScalar.lt_equiv _ _).1 hh
    rw [hindex, h16v] at hn
    omega
  have hle16 : index ≤ 16#usize := by
    apply (UScalar.le_equiv _ _).2
    rw [hindex, h16v]
  have hbranch : (do
      let b0 ← verifier.query_duplicate_chunk0 queries (queries.val[index.val]!) 8#usize
      if b0 then ok (core.result.Result.Err verifier.Error.Checkpoint) else do
        let b1 ← verifier.query_duplicate_chunk1 queries (queries.val[index.val]!) 8#usize
        if b1 then ok (core.result.Result.Err verifier.Error.Checkpoint) else do
          let b2 ← verifier.query_duplicate_chunk2 queries (queries.val[index.val]!) 0#usize
          if b2 then ok (core.result.Result.Err verifier.Error.Checkpoint)
            else ok (core.result.Result.Ok ())) = ok (core.result.Result.Ok ()) := by
    simpa only [verifier.validate_query_index, hidx, hshift, bind_tc_ok,
      if_neg hge, if_neg hlt8, if_neg hnotle8, if_neg hnotlt16, if_pos hle16] using hsuccess
  exact AspisR1.QueryValidatorGateInversion.three_false_of_gates verifier.Error.Checkpoint _ _ _ hbranch

#print axioms index8_calls_false
#print axioms index16_calls_false
end AspisR1.QueryValidateIndexBoundary
