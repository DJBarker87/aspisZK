import Aeneas
import QueryValidatorGeneratedPrefix
import QueryValidatorChunkArrayBridge
import QueryValidatorGateInversion
import Aeneas.Tactic.Solver.ScalarTac
open Aeneas Aeneas.Std Result AspisR1Stage2AdoptedResume
namespace AspisR1.QueryValidateIndexBranch1
abbrev QueryArray := Array Std.U32 22#usize

theorem branch1_calls_false
    (queries : QueryArray) (index : Usize)
    (hindex : 8 < index.val ∧ index.val < 16)
    (hsuccess : verifier.validate_query_index queries index =
      ok (core.result.Result.Ok ())) :
    ∃ count1 : Usize,
      index - 8#usize = ok count1 ∧ count1.val = index.val - 8 ∧
      verifier.query_duplicate_chunk0 queries (queries.val[index.val]!) 8#usize = ok false ∧
      verifier.query_duplicate_chunk1 queries (queries.val[index.val]!) count1 = ok false ∧
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
  have hnot8 : ¬ index < 8#usize := by
    have hn : ¬ index.val < 8 := by omega
    simpa [UScalar.lt_equiv] using hn
  have hnotle8 : ¬ index ≤ 8#usize := by
    have hn : ¬ index.val ≤ 8 := by omega
    simpa [UScalar.le_equiv] using hn
  have hlt16 : index < 16#usize := by
    simpa [UScalar.lt_equiv] using hindex.2
  have hle16 : index ≤ 16#usize := by
    have hn : index.val ≤ 16 := by omega
    simpa [UScalar.le_equiv] using hn
  have h8val : (8#usize).val = 8 := by decide
  have hsubSpec : UScalar.sub index 8#usize
      ⦃ z => z.val = index.val - 8 ∧ 8 ≤ index.val ⦄ := by
    apply UScalar.sub_spec
    rw [h8val]
    omega
  obtain ⟨count1, hsub, hcount1post⟩ := WP.spec_imp_exists hsubSpec
  have hcount1val : count1.val = index.val - 8 := hcount1post.1
  have hsuccess' := hsuccess
  simp only [verifier.validate_query_index, hidx, hshift, bind_tc_ok,
    if_neg hge, if_neg hnot8, if_neg hnotle8, if_pos hlt16, if_pos hle16]
    at hsuccess'
  have hsubExpr : index - 8#usize = ok count1 := hsub
  simp only [hsubExpr, bind_tc_ok] at hsuccess'
  have hbranch : (do
      let b0 ← verifier.query_duplicate_chunk0 queries (queries.val[index.val]!) 8#usize
      if b0 then ok (core.result.Result.Err verifier.Error.Checkpoint) else do
        let b1 ← verifier.query_duplicate_chunk1 queries (queries.val[index.val]!) count1
        if b1 then ok (core.result.Result.Err verifier.Error.Checkpoint) else do
          let b2 ← verifier.query_duplicate_chunk2 queries (queries.val[index.val]!) 0#usize
          if b2 then ok (core.result.Result.Err verifier.Error.Checkpoint)
            else ok (core.result.Result.Ok ())) = ok (core.result.Result.Ok ()) := by
    simpa only [bind_tc_ok] using hsuccess'
  have hfalse := AspisR1.QueryValidatorGateInversion.three_false_of_gates
    verifier.Error.Checkpoint
    (verifier.query_duplicate_chunk0 queries (queries.val[index.val]!) 8#usize)
    (verifier.query_duplicate_chunk1 queries (queries.val[index.val]!) count1)
    (verifier.query_duplicate_chunk2 queries (queries.val[index.val]!) 0#usize)
    (by simpa only [hsub] using hbranch)
  exact ⟨count1, hsub, hcount1val, hfalse.1, hfalse.2.1, hfalse.2.2⟩
end AspisR1.QueryValidateIndexBranch1
