import Aeneas
import QueryValidatorGeneratedPrefix
import QueryValidatorChunkArrayBridge
import QueryValidatorGateInversion
import Aeneas.Tactic.Solver.ScalarTac
open Aeneas Aeneas.Std Result AspisR1Stage2AdoptedResume
namespace AspisR1.QueryValidateIndexBranch2
abbrev QueryArray := Array Std.U32 22#usize

theorem branch2_calls_false
    (queries : QueryArray) (index : Usize)
    (hindex : 16 < index.val ∧ index.val < 22)
    (hsuccess : verifier.validate_query_index queries index =
      ok (core.result.Result.Ok ())) :
    ∃ count2 : Usize,
      index - 16#usize = ok count2 ∧ count2.val = index.val - 16 ∧
      verifier.query_duplicate_chunk0 queries (queries.val[index.val]!) 8#usize = ok false ∧
      verifier.query_duplicate_chunk1 queries (queries.val[index.val]!) 8#usize = ok false ∧
      verifier.query_duplicate_chunk2 queries (queries.val[index.val]!) count2 = ok false := by
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
  have hnot16 : ¬ index < 16#usize := by
    have hn : ¬ index.val < 16 := by omega
    simpa [UScalar.lt_equiv] using hn
  have hnotle16 : ¬ index ≤ 16#usize := by
    have hn : ¬ index.val ≤ 16 := by omega
    simpa [UScalar.le_equiv] using hn
  have h8val : (16#usize).val = 16 := by decide
  have hsubSpec : UScalar.sub index 16#usize
      ⦃ z => z.val = index.val - 16 ∧ 16 ≤ index.val ⦄ := by
    apply UScalar.sub_spec
    rw [h8val]
    omega
  obtain ⟨count2,hsub,hpost⟩ := WP.spec_imp_exists hsubSpec
  have hsubExpr : index - 16#usize = ok count2 := hsub
  have hcount2 : count2.val = index.val - 16 := hpost.1
  have hsuccess' := hsuccess
  simp only [verifier.validate_query_index, hidx, hshift, bind_tc_ok,
    if_neg hge, if_neg hnot8, if_neg hnotle8, if_neg hnot16, if_neg hnotle16]
    at hsuccess'
  simp only [hsubExpr, bind_tc_ok] at hsuccess'
  have hbranch : (do
      let b0 ← verifier.query_duplicate_chunk0 queries (queries.val[index.val]!) 8#usize
      if b0 then ok (core.result.Result.Err verifier.Error.Checkpoint) else do
        let b1 ← verifier.query_duplicate_chunk1 queries (queries.val[index.val]!) 8#usize
        if b1 then ok (core.result.Result.Err verifier.Error.Checkpoint) else do
          let b2 ← verifier.query_duplicate_chunk2 queries (queries.val[index.val]!) count2
          if b2 then ok (core.result.Result.Err verifier.Error.Checkpoint)
            else ok (core.result.Result.Ok ())) = ok (core.result.Result.Ok ()) := by
    simpa only [bind_tc_ok] using hsuccess'
  have hfalse := AspisR1.QueryValidatorGateInversion.three_false_of_gates
    verifier.Error.Checkpoint
    (verifier.query_duplicate_chunk0 queries (queries.val[index.val]!) 8#usize)
    (verifier.query_duplicate_chunk1 queries (queries.val[index.val]!) 8#usize)
    (verifier.query_duplicate_chunk2 queries (queries.val[index.val]!) count2)
    (by simpa only [hsubExpr, bind_tc_ok] using hbranch)
  exact ⟨count2, hsubExpr, hcount2, hfalse.1, hfalse.2.1, hfalse.2.2⟩

#print axioms branch2_calls_false
end AspisR1.QueryValidateIndexBranch2
