import Aeneas
import QueryValidatorGeneratedPrefix
import QueryValidatorChunkArrayBridge
import QueryValidatorChunkArrayBridgeMore
import QueryValidatorLoopInvariant
import Aeneas.Tactic.Solver.ScalarTac
open Aeneas Aeneas.Std Result AspisR1Stage2AdoptedResume
namespace AspisR1.QueryValidateIndexTotal
abbrev QueryArray := Array Std.U32 22#usize

theorem three_gate_total (b0 b1 b2 : Bool) :
    ∃ r : core.result.Result Unit verifier.Error,
      (do
        let x0 ← ok b0
        if x0 then ok (core.result.Result.Err verifier.Error.Checkpoint) else do
          let x1 ← ok b1
          if x1 then ok (core.result.Result.Err verifier.Error.Checkpoint) else do
            let x2 ← ok b2
            if x2 then ok (core.result.Result.Err verifier.Error.Checkpoint)
              else ok (core.result.Result.Ok ())) = ok r := by
  cases b0 <;> cases b1 <;> cases b2 <;> simp [bind_tc_ok]

theorem validate_query_index_total
    (queries : QueryArray) (index : Usize) (hbound : index.val < 22) :
    ∃ r : core.result.Result Unit verifier.Error,
      verifier.validate_query_index queries index = ok r := by
  have hidx : Array.index_usize queries index = ok queries.val[index.val]! :=
    AspisR1.QueryValidatorChunkArrayBridge.index_ok_gen queries index (by scalar_tac)
  have hshift : (1#u32 <<< 18#i32) = ok (262144#u32) := by rfl
  have h0i := AspisR1.QueryValidatorChunkArrayBridge.generated_chunk0_array_formula queries
    (queries.val[index.val]!) index
  have h08 := AspisR1.QueryValidatorChunkArrayBridge.generated_chunk0_array_formula queries
    (queries.val[index.val]!) 8#usize
  have h10 := AspisR1.QueryValidatorChunkArrayBridgeMore.generated_chunk1_array_formula queries
    (queries.val[index.val]!) 0#usize
  have h18 := AspisR1.QueryValidatorChunkArrayBridgeMore.generated_chunk1_array_formula queries
    (queries.val[index.val]!) 8#usize
  have h20 := AspisR1.QueryValidatorChunkArrayBridgeMore.generated_chunk2_array_formula queries
    (queries.val[index.val]!) 0#usize
  have h2i := AspisR1.QueryValidatorChunkArrayBridgeMore.generated_chunk2_array_formula queries
    (queries.val[index.val]!) (index - 16#usize)
  by_cases hge : queries.val[index.val]! ≥ 262144#u32
  · refine ⟨core.result.Result.Err verifier.Error.Checkpoint, ?_⟩
    simp only [verifier.validate_query_index, hidx, hshift, bind_tc_ok, if_pos hge]
  · by_cases hlt8 : index < 8#usize
    · refine ⟨if AspisR1.QueryValidatorGeneratedChunk.formula0 index
          queries.val[0#usize.val]! queries.val[1#usize.val]! queries.val[2#usize.val]!
          queries.val[3#usize.val]! queries.val[4#usize.val]! queries.val[5#usize.val]!
          queries.val[6#usize.val]! queries.val[7#usize.val]! (queries.val[index.val]!)
          then core.result.Result.Err verifier.Error.Checkpoint else core.result.Result.Ok (), ?_⟩
      simpa only [verifier.validate_query_index, hidx, hshift, bind_tc_ok, if_neg hge,
        if_pos hlt8, h0i, h10, h20] using three_gate_total _ _ _
    · have h8val : (8#usize).val = 8 := by decide
      have h16val : (16#usize).val = 16 := by decide
      have hnotlt8 : ¬ index < 8#usize := hlt8
      by_cases hle8 : index ≤ 8#usize
      · refine ⟨if AspisR1.QueryValidatorGeneratedChunk.formula0 8#usize
          queries.val[0#usize.val]! queries.val[1#usize.val]! queries.val[2#usize.val]!
          queries.val[3#usize.val]! queries.val[4#usize.val]! queries.val[5#usize.val]!
          queries.val[6#usize.val]! queries.val[7#usize.val]! (queries.val[index.val]!)
          then core.result.Result.Err verifier.Error.Checkpoint else core.result.Result.Ok (), ?_⟩
        simpa only [verifier.validate_query_index, hidx, hshift, bind_tc_ok, if_neg hge,
          if_neg hnotlt8, if_pos hle8, h08, h10, h20] using three_gate_total _ _ _
      · have hnotle8 : ¬ index ≤ 8#usize := hle8
        by_cases hlt16 : index < 16#usize
        · have hsubSpec : UScalar.sub index 8#usize
              ⦃ z => z.val = index.val - 8 ∧ 8 ≤ index.val ⦄ := by
              apply UScalar.sub_spec
              have h8v : (8#usize).val = 8 := h8val
              rw [h8v]
              have hnot8nat : 8 ≤ index.val := by
                have hn := (UScalar.le_equiv _ _).1 (le_of_not_gt hnotle8)
                rw [h8v] at hn
                omega
              exact ⟨by omega, hnot8nat⟩
          obtain ⟨count1,hsub,hpost⟩ := WP.spec_imp_exists hsubSpec
          have hsubExpr : index - 8#usize = ok count1 := hsub
          have hlt16' := hlt16
          refine ⟨if AspisR1.QueryValidatorGeneratedChunk.formula0 8#usize
            queries.val[0#usize.val]! queries.val[1#usize.val]! queries.val[2#usize.val]!
            queries.val[3#usize.val]! queries.val[4#usize.val]! queries.val[5#usize.val]!
            queries.val[6#usize.val]! queries.val[7#usize.val]! (queries.val[index.val]!)
            then core.result.Result.Err verifier.Error.Checkpoint else
            if AspisR1.QueryValidatorGeneratedChunk.formula0 count1
              queries.val[8#usize.val]! queries.val[9#usize.val]! queries.val[10#usize.val]!
              queries.val[11#usize.val]! queries.val[12#usize.val]! queries.val[13#usize.val]!
              queries.val[14#usize.val]! queries.val[15#usize.val]! (queries.val[index.val]!)
            then core.result.Result.Err verifier.Error.Checkpoint else
            if AspisR1.QueryValidatorGeneratedChunk.formula6 0#usize
              queries.val[16#usize.val]! queries.val[17#usize.val]! queries.val[18#usize.val]!
              queries.val[19#usize.val]! queries.val[20#usize.val]! queries.val[21#usize.val]!
              (queries.val[index.val]!)
            then core.result.Result.Err verifier.Error.Checkpoint else core.result.Result.Ok (), ?_⟩
          simpa only [verifier.validate_query_index, hidx, hshift, bind_tc_ok, if_neg hge,
            if_neg hnotlt8, if_neg hnotle8, if_pos hlt16', hsubExpr, h08, h18, h20]
            using three_gate_total _ _ _
        · have hnotlt16 : ¬ index < 16#usize := hlt16
          by_cases hle16 : index ≤ 16#usize
          · refine ⟨if AspisR1.QueryValidatorGeneratedChunk.formula0 8#usize
              queries.val[0#usize.val]! queries.val[1#usize.val]! queries.val[2#usize.val]!
              queries.val[3#usize.val]! queries.val[4#usize.val]! queries.val[5#usize.val]!
              queries.val[6#usize.val]! queries.val[7#usize.val]! (queries.val[index.val]!)
              then core.result.Result.Err verifier.Error.Checkpoint else
              if AspisR1.QueryValidatorGeneratedChunk.formula0 8#usize
                queries.val[8#usize.val]! queries.val[9#usize.val]! queries.val[10#usize.val]!
                queries.val[11#usize.val]! queries.val[12#usize.val]! queries.val[13#usize.val]!
                queries.val[14#usize.val]! queries.val[15#usize.val]! (queries.val[index.val]!)
              then core.result.Result.Err verifier.Error.Checkpoint else
              if AspisR1.QueryValidatorGeneratedChunk.formula6 0#usize
                queries.val[16#usize.val]! queries.val[17#usize.val]! queries.val[18#usize.val]!
                queries.val[19#usize.val]! queries.val[20#usize.val]! queries.val[21#usize.val]!
                (queries.val[index.val]!)
              then core.result.Result.Err verifier.Error.Checkpoint else core.result.Result.Ok (), ?_⟩
            simpa only [verifier.validate_query_index, hidx, hshift, bind_tc_ok, if_neg hge,
              if_neg hnotlt8, if_neg hnotle8, if_neg hnotlt16, if_pos hle16,
              h08, h18, h20] using three_gate_total _ _ _
          · have hnotle16 : ¬ index ≤ 16#usize := hle16
            have hsubSpec : UScalar.sub index 16#usize
                ⦃ z => z.val = index.val - 16 ∧ 16 ≤ index.val ⦄ := by
                apply UScalar.sub_spec
                rw [h16val]
                have hn : 16 ≤ index.val := by
                  have hleNat : ¬ index.val ≤ 16 := by
                    intro hx
                    have ht : index ≤ 16#usize := (UScalar.le_equiv _ _).2 (by simpa [h16val] using hx)
                    exact hnotle16 ht
                  omega
                exact ⟨by omega, hn⟩
            obtain ⟨count2,hsub,hpost⟩ := WP.spec_imp_exists hsubSpec
            have hsubExpr : index - 16#usize = ok count2 := hsub
            refine ⟨if AspisR1.QueryValidatorGeneratedChunk.formula0 8#usize
              queries.val[0#usize.val]! queries.val[1#usize.val]! queries.val[2#usize.val]!
              queries.val[3#usize.val]! queries.val[4#usize.val]! queries.val[5#usize.val]!
              queries.val[6#usize.val]! queries.val[7#usize.val]! (queries.val[index.val]!)
              then core.result.Result.Err verifier.Error.Checkpoint else
              if AspisR1.QueryValidatorGeneratedChunk.formula0 8#usize
                queries.val[8#usize.val]! queries.val[9#usize.val]! queries.val[10#usize.val]!
                queries.val[11#usize.val]! queries.val[12#usize.val]! queries.val[13#usize.val]!
                queries.val[14#usize.val]! queries.val[15#usize.val]! (queries.val[index.val]!)
              then core.result.Result.Err verifier.Error.Checkpoint else
              if AspisR1.QueryValidatorGeneratedChunk.formula6 count2
                queries.val[16#usize.val]! queries.val[17#usize.val]! queries.val[18#usize.val]!
                queries.val[19#usize.val]! queries.val[20#usize.val]! queries.val[21#usize.val]!
                (queries.val[index.val]!)
              then core.result.Result.Err verifier.Error.Checkpoint else core.result.Result.Ok (), ?_⟩
            simpa only [verifier.validate_query_index, hidx, hshift, bind_tc_ok, if_neg hge,
              if_neg hnotlt8, if_neg hnotle8, if_neg hnotlt16, if_neg hnotle16,
              hsubExpr, h08, h18, h2i] using three_gate_total _ _ _

#print axioms validate_query_index_total
end AspisR1.QueryValidateIndexTotal
