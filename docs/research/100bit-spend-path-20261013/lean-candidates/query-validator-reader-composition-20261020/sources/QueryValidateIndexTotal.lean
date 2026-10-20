import Aeneas
import QueryValidatorGeneratedPrefix
import QueryValidatorChunkArrayBridge
import QueryValidatorChunkArrayBridgeMore
import QueryValidatorLoopInvariant
import Aeneas.Tactic.Solver.ScalarTac
open Aeneas Aeneas.Std Result AspisR1Stage2AdoptedResume
namespace AspisR1.QueryValidateIndexTotal
abbrev QueryArray := Array Std.U32 22#usize

def gateResult (b0 b1 b2 : Bool) : core.result.Result Unit verifier.Error :=
  if b0 then core.result.Result.Err verifier.Error.Checkpoint else
  if b1 then core.result.Result.Err verifier.Error.Checkpoint else
  if b2 then core.result.Result.Err verifier.Error.Checkpoint else core.result.Result.Ok ()

theorem three_gate_total (b0 b1 b2 : Bool) :
    (do
      let x0 ← ok b0
      if x0 then ok (core.result.Result.Err verifier.Error.Checkpoint) else do
        let x1 ← ok b1
        if x1 then ok (core.result.Result.Err verifier.Error.Checkpoint) else do
          let x2 ← ok b2
          if x2 then ok (core.result.Result.Err verifier.Error.Checkpoint)
            else ok (core.result.Result.Ok ())) = ok (gateResult b0 b1 b2) := by
  cases b0 <;> cases b1 <;> cases b2 <;> simp [gateResult, bind_tc_ok]

theorem validate_query_index_total
    (queries : QueryArray) (index : Usize) (hbound : index.val < 22) :
    ∃ r : core.result.Result Unit verifier.Error,
      verifier.validate_query_index queries index = ok r := by
  have hidx : Array.index_usize queries index = ok queries.val[index.val]! :=
    AspisR1.QueryValidatorChunkArrayBridge.index_ok_gen queries index (by scalar_tac)
  have hshift : (1#u32 <<< 18#i32) = ok (262144#u32) := by rfl
  by_cases hge : queries.val[index.val]! ≥ 262144#u32
  · exact ⟨core.result.Result.Err verifier.Error.Checkpoint, by
      simp only [verifier.validate_query_index, hidx, hshift, bind_tc_ok, if_pos hge]⟩
  · have h8v : (8#usize).val = 8 := by decide
    have h16v : (16#usize).val = 16 := by decide
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
    by_cases hlt8 : index < 8#usize
    · have hle8 : index ≤ 8#usize := by
        have hn : index.val ≤ 8 := by have := (UScalar.lt_equiv _ _).1 hlt8; omega
        exact (UScalar.le_equiv _ _).2 (by simpa using hn)
      have hle16 : index ≤ 16#usize := by
        have hn : index.val ≤ 16 := by have := (UScalar.lt_equiv _ _).1 hlt8; omega
        exact (UScalar.le_equiv _ _).2 (by simpa using hn)
      let b0 := AspisR1.QueryValidatorGeneratedChunk.formula0 index
        queries.val[0#usize.val]! queries.val[1#usize.val]! queries.val[2#usize.val]!
        queries.val[3#usize.val]! queries.val[4#usize.val]! queries.val[5#usize.val]!
        queries.val[6#usize.val]! queries.val[7#usize.val]! (queries.val[index.val]!)
      let b1 := AspisR1.QueryValidatorGeneratedChunk.formula0 0#usize
        queries.val[8#usize.val]! queries.val[9#usize.val]! queries.val[10#usize.val]!
        queries.val[11#usize.val]! queries.val[12#usize.val]! queries.val[13#usize.val]!
        queries.val[14#usize.val]! queries.val[15#usize.val]! (queries.val[index.val]!)
      let b2 := AspisR1.QueryValidatorChunkArrayBridgeMore.formula6 0#usize
        queries.val[16#usize.val]! queries.val[17#usize.val]! queries.val[18#usize.val]!
        queries.val[19#usize.val]! queries.val[20#usize.val]! queries.val[21#usize.val]!
        (queries.val[index.val]!)
      refine ⟨gateResult b0 b1 b2, ?_⟩
      simpa only [verifier.validate_query_index, hidx, hshift, bind_tc_ok, if_neg hge,
        if_pos hlt8, if_pos hle8, if_pos hle16, h0i, h10, h20, b0, b1, b2,
        gateResult] using three_gate_total b0 b1 b2
    · have hnotlt8 : ¬ index < 8#usize := hlt8
      by_cases hle8 : index ≤ 8#usize
      · have hle16 : index ≤ 16#usize := by
          have hn8 : index.val ≤ 8 := by have := (UScalar.le_equiv _ _).1 hle8; simpa using this
          have hn16 : index.val ≤ 16 := by omega
          exact (UScalar.le_equiv _ _).2 (by simpa [h16v] using hn16)
        let b0 := AspisR1.QueryValidatorGeneratedChunk.formula0 8#usize
          queries.val[0#usize.val]! queries.val[1#usize.val]! queries.val[2#usize.val]!
          queries.val[3#usize.val]! queries.val[4#usize.val]! queries.val[5#usize.val]!
          queries.val[6#usize.val]! queries.val[7#usize.val]! (queries.val[index.val]!)
        let b1 := AspisR1.QueryValidatorGeneratedChunk.formula0 0#usize
          queries.val[8#usize.val]! queries.val[9#usize.val]! queries.val[10#usize.val]!
          queries.val[11#usize.val]! queries.val[12#usize.val]! queries.val[13#usize.val]!
          queries.val[14#usize.val]! queries.val[15#usize.val]! (queries.val[index.val]!)
        let b2 := AspisR1.QueryValidatorChunkArrayBridgeMore.formula6 0#usize
          queries.val[16#usize.val]! queries.val[17#usize.val]! queries.val[18#usize.val]!
          queries.val[19#usize.val]! queries.val[20#usize.val]! queries.val[21#usize.val]!
          (queries.val[index.val]!)
        refine ⟨gateResult b0 b1 b2, ?_⟩
        simpa only [verifier.validate_query_index, hidx, hshift, bind_tc_ok, if_neg hge,
          if_neg hnotlt8, if_pos hle8, if_pos hle16, h08, h10, h20, b0, b1, b2,
          gateResult] using three_gate_total b0 b1 b2
      · have hnotle8 : ¬ index ≤ 8#usize := hle8
        by_cases hlt16 : index < 16#usize
        · have hsubSpec : UScalar.sub index 8#usize
              ⦃ z => z.val = index.val - 8 ∧ 8 ≤ index.val ⦄ := by
              apply UScalar.sub_spec
              rw [h8v]
              have hnot8Nat : ¬ index.val ≤ 8 := by
                simpa [UScalar.le_equiv, h8v] using hnotle8
              have hlt16Nat : index.val < 16 := (UScalar.lt_equiv _ _).1 hlt16
              omega
          obtain ⟨count1,hsub,hpost⟩ := WP.spec_imp_exists hsubSpec
          have hsubExpr : index - 8#usize = ok count1 := hsub
          have h1i := AspisR1.QueryValidatorChunkArrayBridgeMore.generated_chunk1_array_formula queries
            (queries.val[index.val]!) count1
          have hle16 : index ≤ 16#usize := by
            have hlt16Nat : index.val < 16 := (UScalar.lt_equiv _ _).1 hlt16
            exact (UScalar.le_equiv _ _).2 (by simpa [h16v] using (show index.val ≤ 16 by omega))
          let b0 := AspisR1.QueryValidatorGeneratedChunk.formula0 8#usize
            queries.val[0#usize.val]! queries.val[1#usize.val]! queries.val[2#usize.val]!
            queries.val[3#usize.val]! queries.val[4#usize.val]! queries.val[5#usize.val]!
            queries.val[6#usize.val]! queries.val[7#usize.val]! (queries.val[index.val]!)
          let b1 := AspisR1.QueryValidatorGeneratedChunk.formula0 count1
            queries.val[8#usize.val]! queries.val[9#usize.val]! queries.val[10#usize.val]!
            queries.val[11#usize.val]! queries.val[12#usize.val]! queries.val[13#usize.val]!
            queries.val[14#usize.val]! queries.val[15#usize.val]! (queries.val[index.val]!)
          let b2 := AspisR1.QueryValidatorChunkArrayBridgeMore.formula6 0#usize
            queries.val[16#usize.val]! queries.val[17#usize.val]! queries.val[18#usize.val]!
            queries.val[19#usize.val]! queries.val[20#usize.val]! queries.val[21#usize.val]!
            (queries.val[index.val]!)
          refine ⟨gateResult b0 b1 b2, ?_⟩
          simpa only [verifier.validate_query_index, hidx, hshift, bind_tc_ok, if_neg hge,
            if_neg hnotlt8, if_neg hnotle8, if_pos hlt16, if_pos hle16,
            hsubExpr, h08, h1i, h20,
            b0, b1, b2, gateResult] using three_gate_total b0 b1 b2
        · have hnotlt16 : ¬ index < 16#usize := hlt16
          by_cases hle16 : index ≤ 16#usize
          · let b0 := AspisR1.QueryValidatorGeneratedChunk.formula0 8#usize
              queries.val[0#usize.val]! queries.val[1#usize.val]! queries.val[2#usize.val]!
              queries.val[3#usize.val]! queries.val[4#usize.val]! queries.val[5#usize.val]!
              queries.val[6#usize.val]! queries.val[7#usize.val]! (queries.val[index.val]!)
            let b1 := AspisR1.QueryValidatorGeneratedChunk.formula0 8#usize
              queries.val[8#usize.val]! queries.val[9#usize.val]! queries.val[10#usize.val]!
              queries.val[11#usize.val]! queries.val[12#usize.val]! queries.val[13#usize.val]!
              queries.val[14#usize.val]! queries.val[15#usize.val]! (queries.val[index.val]!)
            let b2 := AspisR1.QueryValidatorChunkArrayBridgeMore.formula6 0#usize
              queries.val[16#usize.val]! queries.val[17#usize.val]! queries.val[18#usize.val]!
              queries.val[19#usize.val]! queries.val[20#usize.val]! queries.val[21#usize.val]!
              (queries.val[index.val]!)
            refine ⟨gateResult b0 b1 b2, ?_⟩
            simpa only [verifier.validate_query_index, hidx, hshift, bind_tc_ok, if_neg hge,
              if_neg hnotlt8, if_neg hnotle8, if_neg hnotlt16, if_pos hle16,
              h08, h18, h20, b0, b1, b2, gateResult] using three_gate_total b0 b1 b2
          · have hnotle16 : ¬ index ≤ 16#usize := hle16
            have hsubSpec : UScalar.sub index 16#usize
                ⦃ z => z.val = index.val - 16 ∧ 16 ≤ index.val ⦄ := by
                apply UScalar.sub_spec
                rw [h16v]
                have hnot16Nat : ¬ index.val ≤ 16 := by
                  simpa [UScalar.le_equiv, h16v] using hnotle16
                omega
            obtain ⟨count2,hsub,hpost⟩ := WP.spec_imp_exists hsubSpec
            have hsubExpr : index - 16#usize = ok count2 := hsub
            have h2i := AspisR1.QueryValidatorChunkArrayBridgeMore.generated_chunk2_array_formula queries
              (queries.val[index.val]!) count2
            let b0 := AspisR1.QueryValidatorGeneratedChunk.formula0 8#usize
              queries.val[0#usize.val]! queries.val[1#usize.val]! queries.val[2#usize.val]!
              queries.val[3#usize.val]! queries.val[4#usize.val]! queries.val[5#usize.val]!
              queries.val[6#usize.val]! queries.val[7#usize.val]! (queries.val[index.val]!)
            let b1 := AspisR1.QueryValidatorGeneratedChunk.formula0 8#usize
              queries.val[8#usize.val]! queries.val[9#usize.val]! queries.val[10#usize.val]!
              queries.val[11#usize.val]! queries.val[12#usize.val]! queries.val[13#usize.val]!
              queries.val[14#usize.val]! queries.val[15#usize.val]! (queries.val[index.val]!)
            let b2 := AspisR1.QueryValidatorChunkArrayBridgeMore.formula6 count2
              queries.val[16#usize.val]! queries.val[17#usize.val]! queries.val[18#usize.val]!
              queries.val[19#usize.val]! queries.val[20#usize.val]! queries.val[21#usize.val]!
              (queries.val[index.val]!)
            refine ⟨gateResult b0 b1 b2, ?_⟩
            simpa only [verifier.validate_query_index, hidx, hshift, bind_tc_ok, if_neg hge,
              if_neg hnotlt8, if_neg hnotle8, if_neg hnotlt16, if_neg hnotle16,
              hsubExpr, h08, h18, h2i, b0, b1, b2, gateResult] using three_gate_total b0 b1 b2
#print axioms validate_query_index_total
end AspisR1.QueryValidateIndexTotal
