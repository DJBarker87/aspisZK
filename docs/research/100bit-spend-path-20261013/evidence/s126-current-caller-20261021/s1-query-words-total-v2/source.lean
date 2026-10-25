import S1FinishFromFnStableV1
import S1QueryWordModelV1
set_option autoImplicit false
namespace AspisS1QueryWordsTotal
open Aeneas Aeneas.Std Result
open AspisR1QueryScanUnrolled.r0_transcript

/-- Every actual source-shaped from_fn byte callback is defined. -/
theorem rank_total (block : Array U8 32#usize) :
    ∃ out : Array U32 8#usize, block_rank block=ok out ∧
      out.val=(List.range 8).map (blockRankWord block) := by
  obtain ⟨out,called,values⟩ := AspisR1SelectedMaskProbe.finish_from_fn_total_of_stable
    8#usize block_rank.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
    (blockRankWord block) block (by
      intro i hi
      have bound : i.val<8 := by simpa using hi
      have h := block_rank_callback_call_mut_success block i bound
      simpa only [blockRankWord,dif_pos bound] using h)
  exact ⟨out,called,values⟩

private theorem mask_list (xs : List U32) :
    AspisV8R19.TraversalRuntime.mapState
      query_words.closure.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut xs ()=
      ok (xs.map queryMaskWord,()) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [AspisV8R19.TraversalRuntime.mapState,query_mask_call_mut_exact,
      bind_tc_ok,List.map_cons,ih]
    rfl

/-- TOTAL original concrete word decoder, retaining exact U32 values and
ordered bytes. No successful from_fn/map call is assumed. -/
theorem words_total (block : Array U8 32#usize) :
    ∃ out : Array U32 8#usize, query_words block=ok out ∧
      out.val=List.ofFn (fun j : Fin 8 => queryMaskWord (blockRankWord block j.val)) := by
  obtain ⟨ranks,called,values⟩ := rank_total block
  have mapped := core.array.Array.map_success
    query_words.closure.Insts.CoreOpsFunctionFnMutTupleU32U32 ranks ()
    (ranks.val.map queryMaskWord) () (mask_list ranks.val)
  refine ⟨⟨ranks.val.map queryMaskWord,by simp [ranks.property]⟩,?_,?_⟩
  · unfold query_words
    rw [called]
    exact mapped
  · rw [values,List.map_map]
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,Function.comp_apply]

#print axioms rank_total
#print axioms words_total
end AspisS1QueryWordsTotal
