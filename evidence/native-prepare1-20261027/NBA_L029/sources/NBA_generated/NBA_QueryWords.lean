import NBA_FromFnTotal
import Query31ConcreteWordsDriverChain
set_option autoImplicit false
namespace AspisR1.NBA_QueryWords
open Aeneas Aeneas.Std Result
open AspisR1QueryScanUnrolled

theorem map_stable {T U F : Type} (call : F → T → Result (U×F))
    (state : F) (value : T → U) (xs : List T)
    (stable : ∀ x,call state x=ok (value x,state)) :
    AspisV8R19.TraversalRuntime.mapState call xs state=ok (xs.map value,state) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [AspisV8R19.TraversalRuntime.mapState,stable x,bind_tc_ok]
    dsimp! only
    rw [ih]

/-- Every typed32-byte input constructs the exact ordered/masked eight-word
array. No successful decoder Result is assumed. -/
theorem source (block : Array U8 32#usize) :
    ∃ words, Query31ConcreteWordsDriverChain.actualQueryWords block=ok words ∧
      words.val=(List.range 8).map (fun j => r0_transcript.queryMaskWord (r0_transcript.blockRankWord block j)) := by
  obtain ⟨ranks,rank⟩ := NBA_FromFnTotal.source 8#usize
    r0_transcript.block_rank.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 block (by
      intro state i hi
      exact ⟨_,state,r0_transcript.block_rank_callback_call_mut_success state i (by simpa only [show (8#usize).val=8 by rfl] using hi)⟩)
  have blockCall : r0_transcript.block_rank block=ok ranks := rank
  have mapped := map_stable
    r0_transcript.query_words.closure.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
    () r0_transcript.queryMaskWord ranks.val (fun w => r0_transcript.query_mask_call_mut_exact () w)
  have mapCall := Aeneas.Std.core.array.Array.map_success
    r0_transcript.query_words.closure.Insts.CoreOpsFunctionFnMutTupleU32U32 ranks ()
    (ranks.val.map r0_transcript.queryMaskWord) () mapped
  have call : ∃ words, r0_transcript.query_words block=ok words := by
    refine ⟨_,?_⟩
    unfold r0_transcript.query_words
    rw [blockCall,bind_tc_ok]
    exact mapCall
  obtain ⟨words,call⟩ := call
  exact ⟨words,call,r0_transcript.query_words_success_byte_mask block words call⟩

#print axioms map_stable
#print axioms source
end AspisR1.NBA_QueryWords
