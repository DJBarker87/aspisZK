import Query31ConcreteWordsDriverChain
set_option autoImplicit false
namespace AspisR1.JGg_QueryTotal
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

theorem loop_total {T F : Type} (N : Usize)
    (callback : core.ops.function.FnMut F Usize T) (f : F) (g : Nat → T)
    (stable : ∀ i : Usize,i.val<N.val → callback.call_mut f i=ok (g i.val,f))
    (fuel : Nat) (i : Usize) (acc : List T)
    (small : N.val≤8) (bound : N.val-i.val≤fuel) :
    ∃ out,arrayFromFnLoop N callback fuel i f acc=ok (out,f) := by
  induction fuel generalizing i acc with
  | zero =>
    have stop : ¬ i<N := by simp only [UScalar.lt_equiv];omega
    exact ⟨acc.reverse,by simp only [arrayFromFnLoop,dif_neg stop]⟩
  | succ fuel ih =>
    by_cases active : i<N
    · have hi : i.val<N.val := (UScalar.lt_equiv _ _).mp active
      have add : (i+1#usize : Result Usize) ⦃ j => j.val=i.val+1 ⦄ := by
        apply UScalar.add_spec
        scalar_tac
      obtain ⟨j,added,hj⟩ := WP.spec_imp_exists add
      obtain ⟨out,tail⟩ := ih j (g i.val::acc) (by omega)
      exact ⟨out,by simp only [arrayFromFnLoop,dif_pos active,stable i hi,bind_tc_ok,added,tail]⟩
    · exact ⟨acc.reverse,by simp only [arrayFromFnLoop,dif_neg active]⟩
#print axioms loop_total

theorem words_total (block : Array U8 32#usize) :
    ∃ out,Query31ConcreteWordsDriverChain.actualQueryWords block=ok out := by
  let callback := AspisR1QueryScanUnrolled.r0_transcript.block_rank.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
  have stable : ∀ i : Usize,i.val<(8#usize).val → callback.call_mut block i=
      ok (AspisR1QueryScanUnrolled.r0_transcript.blockRankWord block i.val,block) := by
    intro i hi
    change i.val<8 at hi
    simpa only [callback,AspisR1QueryScanUnrolled.r0_transcript.blockRankWord,dif_pos hi] using
      AspisR1QueryScanUnrolled.r0_transcript.block_rank_callback_call_mut_success block i hi
  obtain ⟨values,loop⟩ := loop_total 8#usize callback block
    (AspisR1QueryScanUnrolled.r0_transcript.blockRankWord block) stable 9 0#usize [] (by decide) (by decide)
  have rank : ∃ ranks,AspisR1QueryScanUnrolled.r0_transcript.block_rank block=ok ranks := by
    unfold AspisR1QueryScanUnrolled.r0_transcript.block_rank AspisR1QueryScanUnrolled.core.array.from_fn
      AspisR1SelectedMaskProbe.core.array.from_fn
    change ∃ ranks,(match h : arrayFromFnLoop 8#usize callback 9 0#usize block [] with
      | .ok (xs,_) => .ok (⟨xs,arrayFromFnLoop_length_of_success 8#usize callback 9 0#usize block [] xs _ (by decide) (by rfl) (by decide) h⟩ : Array U32 8#usize)
      | .fail e => .fail e
      | .div => .div)=ok ranks
    rw [loop]
    exact ⟨_,rfl⟩
  obtain ⟨ranks,rank⟩ := rank
  have mapped : ∀ xs : List U32,AspisV8R19.TraversalRuntime.mapState
      AspisR1QueryScanUnrolled.r0_transcript.query_words.closure.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
      xs ()=ok (xs.map AspisR1QueryScanUnrolled.r0_transcript.queryMaskWord,()) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [AspisV8R19.TraversalRuntime.mapState,
        AspisR1QueryScanUnrolled.r0_transcript.query_mask_call_mut_exact,bind_tc_ok,ih,List.map_cons]
  unfold Query31ConcreteWordsDriverChain.actualQueryWords AspisR1QueryScanUnrolled.r0_transcript.query_words
  rw [rank,bind_tc_ok]
  unfold AspisR1QueryScanUnrolled.core.array.Array.map AspisR1SelectedMaskProbe.core.array.Array.map
  rw [Aeneas.Std.core.array.Array.map_success _ _ _ _ _ (mapped ranks.val)]
  exact ⟨_,rfl⟩
#print axioms words_total
end AspisR1.JGg_QueryTotal
