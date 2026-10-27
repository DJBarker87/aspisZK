import XRv_FromFnTotal
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRv_DecoderTotal
open AspisR1QueryScanUnrolled.r0_transcript

theorem ranks (block : Array U8 32#usize) :
 ∃ out, AspisR1QueryScanUnrolled.r0_transcript.block_rank block = ok out := by
 apply XRv_FromFnTotal.total 8#usize _ (blockRankWord block) block
 intro j hj
 have hj8 : j.val < 8 := hj
 have h := block_rank_callback_call_mut_success block j hj8
 simpa only [blockRankWord, dif_pos hj8] using h

theorem map_stable {T U F : Type} (call : F → T → Result (U × F))
 (f : F) (g : T → U) (xs : List T)
 (stable : ∀ x, call f x = ok (g x,f)) :
 AspisV8R19.TraversalRuntime.mapState call xs f = ok (xs.map g,f) := by
 induction xs with
 | nil => rfl
 | cons x xs ih =>
   simp only [AspisV8R19.TraversalRuntime.mapState,stable,bind_tc_ok]
   exact congrArg (fun r => r >>= fun (ys,f') => ok (g x :: ys,f')) ih

theorem decoder (block : Array U8 32#usize) :
 ∃ out, AspisR1QueryScanUnrolled.r0_transcript.query_words block = ok out := by
 obtain ⟨r,hr⟩ := ranks block
 have hm := map_stable
   AspisR1QueryScanUnrolled.r0_transcript.query_words.closure.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut
   () queryMaskWord r.val (query_mask_call_mut_exact ())
 have hs := Aeneas.Std.core.array.Array.map_success
   AspisR1QueryScanUnrolled.r0_transcript.query_words.closure.Insts.CoreOpsFunctionFnMutTupleU32U32
   r () (r.val.map queryMaskWord) () hm
 unfold AspisR1QueryScanUnrolled.r0_transcript.query_words
 rw [hr,bind_tc_ok]
 exact ⟨_,hs⟩

#print axioms ranks
#print axioms map_stable
#print axioms decoder
end XRv_DecoderTotal
