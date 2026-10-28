import NDH_FromFnTotal
import QueryScanConcreteWordsDecoder
set_option autoImplicit false
namespace NDH_BlockRank
open Aeneas Aeneas.Std Result
open AspisR1QueryScanUnrolled.r0_transcript

theorem total (block : Array U8 32#usize) :
    ∃ out : Array U32 8#usize,
      block_rank block=ok out ∧
      out.val=(List.range 8).map (blockRankWord block) := by
  let cb := block_rank.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
  have stable : ∀ i : Usize, i.val<(8#usize:Usize).val →
      cb.call_mut block i=ok (blockRankWord block i.val,block) := by
    intro i hi
    have small : i.val<8 := hi
    simpa only [cb,blockRankWord,dif_pos small] using
      block_rank_callback_call_mut_success block i small
  obtain ⟨out,run⟩ := NDH_FromFnTotal.from_fn_total 8#usize cb block
    (fun i => blockRankWord block i.val) stable
  have full : block_rank block=ok out := run
  exact ⟨out,full,block_rank_success_words_in_order block out full⟩

#print axioms total
end NDH_BlockRank
