import QueryWordsArrayMapAll
import QueryScanMaskCallExact
import AspisR1QueryScan.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
namespace AspisR1QueryScanUnrolled

 theorem query_words_success_range
    (block : Array Std.U8 32#usize) (words : Array Std.U32 8#usize)
    (hqw : r0_transcript.query_words block = .ok words) :
    ∀ w ∈ words.val, w.val < 262144 := by
  unfold r0_transcript.query_words at hqw
  cases hrank : r0_transcript.block_rank block with
  | fail e => simp [hrank] at hqw
  | div => simp [hrank] at hqw
  | ok ranks =>
      cases hmap : core.array.Array.map
          r0_transcript.query_words.closure.Insts.CoreOpsFunctionFnMutTupleU32U32 ranks () with
      | fail e => simp [hrank, hmap] at hqw
      | div => simp [hrank, hmap] at hqw
      | ok out =>
          have hout : out = words := by
            simp [hrank, hmap] at hqw
            exact hqw
          subst words
          apply array_map_success_all
            r0_transcript.query_words.closure.Insts.CoreOpsFunctionFnMutTupleU32U32
            (fun y => y.val < 262144) ?_ ranks () out ?_
          · intro f x y f' hy
            have hexact := r0_transcript.query_mask_call_mut_exact f x
            have pairEq : (y, f') = (x &&& 262143#u32, f) := Result.ok.inj (hy.symm.trans hexact)
            have hyEq : y = x &&& 262143#u32 := congrArg Prod.fst pairEq
            subst y
            rw [UScalar.val_and]
            exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)
          · exact hmap

#print axioms query_words_success_range
end AspisR1QueryScanUnrolled
