import AspisR1TerminalDecoder.Funs
import R1Z.PV_RunJoin_ResultDomain28
import R1Z.PV_Src_CompilerTactic
import R1Z.BuilderRecordsArray
set_option autoImplicit false
namespace R1Z.PV_RunJoin_DecoderDigest29
open Aeneas Aeneas.Std Result ControlFlow
open R0Z.WriterRefine

theorem body_in_range (d : Array U32 8#usize) (i : Usize) (hi : i.val < 8) :
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.digest_is_canonical_loop.body d i =
      if d.val[i.val]!.val < 2147483647 then
        (do let j ← i + 1#usize; ok (cont j))
      else ok (done false) := by
  unfold AspisR1TerminalDecoder.pool_v1.pair_tree_profile.digest_is_canonical_loop.body
  rw [index_ok_gen d i (by simpa using hi)]
  simp only [Array.to_slice, Slice.len, lift, bind_tc_ok]
  rw [if_pos (by simpa [UScalar.lt_equiv] using hi)]
  simp only [AspisR1TerminalDecoder.aspis_core.field.P, UScalar.ge_equiv]
  split_ifs <;> simp_all only [not_le]
#print axioms body_in_range

theorem body_done (d : Array U32 8#usize) (i : Usize) (hi : 8 ≤ i.val) :
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.digest_is_canonical_loop.body d i = ok (done true) := by
  unfold AspisR1TerminalDecoder.pool_v1.pair_tree_profile.digest_is_canonical_loop.body
  simp only [Array.to_slice, Slice.len, lift, bind_tc_ok]
  rw [if_neg (by simpa [UScalar.lt_equiv] using (show ¬ i.val < 8 by omega))]
#print axioms body_done
end R1Z.PV_RunJoin_DecoderDigest29
