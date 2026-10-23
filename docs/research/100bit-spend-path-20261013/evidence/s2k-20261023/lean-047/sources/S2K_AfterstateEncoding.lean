import S2K_AfterstateBytes

/-! Complete extracted ASJA payload, defined from symbolic bounded stores and
ordered digest-word folds; validation errors remain in AfterstateStatus. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.AfterstateEncoding
open AspisR1TerminalDecoder
open pool_v1.pair_terminal
abbrev Afterstate := PoolV1PairVerifiedAfterstateV1

def header (a : Afterstate) (out : Array U8 688#usize) : Array U8 688#usize :=
  let out := out.setSlice! 0 POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC.val
  let out := out.set 4#usize POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION
  let out := out.set 5#usize pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION
  let out := out.set 6#usize pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
  let out := out.set 7#usize 1#u8
  let out := out.setSlice! 8 (core.num.U64.to_le_bytes a.next_pair_index).val
  out.setSlice! 16 (DigestBytes.bytes a.next_root).val

def bytes (a : Afterstate) : Array U8 688#usize :=
  AfterstateBytes.fold a.next_frontier.val 0 (header a (Array.repeat 688#usize 0#u8))

theorem encode_exact (a : Afterstate)
    (validated : validate_verified_afterstate a = ok (.Ok ())) :
    encode_pool_v1_pair_verified_afterstate_v1 a = ok (.Ok (bytes a)) := by
  unfold bytes
  simp only [encode_pool_v1_pair_verified_afterstate_v1,validated,
    bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  generalize Array.repeat 688#usize 0#u8 = output
  simp only [DigestBytes.exact,bind_tc_ok,lift]
  simp [core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut, core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    Array.to_slice, Array.from_slice, core.slice.Slice.copy_from_slice,
    Slice.length, Slice.len, Array.update, output.property, List.slice,
    pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC,
    core.slice.Slice.iter, core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default,
    header, Array.set, Array.setSlice!]
  rw [AfterstateBytes.loop_exact a.next_frontier 0#usize (by decide)]
  have zero : (0#usize).val = 0 := rfl
  simp only [bind_tc_ok,zero,List.drop_zero]
  congr 3
  apply Subtype.ext
  simp only [Aeneas.Std.Array.set, Aeneas.Std.Array.setSlice!]
  rfl

#print axioms encode_exact
end AspisR1.S2K.AfterstateEncoding
