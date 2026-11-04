import Lean
import NGK_NFR_AfterstateForward00
import NFY_Part005

set_option autoImplicit false
noncomputable section
namespace NGK_NFR_AfterstateForward
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open AspisR1.S2K AspisS6NativeAfterstateEncoderReuse
open AspisS6NativeAfterstateDecoderFactored NGK_NFR_AfterstateForwardHelpers

theorem self_ne (a : Slice U8) :
    core.cmp.PartialEq.ne.trait_default
      (AspisR1TerminalDecoder.Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) a a = ok false := by
  simp [core.cmp.PartialEq.ne.trait_default,AspisR1TerminalDecoder.Slice.Insts.CoreCmpPartialEqSlice,
    core.cmp.PartialEq.ne.default,NFY_NBG_Header.slice_equal]
#print axioms self_ne

theorem roundtrip (a : Afterstate)
    (valid : pool_v1.pair_terminal.validate_verified_afterstate a = ok (.Ok ())) :
    pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1 (encoded a) = ok (.Ok a) := by
  have content := native_afterstate_contents a
  have head : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      (encoded a) {«end»:=4#usize} =
      ok pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC.to_slice := by
    simp [core.slice.index.Slice.index,core.slice.index.SliceIndexRangeToUsizeSlice.index,
      core.slice.index.SliceIndexRangeUsizeSlice.index,encoded,Array.to_slice,
      Slice.len,Slice.length,(AfterstateEncoding.bytes a).property,content,
      prefix_bytes,header_bytes,List.slice,
      pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC.property,
      pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC,Array.make]
  have get4 : Slice.index_usize (encoded a) 4#usize = ok 1#u8 := by
    simp [Slice.index_usize,encoded,Array.to_slice,Slice.length,
      (AfterstateEncoding.bytes a).property,content,prefix_bytes,header_bytes,
      pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC.property,
      pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC,
      pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION,Array.make]
  have get5 : Slice.index_usize (encoded a) 5#usize = ok 1#u8 := by
    simp [Slice.index_usize,encoded,Array.to_slice,Slice.length,
      (AfterstateEncoding.bytes a).property,content,prefix_bytes,header_bytes,
      pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC.property,
      pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC,
      pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION,Array.make]
  have get6 : Slice.index_usize (encoded a) 6#usize = ok 1#u8 := by
    simp [Slice.index_usize,encoded,Array.to_slice,Slice.length,
      (AfterstateEncoding.bytes a).property,content,prefix_bytes,header_bytes,
      pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC.property,
      pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC,
      pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,Array.make]
  have get7 : Slice.index_usize (encoded a) 7#usize = ok 1#u8 := by
    simp [Slice.index_usize,encoded,Array.to_slice,Slice.length,
      (AfterstateEncoding.bytes a).property,content,prefix_bytes,header_bytes,
      pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC.property,
      pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC,Array.make]
  have readRoot := range (encoded a) 16#usize 48#usize (DigestBytes.bytes a.next_root)
    (by decide) (by simp [encoded,Array.to_slice,(AfterstateEncoding.bytes a).property]) (root_window a)
  have magicArray : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
      pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC
      {start:=0#usize,«end»:=4#usize} =
      ok pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC.to_slice := by
    simp [core.array.Array.index,core.ops.index.IndexSlice,
      core.slice.index.Slice.index,core.slice.index.SliceIndexRangeUsizeSlice.index,
      Array.to_slice,Slice.len,Slice.length,List.slice,
      pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC.property,
      pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC,Array.make]
  rw [←decode_source]
  unfold AspisS6NativeAfterstateDecoderFactored.decode
  simp only [show Slice.len (encoded a)=688#usize from by
      unfold encoded; have := (AfterstateEncoding.bytes a).property; scalar_tac,
    show pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES=ok 688#usize from by
      simp only [pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
        pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES,bind_tc_ok]
      obtain ⟨z,call,value⟩ := WP.spec_imp_exists
        (Usize.add_spec (x:=8#usize) (y:=680#usize) (by scalar_tac))
      have same : z = 688#usize := by scalar_tac
      exact same ▸ call,
    bind_tc_ok,bne_self_eq_false,Bool.false_eq_true,reduceIte,head,magicArray,self_ne,
    get4,get5,get6,get7,pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION,
    pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION,
    pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,Array.make]
  rw [readRoot,bind_tc_ok,AspisR1.NFY_JFt_ExactArray.source _ _ _ rfl,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [NGK_NFR_DigestForward.roundtrip _ (domain a valid).1,bind_tc_ok]
  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  exact NGK_NFR_AfterstateForward00.result a valid
#print axioms roundtrip
end NGK_NFR_AfterstateForward

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
