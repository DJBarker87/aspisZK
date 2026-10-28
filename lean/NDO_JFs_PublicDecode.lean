import NDO_JFs_PublicCommon
import NDO_JFs_PublicValidation
import NDO_JFs_PublicPayment
set_option autoImplicit false
namespace AspisR1.JFs_PublicDecode
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_forest_terminal

theorem source : decode_pool_v1_pair_forest_terminal_statement_v1 JFx_NativeBytes.publicInput=
    ok (.Ok JFs_PublicValue.value) := by
  have size : Slice.len JFx_NativeBytes.publicInput=1880#usize := by
    have h:=JFu_PublicHeader.length
    scalar_tac
  have check : (1880#usize !=1880#usize)=false := by decide
  have one : (1#u8 !=1#u8)=false := by decide
  have magic_array : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
      POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC {start:=0#usize,«end»:=4#usize}=
      ok JFs_PublicHeader.magic := by
    unfold POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC
    rfl
  have magic_compare : core.cmp.PartialEq.ne.trait_default
      (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8)
      JFs_PublicHeader.magic JFs_PublicHeader.magic=ok false := by rfl
  unfold decode_pool_v1_pair_forest_terminal_statement_v1
  simp only [size,JFs_PublicSize.bytes,bind_tc_ok,check,Bool.false_eq_true,↓reduceIte,
    JFs_PublicHeader.firstn,magic_array,magic_compare,
    JFs_PublicHeader.index 4#usize (by decide) 1#u8 (by rfl),
    JFs_PublicHeader.index 5#usize (by decide) 1#u8 (by rfl),
    JFs_PublicHeader.index 6#usize (by decide) 1#u8 (by rfl),
    POOL_V1_PAIR_FOREST_TERMINAL_VERSION,pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,one]
  have kind : transition_kind 1#u8=ok (.Ok pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer) := by
    unfold transition_kind
    rfl
  simp only [kind,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,JFs_PublicCommon.source,
    JFs_PublicSize.payment_offset,JFs_PublicPayment.suffix,JFs_PublicPayment.source,JFs_PublicValidation.source]

#print axioms source
end AspisR1.JFs_PublicDecode
