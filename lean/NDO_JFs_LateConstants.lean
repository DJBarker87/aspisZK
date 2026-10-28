import NDO_JFs_LateBytes
import RPz7_S6NativeLateDecoderSplitV1
set_option autoImplicit false
namespace AspisR1.JFs_LateConstants
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_tree_profile

theorem size : POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES=ok 1520#usize := by
  obtain ⟨v,call,equal⟩:=WP.spec_imp_exists AspisS6NativeLateWordCast.late_size
  exact equal ▸ call

theorem length : Slice.len JFu_PublicRange.late=1520#usize := by
  have h : JFu_PublicRange.late.length=1520 := JFu_PublicRange.length 144 1520 (by decide)
  scalar_tac

theorem magic_array : core.array.Array.index
    (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
    POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC {start:=0#usize,«end»:=8#usize}=ok JFs_LateBytes.magic := by
  unfold POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC
  rfl

theorem magic_compare : core.cmp.PartialEq.ne.trait_default
    (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8)
    JFs_LateBytes.magic JFs_LateBytes.magic=ok false := by rfl

#print axioms size
#print axioms length
#print axioms magic_array
#print axioms magic_compare
end AspisR1.JFs_LateConstants
