import JGx_SdkAfterValidationEq
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_MagicGate
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

def value (ops : Ops) (data : Slice U8) : Result Bool := do
  let o ← core.slice.Slice.get (core.slice.index.SliceIndexRangeToUsizeSlice U8) data {«end»:=4#usize}
  let s ← core.array.Array.index (core.ops.index.IndexSlice
    ((core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice ops) U8))
    aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC ()
  core.cmp.PartialEq.ne.trait_default ((core.option.Option.Insts.CoreCmpPartialEqOption ops)
    (core.cmp.PartialEqShared (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8))) o (some s)

theorem source (ops : Ops) (data : Slice U8) (selected : Option (Slice U8)) (magic : Slice U8)
    (read : core.slice.Slice.get (core.slice.index.SliceIndexRangeToUsizeSlice U8) data {«end»:=4#usize}=ok selected)
    (array : core.array.Array.index (core.ops.index.IndexSlice
      ((core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice ops) U8))
      aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC ()=ok magic)
    (compare : core.cmp.PartialEq.ne.trait_default ((core.option.Option.Insts.CoreCmpPartialEqOption ops)
      (core.cmp.PartialEqShared (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8))) selected (some magic)=ok false) :
    value ops data=ok false := by
  unfold value
  rw [read,bind_tc_ok,array,bind_tc_ok,compare]
#print axioms source
end AspisR1.JGx_MagicGate
end
