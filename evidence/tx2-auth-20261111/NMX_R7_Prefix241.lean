import NMX_R7_Std241
set_option autoImplicit false
noncomputable section
namespace NMX_R7_Prefix241
open Aeneas Aeneas.Std Result AdapterRw

def magicCheck (env : RSL.Env) (data : Slice U8) : Result Bool := do
 let o ← core.slice.Slice.get (core.slice.index.SliceIndexRangeToUsizeSlice U8) data {«end» := 4#usize}
 let a ← (pure aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC : Result (Array U8 4#usize))
 let s ← core.array.Array.index (core.ops.index.IndexSlice
  (core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice (NMX_R7_Std241.ops env) U8)) a ()
 core.cmp.PartialEq.ne.trait_default
  (core.option.Option.Insts.CoreCmpPartialEqOption (NMX_R7_Std241.ops env)
   (core.cmp.PartialEqShared (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8))) o (some s)

/-- Exact source magic array, before comparing native slices. -/
theorem magic :
 NMS_R2N_RSLScalars.bytes
  aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC.to_slice = RSL.REQUEST_MAGIC := by
 unfold aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC
 unfold NMS_R2N_RSLScalars.bytes RSL.REQUEST_MAGIC
 rfl

#print axioms magic
end NMX_R7_Prefix241
end
