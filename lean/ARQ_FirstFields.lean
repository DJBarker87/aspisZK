import ARQ_FirstTrace
set_option autoImplicit false
namespace AspisR1.ARQ_FirstFields
open Aeneas Aeneas.Std Result S2W_NativeConsolidation

/-- Source-prefix operands, with no independently chosen accepted child. -/
structure Facts (ops : AdapterRw.Ops) (accounts : S2W_ExtractionBoundary.Accounts)
    (data : Slice U8) (saved : alloc.vec.Vec U8) (f : FirstCut) : Prop where
  proofIndex : Slice.index_usize accounts 0#usize = ok f.proofAccount
  publicIndex : Slice.index_usize accounts 1#usize = ok f.publicAccount
  rawRead : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops f.proofAccount = ok (.Ok f.raw)
  pubRead : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops f.publicAccount = ok (.Ok f.pub)
  decode : ops.op47 f.pub = ok (.Ok f.statement)
  semantic : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
    f.statement = ok f.semantic
  range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    f.raw {start := 688#usize,«end» := 58295#usize} = ok f.proof
  first : AdapterRw.first_decoded ops f.semantic f.pub f.proof f.split = ok (.Ok saved)

#print Facts
end AspisR1.ARQ_FirstFields
