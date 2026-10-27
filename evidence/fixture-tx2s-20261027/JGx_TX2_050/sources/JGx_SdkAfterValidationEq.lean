import JGx_SdkContinuation
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_SdkAfterValidationEq
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

theorem source (ops : Ops) (program : solana_pubkey.Pubkey)
    (accounts : S2W_ExtractionBoundary.Accounts) (data : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot)
    (validated : r1_pool_adapter.ValidatedAsqa)
    (count : Slice.len accounts=7#usize)
    (magic : (do
      let o ← core.slice.Slice.get (core.slice.index.SliceIndexRangeToUsizeSlice U8) data {«end»:=4#usize}
      let s ← core.array.Array.index (core.ops.index.IndexSlice
        ((core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice ops) U8))
        aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC ()
      core.cmp.PartialEq.ne.trait_default ((core.option.Option.Insts.CoreCmpPartialEqOption ops)
        (core.cmp.PartialEqShared (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8))) o (some s))=ok false)
    (validation : r1_pool_adapter.owned.validate_asq8 ops program accounts data slot=ok (.Ok validated)) :
    r1_pool_adapter.owned.stage2_owned ops program accounts data slot=
      JGx_SdkContinuation.afterValidation ops accounts validated := by
  unfold r1_pool_adapter.owned.stage2_owned
  rw [count]
  simp only [show (7#usize !=7#usize)=false from by decide,Bool.false_eq_true,ite_false]
  obtain ⟨o,read,rest⟩ := AdapterRw.Cuts.bind_success _ _ _ magic
  obtain ⟨s,index,neq⟩ := AdapterRw.Cuts.bind_success _ _ _ rest
  rw [read,bind_tc_ok,index,bind_tc_ok,neq,bind_tc_ok]
  simp only [Bool.false_eq_true,ite_false]
  rw [validation,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JGx_SdkAfterValidationEq
end
