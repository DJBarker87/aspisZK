import AdapterRwCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCK_Stage2Cuts
open Aeneas Aeneas.Std Result
open AdapterRw.r1_pool_adapter
open AdapterRw.r1_pool_adapter.owned
open AdapterRw.Cuts
attribute [local irreducible] validate_asq8 OwnedAccount.data
/-- Forward composition of the top owned body. The U16 and U15 calls are
explicit local cuts, not discharged native bridges or replacement lower units. -/
theorem compose (ops : _root_.AdapterRw.Ops)
    (program : _root_.AdapterRw.solana_pubkey.Pubkey) (accounts : Slice Account)
    (data : Slice U8) (slot : core.result.Result U64 PE)
    (validated : _root_.AdapterRw.r1_pool_adapter.ValidatedAsqa)
    (pa ca : Account) (raw cp selected magic : Slice U8)
    (prefix : Option (Slice U8)) (pub : Array U8 1880#usize) (finish : Usize)
    (count : Slice.len accounts = 7#usize)
    (getPrefix : core.slice.Slice.get (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      data {«end» := 4#usize} = ok prefix)
    (getMagic : core.array.Array.index (core.ops.index.IndexSlice
      ((core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice ops) U8))
      _root_.AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC () = ok magic)
    (sameMagic : core.cmp.PartialEq.ne.trait_default
      ((core.option.Option.Insts.CoreCmpPartialEqOption ops)
        (core.cmp.PartialEqShared (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8)))
      prefix (some magic) = ok false)
    (auth : validate_asq8 ops program accounts data slot = ok (.Ok validated))
    (proofAccount : Slice.index_usize accounts 0#usize = ok pa)
    (checkpointAccount : Slice.index_usize accounts 6#usize = ok ca)
    (proofData : OwnedAccount.data ops pa = ok (.Ok raw))
    (checkpointData : OwnedAccount.data ops ca = ok (.Ok cp))
    (extent : Usize.checked_add 688#usize validated.proof_length = some finish)
    (rawLength : Slice.len raw = finish)
    (encode : ops.op22 validated.statement = ok (.Ok pub))
    (selection : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      raw {start := 688#usize, «end» := finish} = ok selected)
    (tx2 : ops.op11 (_root_.AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
      (Array.to_slice pub) selected cp () none = ok (.Ok ()))
    (emit : ops.op53 validated.statement = ok (.Ok ())) :
    stage2_owned ops program accounts data slot = ok (.Ok ()) := by
  simp only [stage2_owned, count, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    getPrefix, getMagic, sameMagic, bind_tc_ok, auth,
    core.result.Result.Insts.CoreOpsTry.branch, proofAccount, proofData,
    checkpointAccount, checkpointData,
    AdapterRw.Constants.constant_aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
    extent, core.option.Option.ok_or, rawLength, encode,
    _root_.AdapterRw.core.result.Result.map_err,
    _root_.AdapterRw.r1_pool_adapter.owned.stage2_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError,
    selection, _root_.AdapterRw.observer, tx2, emit]

#print axioms compose
end AspisR1.NCK_Stage2Cuts
end
