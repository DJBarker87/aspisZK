import S2X_RuntimeRetention

set_option autoImplicit false
namespace AspisR1.S2X
open Aeneas Aeneas.Std Result
open AdapterRw.Cuts

attribute [local irreducible] AdapterRw.r1_pool_adapter.owned.validate_asq8
  AdapterRw.r1_pool_adapter.owned.OwnedAccount.data

/-- The actual accepted owned TX2 selects from byte 688 through the end of
its raw proof account and passes that SAME selection to the second child. -/
theorem second_fixed_range (ops : AdapterRw.Ops)
    (program : AdapterRw.solana_pubkey.Pubkey) (accounts : Slice Account)
    (data : Slice U8) (slot : core.result.Result U64 PE)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage2_owned ops program accounts data slot =
      ok (.Ok ())) :
    ∃ validated proofAccount checkpointAccount raw checkpointInput publicArray selected finish,
      AdapterRw.r1_pool_adapter.owned.validate_asq8 ops program accounts data slot = ok (.Ok validated) ∧
      Slice.index_usize accounts 0#usize = ok proofAccount ∧
      Slice.index_usize accounts 6#usize = ok checkpointAccount ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops proofAccount = ok (.Ok raw) ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops checkpointAccount = ok (.Ok checkpointInput) ∧
      ops.op22 validated.statement = ok (.Ok publicArray) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        raw {start := 688#usize, «end» := finish} = ok selected ∧
      ops.op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
        (Array.to_slice publicArray) selected checkpointInput () none = ok (.Ok ()) ∧
      raw.val.length = finish.val := by
  unfold AdapterRw.r1_pool_adapter.owned.stage2_owned at accepted
  simp only [AdapterRw.core.result.Result.map_err,
    AdapterRw.Constants.constant_aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES] at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals try simp only [error_bind_ne_ok] at *
  all_goals aesop (add simp [bne_iff_ne])

/-- Checked range success includes ordering; no scanner honesty assumption is
needed for this property. No concrete proof contents are reduced. -/
theorem successful_range_ordered (raw selected : Slice U8) (start finish : Usize)
    (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      raw {start := start, «end» := finish} = ok selected) : start.val ≤ finish.val := by
  by_contra unordered
  simp [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index, unordered] at range

#print axioms second_fixed_range
#print axioms successful_range_ordered
end AspisR1.S2X
