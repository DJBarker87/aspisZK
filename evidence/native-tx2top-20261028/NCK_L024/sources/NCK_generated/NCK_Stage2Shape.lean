import NCK_ScanDependency
import NCK_ProofSuffix
import AdapterRwConstants
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCK_Stage2Shape
open Aeneas Aeneas.Std Result
open AdapterRw.Cuts
attribute [local irreducible] _root_.AdapterRw.r1_pool_adapter.owned.validate_asq8
  _root_.AdapterRw.r1_pool_adapter.owned.OwnedAccount.data
/-- Scanner's exact length law is sufficient for the top caller to derive
its fixed proof range on the SAME successful verifier call. -/
theorem fixed_range (ops : _root_.AdapterRw.Ops)
    (program : _root_.AdapterRw.solana_pubkey.Pubkey) (accounts : Slice Account)
    (data : Slice U8) (slot : core.result.Result U64 PE)
    (scanner : NCK_ScanDependency.ScannerLength ops)
    (accepted : _root_.AdapterRw.r1_pool_adapter.owned.stage2_owned ops
      program accounts data slot = ok (.Ok ())) :
    ∃ proofAccount checkpointAccount raw cp,
      ∃ pub : Array U8 1880#usize, ∃ selected,
      Slice.index_usize accounts 0#usize = ok proofAccount ∧
      Slice.index_usize accounts 6#usize = ok checkpointAccount ∧
      _root_.AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops proofAccount = ok (.Ok raw) ∧
      _root_.AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops checkpointAccount = ok (.Ok cp) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        raw {start := 688#usize, «end» := 58295#usize} = ok selected ∧
      ops.op11 (_root_.AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
        (Array.to_slice pub) selected cp () none = ok (.Ok ()) ∧
      raw.val.length = 58295 := by
  unfold _root_.AdapterRw.r1_pool_adapter.owned.stage2_owned at accepted
  simp only [_root_.AdapterRw.core.result.Result.map_err,
    AdapterRw.Constants.constant_aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES] at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals try simp only [error_bind_ne_ok] at *
  all_goals
    have scanLen := NCK_ScanDependency.validated_length ops program accounts data _ _ scanner (by assumption)
    simp only [scanLen, AdapterRw.Scalar.checked_add_eq 688#usize 57607#usize 58295#usize (by scalar_tac)] at *
    aesop (add simp [bne_iff_ne]) (add safe [UScalar.eq_of_val_eq])
#print axioms fixed_range
end AspisR1.NCK_Stage2Shape
end
