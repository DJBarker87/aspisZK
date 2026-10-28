import AspisR1TerminalDecoder.Funs
set_option autoImplicit false
namespace R1Z.PV_RJDec_PaymentAsset
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.payment_relation

theorem rejection (s : CommonPublicV1) (capacity : U64)
    (hp : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 s.pool (Array.repeat 32#usize 0#u8) = ok false)
    (hd : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 s.deployment_domain (Array.repeat 32#usize 0#u8) = ok false)
    (hc : pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY = ok capacity)
    (hi : (s.anchor_sequence > capacity) = false)
    (hr : pool_v1.payment_relation.digest_is_canonical s.anchor_root = ok true)
    (hn : pool_v1.payment_relation.digest_is_canonical s.nullifier = ok true)
    (bad : (s.asset_id >= aspis_core.field.P) = true) :
    validate_common s = ok (.Err PoolV1PaymentStatementFormatError.NonCanonicalAssetId) := by
  unfold validate_common
  simp only [hp, hd, hc, hi, hr, hn, bad, bind_tc_ok, Bool.false_eq_true, Bool.true_eq_true, ↓reduceIte]

#print axioms rejection
end R1Z.PV_RJDec_PaymentAsset
