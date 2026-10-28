import AspisR1TerminalDecoder.Funs
set_option autoImplicit false
namespace R1Z.PV_RJDec_PaymentNullifier
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.payment_relation

theorem rejection (s : CommonPublicV1) (capacity : U64)
    (hp : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 s.pool (Array.repeat 32#usize 0#u8) = ok false)
    (hd : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 s.deployment_domain (Array.repeat 32#usize 0#u8) = ok false)
    (hc : pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY = ok capacity)
    (hi : (s.anchor_sequence > capacity) = false)
    (hr : pool_v1.payment_relation.digest_is_canonical s.anchor_root = ok true)
    (bad : pool_v1.payment_relation.digest_is_canonical s.nullifier = ok false) :
    validate_common s = ok (.Err PoolV1PaymentStatementFormatError.NonCanonicalDigest) := by
  unfold validate_common
  simp only [hp, hd, hc, hi, hr, bad, bind_tc_ok, Bool.false_eq_true, ↓reduceIte]

#print axioms rejection
end R1Z.PV_RJDec_PaymentNullifier
