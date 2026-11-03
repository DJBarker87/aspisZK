import NEQ_DecodeScalar
import NEQ_UnwrapDomains
import NBP_CommonDecode
import NEM_ValidatorComposed
set_option autoImplicit false
noncomputable section
namespace NEQ_CommonDecode
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev Common := pool_v1.payment_relation.CommonPublicV1
abbrev Err := pool_v1.payment_relation.PoolV1PaymentStatementFormatError
abbrev DigestCall := Array U8 32#usize → Result (core.result.Result (Array U32 8#usize) atomic_statement.AtomicStatementError)
abbrev Validate := Common → Result (core.result.Result Unit Err)
attribute [local instance] Classical.propDecidable

def run (decode : DigestCall) (validate : Validate) (b : Array U8 216#usize) :
    Result (core.result.Result Common Err) := do
  if NBP_CommonDecode.asset b >= 2147483647#u32 then ok (.Err .NonCanonicalAssetId)
  else
    let anchor ← decode (NBP_Read.chunk b 80 (by decide))
    match anchor with
    | .Err _ => ok (.Err .NonCanonicalDigest)
    | .Ok a =>
      let nullifier ← decode (NBP_Read.chunk b 112 (by decide))
      match nullifier with
      | .Err _ => ok (.Err .NonCanonicalDigest)
      | .Ok n =>
        let c := NBP_CommonDecode.common b a n
        let valid ← validate c
        match valid with
        | .Err e => ok (.Err e)
        | .Ok _ => ok (.Ok c)

theorem substitution (b : Array U8 216#usize) :
    run atomic_statement.decode_digest_canonical pool_v1.payment_relation.validate_common b =
      ok (NBP_CommonDecode.decoded b) := by
  unfold run NBP_CommonDecode.decoded
  simp only [NBP_DigestDecode.result,NBG_PaymentChecks.common_result,bind_tc_ok]
  by_cases invalid : NBP_CommonDecode.asset b >= 2147483647#u32
  · simp only [if_pos invalid]
  · simp only [if_neg invalid]
    cases a : NBP_DigestDecode.decoded (NBP_Read.chunk b 80 (by decide)) with
    | Err e => rfl
    | Ok anchor =>
      dsimp only
      cases n : NBP_DigestDecode.decoded (NBP_Read.chunk b 112 (by decide)) with
      | Err e => rfl
      | Ok nullifier =>
        dsimp only
        cases NBG_PaymentChecks.common (NBP_CommonDecode.common b anchor nullifier) <;> rfl

theorem result_state_effects {State : Type} (b : Array U8 216#usize) (state : State) :
    (run atomic_statement.decode_digest_canonical pool_v1.payment_relation.validate_common b,state,([] : List Unit)) =
      (pool_v1.payment_relation.decode_common b,state,[]) := by
  rw [substitution,NBP_CommonDecode.result]

#print axioms substitution
#print axioms result_state_effects
end NEQ_CommonDecode
