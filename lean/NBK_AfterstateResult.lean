import NBH_Audit
import S2K_AfterstateEncoding
set_option autoImplicit false
noncomputable section
namespace NBK_AfterstateResult
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder AspisR1.S2K
open pool_v1.pair_terminal

/-- Full Result on every typed input: no validation or canonicality premise. -/
theorem source (a : PoolV1PairVerifiedAfterstateV1) :
    encode_pool_v1_pair_verified_afterstate_v1 a = ok
      (match NBH_Validators.afterResult a with
      | .Ok _ => .Ok (AfterstateEncoding.bytes a)
      | .Err e => .Err e) := by
  have val := NBH_Validators.afterstate a
  cases r : NBH_Validators.afterResult a with
  | Ok u =>
    cases u
    rw [r] at val
    exact AfterstateEncoding.encode_exact a val
  | Err e =>
    rw [r] at val
    exact AfterstateStatus.rejection a e val

#print axioms source
end NBK_AfterstateResult
