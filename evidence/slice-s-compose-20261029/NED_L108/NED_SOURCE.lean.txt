import NED_LateValidatorCohorts
import NED_AfterEncodingConstants
import NBK_AfterstateResult
set_option autoImplicit false
noncomputable section
namespace NED_AfterEncodingCohort
open Aeneas Aeneas.Std Result NED_LateCarriers NED_LateValidatorCohorts NED_ErrorCarriers
open AspisR1.S2K

def mapOuter {α E F : Type} (f : E → F) : Result (core.result.Result α E) → Result (core.result.Result α F)
 | .ok r => .ok (mapResult f r)
 | .fail e => .fail e
 | .div => .div

/-- Reuse the symbolic bounded-store and frontier-fold theorems; no concrete
688-byte prefix or entire loop is evaluated by definitional equality. -/
theorem result (s : TAfter) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 (toRawAfter s) =
    mapOuter toRawPoolV1PairVerifierTransportErrorV1
      (AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 s) := by
  rw [NBK_AfterstateResult.source]
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1
  rw [NED_LateValidatorCohorts.after]
  cases valid : NBH_Validators.afterResult s with
  | Err e => simp [mapResult,mapOuter,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]
  | Ok u =>
    cases u
    simp only [mapResult,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,mapOuter]
    simp only [toRawAfter,AspisR1.JHf_Carrier.toPoolV1PairVerifiedAfterstateV1,
      AspisS6CurrentAdapterCarrier.fromPoolV1PairVerifiedAfterstateV1,
      NED_DigestCohorts.digest_encode,NED_EncoderLoopCohorts.after_loop,
      NED_AfterEncodingConstants.magic,NED_AfterEncodingConstants.transport_version,
      NED_AfterEncodingConstants.storage_version,NED_AfterEncodingConstants.digest_version]
    unfold AfterstateEncoding.bytes
    generalize Array.repeat 688#usize 0#u8 = output
    change AfterstatePrepare.run s output (fun iter out => do
      let encoded ← AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop iter out
      ok (core.result.Result.Ok encoded)) = _
    rw [AfterstatePrepare.exact]
    rw [AfterstateBytes.loop_exact s.next_frontier 0#usize (by decide)]
    rfl

#print axioms result
end NED_AfterEncodingCohort
