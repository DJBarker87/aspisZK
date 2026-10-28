import NBN_ValidatorSummary
import NBN_InstalledEncoder
set_option autoImplicit false
noncomputable section
namespace NBN_StatementEncoderSummary
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder NBN_StatementResult NBN_ValidatorSummary
attribute [local instance] Classical.propDecidable
abbrev Raw := NBN_DigestResultDependency.NBN_Dep_DigestEncodeRaw
abbrev BytesResult := Result (core.result.Result (List U8) NBN_StatementResult.Error)

def prefixBytes (s : Statement) (anchor : Array U8 32#usize) : List U8 :=
  let c := AspisS6OuterCarrierBridge.fromPoolV1PairForestTerminalCommonV1 (common s)
  AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC.val ++
    [AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_VERSION,
     NBN_EncoderBytes.tag s,
     AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,c.output_lane] ++
    c.master_account.val ++ c.checkpoint_account.val ++ c.selected_lane_account.val ++
    (core.num.U64.to_le_bytes c.checkpoint_sequence).val ++ anchor.val

theorem prefix_source (s : Statement) :
    prefixBytes s (AspisR1.S2K.DigestBytes.bytes (common s).historical_global_anchor) = NBN_EncoderBytes.commonBytes s := by
  unfold prefixBytes NBN_EncoderBytes.commonBytes AspisS6OuterByteLayout.common_prefix
  rw [AspisS6NativeAfterstateEncoderReuse.native_digest_bytes]
  rfl

def observe (r : Result (core.result.Result (Array U8 1880#usize) NBN_StatementResult.Error)) : BytesResult := do
  let r ← r
  match r with
  | .Err e => ok (.Err e)
  | .Ok a => ok (.Ok a.val)

def run (enc : Encode) (t : Transfer → PaymentResult) (w : Withdrawal → PaymentResult) (s : Statement) : BytesResult := do
  let valid ← NBN_ValidatorSummary.run enc t w s
  match valid with
  | .Err e => ok (.Err e)
  | .Ok _ =>
    let anchor ← enc (common s).historical_global_anchor
    let (status,late) ← NBN_LateSummary.run enc (common s).lane_transition NBN_LateResult.zero
    match status with
    | .Err e => ok (.Err (.LaneTransition e))
    | .Ok _ =>
      let pay ← paymentWith t w s
      match pay with
      | .Err e => ok (.Err (.Payment e))
      | .Ok a => ok (.Ok ((prefixBytes s anchor ++ late.val) ++ a.val))

theorem source (enc : Encode) (t : Transfer → PaymentResult) (w : Withdrawal → PaymentResult)
    (hd : Raw enc) (ht : NBN_Dep_TransferEncode t) (hw : NBN_Dep_WithdrawalEncode w) (s : Statement) :
    run enc t w s = observe (AspisS6OuterNativeInstalled.encode s) := by
  have hc : NBN_DigestResultDependency.NBN_Dep_DigestEncodeCanonical enc := fun d _ => hd d
  obtain ⟨v,hv⟩ := AspisS6NativeForestTotal.validate_total s
  have validation := NBN_ValidatorSummary.source enc t w hc ht hw s
  rw [hv] at validation
  cases v with
  | Err e =>
    rw [NBN_EncoderRejection.source s e hv]
    simp only [run,validation,observe,bind_tc_ok]
  | Ok u =>
    cases u
    obtain ⟨pay,hpay,_⟩ := NBN_StatementDomains.payment_reached s hv
    have late := (NBN_LateInvariant.statement_ready s hv NBN_LateResult.zero (by
      simp only [NBN_LateResult.zero,Slice.length,Array.to_slice,Array.repeat_val,List.length_replicate];rfl)).1
    have contents : AspisS6OuterNativeInstalled.encode s = ok (.Ok (NBN_EncoderBytes.bytes s pay)) := by
      rw [NBN_EncoderResult.source]
      simp only [NBN_EncoderResult.result,← NBN_StatementResult.source,hv,hpay,bind_tc_ok]
    simp only [run,validation,bind_tc_ok]
    rw [hd _,NBN_LateSummary.source enc hc,late]
    simp only [bind_tc_ok]
    rw [payment_source t w ht hw s,hpay]
    simp only [bind_tc_ok]
    rw [prefix_source,contents]
    rfl

#print axioms prefix_source
#print axioms source
end NBN_StatementEncoderSummary
