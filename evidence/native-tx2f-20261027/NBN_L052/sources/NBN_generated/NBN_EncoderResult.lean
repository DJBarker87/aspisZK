import NBN_EncoderContents
import NBN_EncoderRejection
set_option autoImplicit false
noncomputable section
namespace NBN_EncoderResult
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder NBN_StatementResult
open pool_v1.pair_forest_terminal

def result (s : Statement) : Result (core.result.Result (Array U8 1880#usize) NBN_StatementResult.Error) := do
  let validated ← NBN_StatementResult.result s
  match validated with
  | .Err e => ok (.Err e)
  | .Ok _ =>
    let pay ← payment s
    match pay with
    | .Err e => ok (.Err (.Payment e))
    | .Ok bytes => ok (.Ok (NBN_EncoderBytes.bytes s bytes))

theorem source (s : Statement) : AspisS6OuterNativeInstalled.encode s = result s := by
  obtain ⟨v,valid⟩ := AspisS6NativeForestTotal.validate_total s
  have modeled : NBN_StatementResult.result s = ok v := by rw [← NBN_StatementResult.source];exact valid
  cases v with
  | Err e =>
    rw [NBN_EncoderRejection.source s e valid]
    simp only [result,modeled,bind_tc_ok]
  | Ok unit =>
    cases unit
    have contents : ∃ pay, payment s = ok (.Ok pay) ∧
        AspisS6OuterNativeInstalled.encode s = ok (.Ok (NBN_EncoderBytes.bytes s pay)) := by
      cases s with
      | PrivateTransfer c p => exact NBN_EncoderContents.private_contents c p valid
      | Withdrawal c p => exact NBN_EncoderContents.withdrawal_contents c p valid
    obtain ⟨pay,payment_run,encoded⟩ := contents
    rw [encoded]
    simp only [result,modeled,bind_tc_ok,payment_run]

#print axioms source
end NBN_EncoderResult
